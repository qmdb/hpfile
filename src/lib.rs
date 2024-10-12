//! # Head-prunable file
//!
//! Normal files can not be pruned\(truncated\) from the beginning to some middle position.
//! A `HPFile` use a sequence of small files to simulate one big virtual file. Thus, pruning
//! from the beginning is to delete the first several small files.
//!
//! A `HPFile` can only be read and appended. Any byteslice which was written to it is
//! immutable.
//!
//! To append a new byteslice into a `HPFile`, use the `append` function, which will return
//! the start position of this byteslice. Later, just pass this start position to `read_at`
//! for reading this byteslice out. The position passed to `read_at` must be the beginning of a
//! byteslice that was written before, instead of its middle. Do NOT try to read the later
//! half (from a middle point to the end) of a byteslice.
//!
//! A `HPFile` can also be truncated: discarding the content from a given position to the
//! end of the file. During trucation, several small files may be removed and one small file
//! may get truncated.
//!
//! A `HPFile` can serve many reader threads. If a reader thread just read random positions,
//! plain `read_at` is enough. If a reader tends to read many adjacent byteslices in sequence, it
//! can take advantage of spatial locality by using `read_at_with_pre_reader`, which uses a
//! `PreReader` to read large chunks of data from file and cache them. Each reader thread can have
//! its own `PreReader`. A `PreReader` cannot be shared by different `HPFile`s.
//!
//! A `HPFile` can serve only one writer thread. The writer thread must own a write buffer that
//! collects small pieces of written data into one big single write to the underlying OS file,
//! to avoid the cost of many syscalls writing the OS file. This write buffer must be provided
//! when calling `append` and `flush`. It is owned by the writer thead, instead of `HPFile`,
//! because we want `HPFile` to be shared between many reader threads.
//!
//! `TempDir` is used in unit test. It is a temporary directory created during a unit test
//! function, and will be deleted when this test function exits.

use anyhow::{anyhow, Result};
use dashmap::DashMap;
use std::{
    fs::{self, create_dir, metadata, read_dir, remove_dir_all, File},
    io::{self, Seek, SeekFrom, Write},
    os::unix::fs::FileExt,
    path::Path,
    sync::atomic::{AtomicI64, Ordering},
};

const PRE_READ_BUF_SIZE: usize = 512 * 1024;

/// Head-prunable file
#[derive(Debug)]
pub struct HPFile {
    dir_name: String, // where we store the small files
    segment_size: i64, // the size of each small file
    buffer_size: i64, // the write buffer's size
    file_map: DashMap<i64, File>,
    largest_id: AtomicI64,
    latest_file_size: AtomicI64,
}

impl HPFile {
/// Create a `HPFile` with a directory. If this directory was used by an old HPFile, the old
/// HPFile must have the same `segment_size` as this one.
///
/// # Parameters
///
/// - `wr_buf_size`: The write buffer used in `append` will not exceed this size
/// - `segment_size`: The target size of the small files
/// - `dir_name`: The name of the directory used to store the small files
///
/// # Returns
///
/// A `Result` which is:
///
/// - `Ok`: A successfully initialized `HPFile`
/// - `Err`: Encounted some file system error.
///
    pub fn new(wr_buf_size: i64, segment_size: i64, dir_name: String) -> Result<HPFile> {
        if segment_size % wr_buf_size != 0 {
            return Err(anyhow!(
                "Invalid segmentSize:{} writeBufferSize:{}",
                segment_size,
                wr_buf_size
            ));
        }

        let (id_list, largest_id) = Self::get_file_ids(&dir_name, segment_size)?;
        let (file_map, latest_file_size) =
            Self::load_file_map(&dir_name, segment_size, id_list, largest_id)?;

        Ok(HPFile {
            dir_name: dir_name.clone(),
            segment_size: segment_size,
            buffer_size: wr_buf_size,
            file_map,
            largest_id: AtomicI64::new(largest_id),
            latest_file_size: AtomicI64::new(latest_file_size),
        })
    }

/// Create an empty `HPFile` that has no function and can only be used as placeholder.
    pub fn empty() -> HPFile {
        HPFile {
            dir_name: "".to_owned(),
            segment_size: 0,
            buffer_size: 0,
            file_map: DashMap::with_capacity(0),
            largest_id: AtomicI64::new(0),
            latest_file_size: AtomicI64::new(0),
        }
    }

/// Returns whether this `HPFile` is empty.
    pub fn is_empty(&self) -> bool {
        self.segment_size == 0
    }

    fn get_file_ids(dir_name: &str, segment_size: i64) -> Result<(Vec<i64>, i64)> {
        let mut largest_id = 0;
        let mut id_list = Vec::new();

        for entry in fs::read_dir(dir_name)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                continue;
            }

            let file_name = entry.file_name().to_string_lossy().to_string();
            let id = Self::parse_filename(segment_size, &file_name)?;
            largest_id = largest_id.max(id);
            id_list.push(id);
        }

        Ok((id_list, largest_id))
    }

    fn parse_filename(segment_size: i64, file_name: &str) -> Result<i64> {
        let parts: Vec<_> = file_name.split("-").collect();
        if parts.len() != 2 {
            return Err(anyhow!(
                "{} does not match the pattern 'FileId-segmentSize'",
                file_name
            ));
        }

        let id: i64 = parts[0].parse()?;
        let size: i64 = parts[1].parse()?;

        if segment_size != size {
            return Err(anyhow!("Invalid Size! {}!={}", size, segment_size));
        }

        Ok(id)
    }

    fn load_file_map(
        dir_name: &str,
        segment_size: i64,
        id_list: Vec<i64>,
        largest_id: i64,
    ) -> Result<(DashMap<i64, File>, i64)> {
        let file_map = DashMap::new();
        let mut latest_file_size = 0;

        for &id in &id_list {
            let file_name = format!("{}/{}-{}", dir_name, id, segment_size);
            let file = File::options().read(true).write(true).open(file_name)?;
            if id == largest_id {
                latest_file_size = file.metadata()?.len() as i64;
            }
            file_map.insert(id, file);
        }

        if id_list.is_empty() {
            let file_name = format!("{}/{}-{}", &dir_name, 0, segment_size);
            let file = File::create_new(file_name)?;
            file_map.insert(0, file);
        }

        Ok((file_map, latest_file_size))
    }

/// Returns the size of the virtual large file
    pub fn size(&self) -> i64 {
        self.largest_id.load(Ordering::SeqCst) * self.segment_size
            + self.latest_file_size.load(Ordering::SeqCst)
    }

/// Truncate the file to make it smaller
///
/// # Parameters
///
/// - `size`: the size of the virtual large file after truncation. It must be smaller 
///           than the original size.
///
/// # Returns
///
/// A `Result` which is:
///
/// - `Ok`: It's truncated successfully
/// - `Err`: Encounted some file system error.
///
    pub fn truncate(&self, size: i64) -> io::Result<()> {
        if self.is_empty() {
            return Ok(());
        }

        let mut largest_id = self.largest_id.load(Ordering::SeqCst);

        while size < largest_id * self.segment_size {
            self.file_map.remove(&largest_id);
            let file_name = format!("{}/{}-{}", self.dir_name, largest_id, self.segment_size);
            fs::remove_file(file_name)?;
            self.largest_id.fetch_sub(1, Ordering::SeqCst);
            largest_id -= 1;
        }

        let remaining_size = size - largest_id * self.segment_size;
        let file_name = format!("{}/{}-{}", self.dir_name, largest_id, self.segment_size);
        let mut f = File::options().read(true).write(true).open(file_name)?;
        f.set_len(remaining_size as u64)?;
        f.seek(SeekFrom::End(0))?;

        self.file_map.insert(largest_id, f);
        self.latest_file_size
            .store(remaining_size, Ordering::SeqCst);

        Ok(())
    }

/// Flush the remained data in `buffer` into file system
///
/// # Parameters
///
/// - `buffer`: the write buffer, which is used by the client to call `append`.
///
/// # Returns
///
/// A `Result` which is:
///
/// - `Ok`: It's flushed successfully
/// - `Err`: Encounted some file system error.
///
    pub fn flush(&self, buffer: &mut Vec<u8>) -> io::Result<()> {
        if self.is_empty() {
            return Ok(());
        }
        let largest_id = self.largest_id.load(Ordering::SeqCst);
        // todo: is it the largest id safe?
        let mut opt = self.file_map.get_mut(&largest_id);
        let mut f = opt.as_mut().unwrap().value();
        if buffer.len() != 0 {
            f.seek(SeekFrom::End(0)).unwrap();
            f.write(&buffer).unwrap();
            buffer.clear();
        }

        f.sync_all()
    }

/// Close the opened small files
    pub fn close(&self) {
        self.file_map.clear();
    }

/// Read data from file at `offset` to fill `buf`
///
/// # Parameters
///
/// - `offset`: the start position of a byteslice that was written before
///
/// # Returns
///
/// A `Result` which is:
///
/// - `Ok`: Number of bytes that was filled into `buf`
/// - `Err`: Encounted some file system error.
///
    pub fn read_at(&self, buf: &mut [u8], offset: i64) -> io::Result<usize> {
        let file_id = offset / self.segment_size;
        let pos = offset % self.segment_size;
        let opt = self.file_map.get(&file_id);
        let f = opt.as_ref().unwrap().value();
        f.read_at(buf, pos as u64)
    }

/// Read at most `num_bytes` from file at `offset` to fill `buf`
///
/// # Parameters
///
/// - `buf`: a vector to be filled
/// - `num_bytes`: the wanted number of bytes to be read
/// - `offset`: the start position of a byteslice that was written before
/// - `pre_reader`: a PreReader used to take advantage of spatial locality
///
/// # Returns
///
/// A `Result` which is:
///
/// - `Ok`: Number of bytes that was filled into `buf`
/// - `Err`: Encounted some file system error.
///
    pub fn read_at_with_pre_reader(
        &self,
        buf: &mut Vec<u8>,
        num_bytes: usize,
        offset: i64,
        pre_reader: &mut PreReader,
    ) -> io::Result<usize> {
        if buf.len() < num_bytes {
            buf.resize(num_bytes, 0);
        }

        let file_id = offset / self.segment_size;
        let pos = offset % self.segment_size;

        if pre_reader.try_read(file_id, pos, &mut buf[..num_bytes]) {
            return Ok(num_bytes);
        }

        let opt = self.file_map.get(&file_id);
        let f = opt.as_ref().unwrap().value();

        if num_bytes >= PRE_READ_BUF_SIZE || pos + num_bytes as i64 > self.segment_size {
            return f.read_at(&mut buf[..num_bytes], pos as u64);
        }

        pre_reader.fill_slice(file_id, pos, |slice| {
            f.read_at(slice, pos as u64).map(|n| n as i64)
        })?;

        if !pre_reader.try_read(file_id, pos, &mut buf[..num_bytes]) {
            panic!(
                "Internal error: cannot read data just fetched in {} fileID {}",
                self.dir_name, file_id
            );
        }

        Ok(num_bytes)
    }

/// Append a byteslice to the file. This byteslice may be temporarily held in
/// `buffer` before flushing.
///
/// # Parameters
///
/// - `bz`: the byteslice to append. It cannot be longer than `wr_buf_size` specified
///         in `HPFile::new`.
/// - `buffer`: the write buffer. It will never be larger than `wr_buf_size`.
///
/// # Returns
///
/// A `Result` which is:
///
/// - `Ok`: the start position where this byteslice locates in the file
/// - `Err`: Encounted some file system error.
///
    pub fn append(&self, bz: &[u8], buffer: &mut Vec<u8>) -> io::Result<i64> {
        if self.is_empty() {
            return Ok(0);
        }

        if bz.len() as i64 > self.buffer_size {
            panic!("bz is too large");
        }

        let mut largest_id = self.largest_id.load(Ordering::SeqCst);
        let start_pos = self.size();
        let old_size = self
            .latest_file_size
            .fetch_add(bz.len() as i64, Ordering::SeqCst);
        let mut split_pos = 0;
        let extra_bytes = (buffer.len() + bz.len()) as i64 - self.buffer_size;
        if extra_bytes > 0 {
            // flush buffer_size bytes to disk
            split_pos = bz.len() - extra_bytes as usize;
            buffer.extend_from_slice(&bz[0..split_pos]);
            let mut opt = self.file_map.get_mut(&largest_id);
            let mut f = opt.as_mut().unwrap().value();
            if let Err(_) = f.write(buffer.as_slice()) {
                panic!("Fail to write file");
            }
            buffer.clear();
        }
        buffer.extend_from_slice(&bz[split_pos..]); //put remained bytes into buffer
        let overflow_byte_count = old_size + bz.len() as i64 - self.segment_size;
        if overflow_byte_count >= 0 {
            self.flush(buffer)?;
            self.largest_id.fetch_add(1, Ordering::SeqCst);
            largest_id += 1;
            let file_name = format!("{}/{}-{}", self.dir_name, largest_id, self.segment_size);
            let f = match File::create_new(&file_name) {
                Ok(file) => file,
                Err(_) => File::options()
                    .read(true)
                    .write(true)
                    .open(&file_name)
                    .unwrap(),
            };
            if overflow_byte_count != 0 {
                // write zero bytes as placeholder
                buffer.resize(0, 0);
                buffer.resize(overflow_byte_count as usize, 0);
            }
            self.file_map.insert(largest_id, f);
            self.latest_file_size
                .store(overflow_byte_count, Ordering::SeqCst);
        }

        Ok(start_pos)
    }

/// Prune from the beginning to `offset`. This part of the file cannot be read hereafter.
    pub fn prune_head(&self, offset: i64) -> io::Result<()> {
        if self.is_empty() {
            return Ok(());
        }

        let file_id = offset / self.segment_size;
        let ids_to_remove: Vec<i64> = self
            .file_map
            .iter()
            .filter(|entry| *entry.key() < file_id)
            .map(|entry| *entry.key())
            .collect();

        for id in ids_to_remove {
            self.file_map.remove(&id);
            let file_name = format!("{}/{}-{}", self.dir_name, id, self.segment_size);
            fs::remove_file(file_name)?;
        }

        Ok(())
    }
}

/// Pre-read a large chunk of data from file for caching
#[derive(Debug)]
pub struct PreReader {
    buffer: Box<[u8]>, // size is PRE_READ_BUF_SIZE
    file_id: i64,
    start: i64,
    end: i64,
}

impl PreReader {
    /// Create a `PreReader` to be used in `HPFile::read_at_with_pre_reader`
    pub fn new() -> Self {
        Self {
            buffer: vec![0; PRE_READ_BUF_SIZE].into_boxed_slice(),
            file_id: 0,
            start: 0,
            end: 0,
        }
    }

    fn fill_slice<F>(&mut self, file_id: i64, start: i64, access: F) -> io::Result<()>
    where
        F: FnOnce(&mut [u8]) -> io::Result<i64>,
    {
        self.file_id = file_id;
        self.start = start;
        let n = access(&mut self.buffer[..])?;
        self.end = start + n;
        Ok(())
    }

    fn try_read(&self, file_id: i64, start: i64, bz: &mut [u8]) -> bool {
        if file_id == self.file_id && self.start <= start && start + bz.len() as i64 <= self.end {
            let offset = (start - self.start) as usize;
            bz.copy_from_slice(&self.buffer[offset..offset + bz.len()]);
            true
        } else {
            false
        }
    }
}

/// Temporary directory for unit test
pub struct TempDir {
    dir: String,
}

impl TempDir {
    /// Create a new TempDir
    pub fn new(dir: &str) -> Self {
        remove_dir_all(dir).unwrap_or(()); // ignore error
        create_dir(dir).unwrap_or(()); // ignore error
        Self {
            dir: dir.to_string(),
        }
    }

    /// Return the path of this temporary directory
    pub fn to_string(&self) -> String {
        self.dir.clone()
    }

    /// Return the names of the files in this directory
    pub fn list(&self) -> Vec<String> {
        TempDir::list_dir(&self.dir)
    }

    /// Return the names of the files in `dir`
    pub fn list_dir(dir: &str) -> Vec<String> {
        let mut result = vec![];
        let paths = std::fs::read_dir(Path::new(dir)).unwrap();
        for path in paths {
            result.push(path.unwrap().path().to_str().unwrap().to_string());
        }
        result.sort();
        result
    }

    /// Create a new file in this directory
    pub fn create_file(&self, name: &str) {
        let file_path = Path::new(&self.dir).join(Path::new(name));
        File::create_new(file_path).unwrap();
    }

    /// Return the names of the files in `path` and its subdirectories recursively
    pub fn list_all(path: &Path) -> Vec<String> {
        let mut vec = Vec::new();
        TempDir::_list_files(&mut vec, path);
        vec.sort();
        vec
    }

    fn _list_files(vec: &mut Vec<String>, path: &Path) {
        if metadata(&path).unwrap().is_dir() {
            let paths = read_dir(&path).unwrap();
            for path_result in paths {
                let full_path = path_result.unwrap().path();
                if metadata(&full_path).unwrap().is_dir() {
                    TempDir::_list_files(vec, &full_path);
                } else {
                    vec.push(String::from(full_path.to_str().unwrap()));
                }
            }
        }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        remove_dir_all(&self.dir).unwrap_or(()); // ignore error
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Read;

    #[test]
    fn test_pre_reader() {
        let temp_dir = TempDir::new("pre_reader_test");
        let file_path = format!("{}/test.txt", temp_dir.to_string());
        let mut f = File::create(&file_path).unwrap();
        f.write_all(&[0u8; 8]).unwrap();
        f.write_all(&[1u8; 8]).unwrap();
        f.sync_all().unwrap(); // Ensure file is fully written before reading

        let mut r = PreReader::new();
        let file_id = 1;
        let pos = 8;
        r.fill_slice(file_id, pos, |slice| {
            let mut file = File::open(&file_path)?;
            file.seek(SeekFrom::Start(pos as u64))?;
            file.read(slice).map(|n| n as i64)
        })
        .unwrap();

        assert_eq!(r.start, 8);
        assert_eq!(r.end, 16);
        assert_eq!(r.buffer[0], 1);
        assert_eq!(r.buffer[7], 1);
        assert_eq!(r.buffer[8], 0);

        let mut buf = [0; 4];
        let res = r.try_read(file_id, 8, &mut buf);
        assert!(res);
        assert_eq!(buf, [1, 1, 1, 1]);
    }

    #[test]
    fn test_hp_file_new() {
        let dir = TempDir::new("hp_file_test");
        let buffer_size = 64;
        let segment_size = 128;
        let hp = HPFile::new(buffer_size, segment_size, dir.to_string()).unwrap();
        assert_eq!(hp.buffer_size, buffer_size);
        assert_eq!(hp.segment_size, segment_size);
        assert_eq!(hp.file_map.len(), 1);
        // assert_eq!(
        //     hp.file_map
        //         .write()
        //         .unwrap()
        //         .get(&0)
        //         .unwrap()
        //         .metadata()
        //         .unwrap()
        //         .len(),
        //     0
        // );

        let slice0 = [1; 44];
        let mut buffer = vec![];
        let mut pos = hp.append(&slice0.to_vec(), &mut buffer).unwrap();
        assert_eq!(0, pos);
        assert_eq!(44, hp.size());

        let slice1a = [2; 16];
        let slice1b = [3; 10];
        let mut slice1 = vec![];
        slice1.extend_from_slice(&slice1a);
        slice1.extend_from_slice(&slice1b);
        pos = hp.append(slice1.as_ref(), &mut buffer).unwrap();
        assert_eq!(44, pos);
        assert_eq!(70, hp.size());

        let slice2a = [4; 25];
        let slice2b = [5; 25];
        let mut slice2 = vec![];
        slice2.extend_from_slice(&slice2a);
        slice2.extend_from_slice(&slice2b);
        pos = hp.append(slice2.as_ref(), &mut buffer).unwrap();
        assert_eq!(70, pos);
        assert_eq!(120, hp.size());

        let mut check0 = [0; 44];
        hp.read_at(&mut check0, 0).unwrap();
        assert_eq!(slice0.to_vec(), check0.to_vec());

        hp.flush(&mut buffer).unwrap();

        let mut check1 = [0; 26];
        hp.read_at(&mut check1, 44).unwrap();
        assert_eq!(slice1, check1);

        let mut check2 = [0; 50];
        hp.read_at(&mut check2, 70).unwrap();
        assert_eq!(slice2, check2);

        let slice3 = [0; 16];
        pos = hp.append(slice3.to_vec().as_ref(), &mut buffer).unwrap();
        assert_eq!(120, pos);
        assert_eq!(136, hp.size());

        hp.flush(&mut buffer).unwrap();
        hp.close();

        let hp_new = HPFile::new(64, 128, dir.to_string()).unwrap();

        hp_new.read_at(&mut check0, 0).unwrap();
        assert_eq!(slice0.to_vec(), check0.to_vec());

        hp_new.read_at(&mut check1, 44).unwrap();
        assert_eq!(slice1, check1);

        hp_new.read_at(&mut check2, 70).unwrap();
        assert_eq!(slice2, check2);

        let mut check3 = [0; 16];
        hp_new.read_at(&mut check3, 120).unwrap();
        assert_eq!(slice3.to_vec(), check3.to_vec());

        hp_new.prune_head(64).unwrap();
        hp_new.truncate(120).unwrap();
        assert_eq!(hp_new.size(), 120);
        let mut slice4 = vec![];
        hp_new.read_at(&mut slice4, 120).unwrap();
        assert_eq!(slice4.len(), 0);
    }

    #[test]
    #[should_panic(expected = "Invalid segmentSize:127 writeBufferSize:64")]
    fn test_new_file_invalid_buffer_or_segment_size() {
        let dir = TempDir::new("test_new_file_invalid_buffer_or_segment_size");
        let buffer_size = 64;
        let segment_size = 127;
        let _ = HPFile::new(buffer_size, segment_size, dir.to_string()).unwrap();
    }

    #[test]
    fn test_new_file_invalid_filename() {
        let dir = TempDir::new("test_new_file_invalid_filename");
        dir.create_file("hello.txt"); // invalid filename
        assert_eq!(
            "hello.txt does not match the pattern 'FileId-segmentSize'",
            HPFile::new(64, 128, dir.to_string())
                .unwrap_err()
                .to_string()
        )
    }

    #[test]
    fn test_new_file_invalid_filename2() {
        let dir = TempDir::new("test_new_file_invalid_filename2");
        dir.create_file("hello-hello.txt"); // invalid filename
        assert_eq!(
            "invalid digit found in string",
            HPFile::new(64, 128, dir.to_string())
                .unwrap_err()
                .to_string()
        )
    }

    #[test]
    fn test_new_file_invalid_filename3() {
        let dir = TempDir::new("test_new_file_invalid_filename3");
        dir.create_file("1-hello.txt"); // invalid xx-xx filename
        assert_eq!(
            "invalid digit found in string",
            HPFile::new(64, 128, dir.to_string())
                .unwrap_err()
                .to_string()
        )
    }

    #[test]
    fn test_new_file_failed_invalid_size() {
        let dir = TempDir::new("test_new_file_failed_invalid_size");
        dir.create_file("1-1"); // invalid file size not equal block size
        assert_eq!(
            "Invalid Size! 1!=128",
            HPFile::new(64, 128, dir.to_string())
                .unwrap_err()
                .to_string()
        )
    }

    #[test]
    fn test_read_at_with_pre_reader() {
        let dir = TempDir::new("hpfile_test_dir_4");
        let buffer_size = 64;
        let segment_size = 128;
        let hp_file = HPFile::new(buffer_size, segment_size, dir.to_string()).unwrap();
        let mut pre_reader = PreReader::new();
        pre_reader.end = 5;
        for i in 0..5 {
            pre_reader.buffer[i as usize] = i;
        }
        let mut buf = Vec::from([0; 10]);
        hp_file
            .read_at_with_pre_reader(&mut buf, 3, 0, &mut pre_reader)
            .unwrap();
        assert_eq!(buf[0..3], [0, 1, 2]);
        let mut buf = Vec::from([0; 129]);
        fs::write("./hpfile_test_dir_4/0-128", [1, 2, 3, 4]).unwrap();
        hp_file
            .read_at_with_pre_reader(&mut buf, 129, 0, &mut pre_reader)
            .unwrap();
        assert_eq!(buf[0..4], [1, 2, 3, 4]);

        fs::write("./hpfile_test_dir_4/0-128", [1, 2, 3, 4, 5, 6, 7, 8, 9]).unwrap();
        let mut pre_reader = PreReader::new();
        let mut buf = Vec::from([0; 10]);
        hp_file
            .read_at_with_pre_reader(&mut buf, 9, 0, &mut pre_reader)
            .unwrap();
        assert_eq!(buf[0..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(pre_reader.end, 9);
    }

    #[test]
    fn test_prune_head() {
        let dir = TempDir::new("hpfile_test_dir_5");
        let buffer_size = 64;
        let segment_size = 128;
        let hp_file = HPFile::new(buffer_size, segment_size, dir.to_string()).unwrap();
        hp_file.prune_head(segment_size * 2).unwrap();
        assert_eq!(fs::read_dir(dir.to_string()).unwrap().count(), 0);
    }

    #[test]
    fn test_hpfile() {
        let dir = TempDir::new("hpfile_test_dir_6");
        let buffer_size = 64;
        let segment_size = 128;
        let hp_file = HPFile::new(buffer_size, segment_size, dir.to_string()).unwrap();
        let mut buffer = Vec::with_capacity(buffer_size as usize);

        for _i in 0..100 {
            hp_file
                .append("aaaaaaaaaaaaaaaaaaaa".as_bytes(), &mut buffer)
                .unwrap();
            hp_file.flush(&mut buffer).unwrap();
        }

        assert_eq!(
            dir.list().join(","),
            [
                "hpfile_test_dir_6/0-128",
                "hpfile_test_dir_6/1-128",
                "hpfile_test_dir_6/10-128",
                "hpfile_test_dir_6/11-128",
                "hpfile_test_dir_6/12-128",
                "hpfile_test_dir_6/13-128",
                "hpfile_test_dir_6/14-128",
                "hpfile_test_dir_6/15-128",
                "hpfile_test_dir_6/2-128",
                "hpfile_test_dir_6/3-128",
                "hpfile_test_dir_6/4-128",
                "hpfile_test_dir_6/5-128",
                "hpfile_test_dir_6/6-128",
                "hpfile_test_dir_6/7-128",
                "hpfile_test_dir_6/8-128",
                "hpfile_test_dir_6/9-128",
            ]
            .join(",")
        );

        hp_file.prune_head(500).unwrap();

        assert_eq!(
            dir.list().join(","),
            [
                "hpfile_test_dir_6/10-128",
                "hpfile_test_dir_6/11-128",
                "hpfile_test_dir_6/12-128",
                "hpfile_test_dir_6/13-128",
                "hpfile_test_dir_6/14-128",
                "hpfile_test_dir_6/15-128",
                "hpfile_test_dir_6/3-128",
                "hpfile_test_dir_6/4-128",
                "hpfile_test_dir_6/5-128",
                "hpfile_test_dir_6/6-128",
                "hpfile_test_dir_6/7-128",
                "hpfile_test_dir_6/8-128",
                "hpfile_test_dir_6/9-128",
            ]
            .join(",")
        );
    }
}
