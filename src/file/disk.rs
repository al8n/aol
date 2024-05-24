use std::{
  fs::{File as StdFile, OpenOptions},
  io::{self, BufReader, BufWriter, Read, Write},
  path::Path,
};

use crate::MANIFEST_DELETIONS_REWRITE_THRESHOLD;

use super::*;

/// File options.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FileOptions {
  #[cfg_attr(feature = "serde", serde(skip_serializing_if = "Option::is_none"))]
  read_buffer_size: Option<usize>,
  #[cfg_attr(feature = "serde", serde(skip_serializing_if = "Option::is_none"))]
  write_buffer_size: Option<usize>,
}

impl Default for FileOptions {
  /// Create a default `FileOptions`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::file::FileOptions;
  ///
  /// let opts = FileOptions::default();
  /// ```
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl FileOptions {
  /// Create a new `FileOptions`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::file::FileOptions;
  ///
  /// let opts = FileOptions::new();
  /// ```
  #[inline]
  pub const fn new() -> Self {
    Self {
      read_buffer_size: None,
      write_buffer_size: None,
    }
  }

  /// Set the read buffer size.
  ///
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::file::FileOptions;
  ///
  ///
  /// let opts = FileOptions::new().read_buffer_size(1024);
  /// ```
  #[inline]
  pub const fn read_buffer_size(mut self, size: usize) -> Self {
    self.read_buffer_size = Some(size);
    self
  }

  /// Set the write buffer size.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::file::FileOptions;
  ///
  /// let opts = FileOptions::new().write_buffer_size(1024);
  /// ```
  #[inline]
  pub const fn write_buffer_size(mut self, size: usize) -> Self {
    self.write_buffer_size = Some(size);
    self
  }
}

/// [`File`](super::File) trait implementation based `std::fs::File`.
///
/// **Note:** This implementation is only for [`ManifestFile`](super::ManifestFile), and cannot be used for other purposes.
pub struct File {
  reader: BufReader<StdFile>,
  writer: BufWriter<StdFile>,
}

impl BackedFile for File {
  type Options = FileOptions;

  type Error = io::Error;

  fn open<P: AsRef<Path>>(path: P, opts: Self::Options) -> Result<(bool, Self), Self::Error>
  where
    Self: Sized,
  {
    let path = path.as_ref();
    let existing = path.exists();
    OpenOptions::new()
      .read(true)
      .create(true)
      .truncate(false)
      .append(true)
      .open(path)
      .and_then(|f| {
        Ok((
          existing,
          Self {
            reader: BufReader::with_capacity(
              opts
                .read_buffer_size
                .unwrap_or(MANIFEST_DELETIONS_REWRITE_THRESHOLD as usize),
              f.try_clone()?,
            ),
            writer: BufWriter::with_capacity(
              opts
                .write_buffer_size
                .unwrap_or(MANIFEST_DELETIONS_REWRITE_THRESHOLD as usize),
              f,
            ),
          },
        ))
      })
  }

  fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), Self::Error> {
    self.reader.read_exact(buf)
  }

  fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
    self.writer.write_all(data)
  }

  fn flush(&mut self) -> Result<(), Self::Error> {
    self.writer.get_ref().sync_data()
  }

  fn sync_all(&self) -> Result<(), Self::Error> {
    self.writer.get_ref().sync_all()
  }

  fn truncate(&mut self, len: u64) -> Result<(), Self::Error> {
    self.writer.get_ref().set_len(len)
  }

  fn size(&self) -> Result<u64, Self::Error> {
    self
      .reader
      .get_ref()
      .metadata()
      .map(|m| m.len())
      .map_err(Into::into)
  }
}
