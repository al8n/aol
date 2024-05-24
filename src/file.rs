mod memory;

#[cfg(feature = "std")]
mod disk;
#[cfg(feature = "std")]
pub use disk::*;

/// The error type for the file.
#[cfg(feature = "std")]
pub trait BackedFileError: std::error::Error {
  /// Returns whether the error is EOF.
  fn is_eof(&self) -> bool;
}

#[cfg(feature = "std")]
impl BackedFileError for std::io::Error {
  #[inline]
  fn is_eof(&self) -> bool {
    self.kind() == std::io::ErrorKind::UnexpectedEof
  }
}

impl BackedFileError for core::convert::Infallible {
  #[inline]
  fn is_eof(&self) -> bool {
    false
  }
}

/// The error type for the file.
#[cfg(not(feature = "std"))]
pub trait BackedFileError: core::fmt::Debug + core::fmt::Display {
  /// Returns whether the error is EOF.
  fn is_eof(&self) -> bool;
}

/// The underlying file.
pub trait BackedFile {
  /// Options for opening a manifest file.
  type Options;

  /// Error type for the file.
  type Error: BackedFileError;

  /// Open a manifest file with the given options, returning the file and whether it's a new file.
  #[cfg(feature = "std")]
  fn open<P: AsRef<std::path::Path>>(
    path: P,
    opts: Self::Options,
  ) -> Result<(bool, Self), Self::Error>
  where
    Self: Sized;

  /// Open a manifest file with the given options, returning the file and whether it's a new file.
  #[cfg(not(feature = "std"))]
  fn open(opts: Self::Options) -> Result<(bool, Self), Self::Error>
  where
    Self: Sized;

  /// Read exactly `buf.len()` bytes into the buffer.
  fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), Self::Error>;

  /// Write all the data to the file.
  fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error>;

  /// Flush the file.
  fn flush(&mut self) -> Result<(), Self::Error>;

  /// Sync the file.
  fn sync_all(&self) -> Result<(), Self::Error>;

  /// Truncate the file.
  fn truncate(&mut self, len: u64) -> Result<(), Self::Error>;

  /// Returns the size of the file.
  fn size(&self) -> Result<u64, Self::Error>;
}
