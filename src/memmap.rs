use core::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "std")]
use std::path::PathBuf;

use super::*;

const CURRENT_VERSION: u16 = 0;
const HEADER_SIZE: usize = MAGIC_TEXT_LEN + MAGIC_VERSION_LEN; // magic text + external magic + magic

/// Lock-free concurrent safe append-only log based on memory-map.
pub mod sync;

/// Append-only log based on memory-map.
pub mod unsync;

/// Options for the append only log.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Options {
  magic_version: u16,
  sync_on_write: bool,
  capacity: u32,
}

impl Default for Options {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl Options {
  /// Create a new Options with the given capacity.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
  ///
  /// let opts = Options::new(10_000);
  /// ```
  #[inline]
  pub const fn new() -> Self {
    Self {
      magic_version: 0,
      sync_on_write: true,
      capacity: 0,
    }
  }

  /// Get the external magic.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.magic_version(), 0);
  /// ```
  #[inline]
  pub const fn magic_version(&self) -> u16 {
    self.magic_version
  }

  /// Get whether flush the data to disk after write.
  ///
  /// Default is `true`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.sync_on_write(), true);
  /// ```
  #[inline]
  pub const fn sync_on_write(&self) -> bool {
    self.sync_on_write
  }

  /// Get the capacity of the append-only log.
  ///
  /// This configuration is used to pre-allocate the append-only log.
  /// When using [`AppendLog::map`], this configuration will be ignored.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
  ///
  /// let opts = Options::new().with_capacity(10_000);
  ///
  /// assert_eq!(opts.capacity(), 0);
  /// ```
  #[inline]
  pub const fn capacity(&self) -> u32 {
    self.capacity
  }

  /// Set the external magic.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
  ///
  /// let opts = Options::new().with_magic_version(1);
  ///
  /// assert_eq!(opts.magic_version(), 1);
  /// ```
  #[inline]
  pub const fn with_magic_version(mut self, magic_version: u16) -> Self {
    self.magic_version = magic_version;
    self
  }

  /// Set whether flush the data to disk after write.
  ///
  /// Default is `true`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
  ///
  /// let opts = Options::new().with_sync_on_write(false);
  ///
  /// assert_eq!(opts.sync_on_write(), false);
  /// ```
  #[inline]
  pub const fn with_sync_on_write(mut self, sync_on_write: bool) -> Self {
    self.sync_on_write = sync_on_write;
    self
  }

  /// Set the capacity of the append-only log.
  ///
  /// This configuration is used to pre-allocate the append-only log.
  /// When using [`AppendLog::map`], this configuration will be ignored.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
  ///
  /// let opts = Options::new().with_capacity(10_000);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Self {
    self.capacity = capacity;
    self
  }
}
