use super::*;

/// Errors for append-only file.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
pub enum Error<F, M: Manifest> {
  /// Manifest has bad magic.
  #[cfg_attr(feature = "std", error("append-only has bad magic text"))]
  BadMagicText,
  /// Cannot open append-only because the external magic doesn't match.
  #[cfg_attr(feature = "std", error("cannot open append-only because the external magic doesn't match. expected {expected}, found {found}"))]
  BadExternalMagic {
    /// Expected external magic.
    expected: u16,
    /// Found external magic.
    found: u16,
  },
  /// Cannot open append-only because the magic doesn't match.
  #[cfg_attr(
    feature = "std",
    error(
      "cannot open append-only because the magic doesn't match. expected {expected}, found {found}"
    )
  )]
  BadMagic {
    /// Expected magic.
    expected: u16,
    /// Found magic.
    found: u16,
  },

  /// Corrupted append-only file: entry checksum mismatch.
  #[cfg_attr(feature = "std", error("entry checksum mismatch"))]
  ChecksumMismatch,

  /// Corrupted append-only file: not enough bytes to decode append-only entry.
  #[cfg_attr(feature = "std", error("entry data len {len} is greater than the remaining file size {remaining}, append-only file might be corrupted"))]
  EntryTooLarge {
    /// Entry data len.
    len: u32,
    /// Remaining file size.
    remaining: u32,
  },

  /// Encode/decode data error.
  #[cfg_attr(feature = "std", error(transparent))]
  Data(<M::Data as Data>::Error),

  /// Manifest error.
  #[cfg_attr(feature = "std", error(transparent))]
  Manifest(M::Error),

  /// I/O error.
  #[cfg_attr(feature = "std", error(transparent))]
  IO(F),
}

#[cfg(not(feature = "std"))]
impl<F: BackedFile, M: Manifest> core::fmt::Display for Error<F, M> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::BadExternalMagic { expected, found } => write!(
        f,
        "cannot open append-only because the external magic doesn't match. expected {}, found {}",
        expected, found
      ),
      Self::BadMagic { expected, found } => write!(
        f,
        "cannot open append-only because the magic doesn't match. expected {}, found {}",
        expected, found
      ),
      Self::BadMagicText => write!(f, "append-only has bad magic text"),
      Self::ChecksumMismatch => write!(f, "entry checksum mismatch"),
      Self::EntryTooLarge { len, remaining } => write!(
        f,
        "entry data len {} is greater than the remaining file size {}, append-only file might be corrupted",
        len, remaining
      ),
      Self::Data(err) => err.fmt(f),
      Self::Manifest(err) => err.fmt(f),
      Self::IO(err) => err.fmt(f),
    }
  }
}

impl<F: core::fmt::Debug + core::fmt::Display, M: Manifest> Error<F, M> {
  /// Create a new `Error` from an I/O error.
  #[inline]
  pub const fn io(err: F) -> Self {
    Self::IO(err)
  }

  /// Create a new `Error` from a data error.
  #[inline]
  pub const fn data(err: <M::Data as Data>::Error) -> Self {
    Self::Data(err)
  }

  /// Create a new `Error` from an unknown append-only event.
  #[inline]
  pub const fn manifest(err: M::Error) -> Self {
    Self::Manifest(err)
  }

  /// Create a new `Corrupted` error.
  #[inline]
  pub(crate) const fn entry_corrupted(len: u32, remaining: u32) -> Self {
    Self::EntryTooLarge { len, remaining }
  }
}
