use among::Among;

use core::fmt::{Debug, Display, Formatter, Result};

/// Errors for append-only file.
#[derive(thiserror::Error)]
pub enum Error {
  /// Missing corrupted append-only log header.
  #[error("missing append-only log header, log may be corrupted")]
  CorruptedHeader,

  /// Snapshot has bad magic.
  #[error("append-only has bad magic text")]
  BadMagicText,
  /// Cannot open append-only because the external magic doesn't match.
  #[error("cannot open append-only because the external magic doesn't match. expected {expected}, found {found}")]
  BadExternalMagic {
    /// Expected external magic.
    expected: u16,
    /// Found external magic.
    found: u16,
  },
  /// Cannot open append-only because the magic doesn't match.
  #[error(
    "cannot open append-only because the magic doesn't match. expected {expected}, found {found}"
  )]
  BadMagic {
    /// Expected magic.
    expected: u16,
    /// Found magic.
    found: u16,
  },
  /// Corrupted append-only file: entry checksum mismatch.
  #[error("entry checksum mismatch")]
  ChecksumMismatch,

  /// Corrupted append-only file: not enough bytes to decode append-only entry.
  #[error("entry data len {len} is greater than the remaining file size {remaining}, append-only file might be corrupted")]
  EntryTooLarge {
    /// Entry data len.
    len: u32,
    /// Remaining file size.
    remaining: u32,
  },
  /// I/O error.
  #[error(transparent)]
  IO(#[from] std::io::Error),
}

impl Debug for Error {
  fn fmt(&self, f: &mut Formatter<'_>) -> Result {
    Display::fmt(self, f)
  }
}

impl Error {
  /// Create a new `Error` from an I/O error.
  #[inline]
  pub(super) const fn io<A, B>(err: std::io::Error) -> Among<A, B, Self> {
    Among::Right(Self::IO(err))
  }

  #[inline]
  pub(super) const fn checksum_mismatch<A, B>() -> Among<A, B, Self> {
    Among::Right(Self::ChecksumMismatch)
  }

  /// Create a new `Corrupted` error.
  #[inline]
  pub(super) const fn entry_corrupted<A, B>(len: u32, remaining: u32) -> Among<A, B, Self> {
    Among::Right(Self::EntryTooLarge { len, remaining })
  }

  #[inline]
  pub(super) const fn bad_external_magic<A, B>(expected: u16, found: u16) -> Among<A, B, Self> {
    Among::Right(Self::BadExternalMagic { expected, found })
  }

  #[inline]
  pub(super) const fn bad_magic<A, B>(expected: u16, found: u16) -> Among<A, B, Self> {
    Among::Right(Self::BadMagic { expected, found })
  }

  #[inline]
  pub(super) const fn corrupted_header<A, B>() -> Among<A, B, Self> {
    Among::Right(Self::CorruptedHeader)
  }
}

#[cfg(feature = "std")]
#[inline]
pub(super) fn read_only_error() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::PermissionDenied, "append log read-only")
}
