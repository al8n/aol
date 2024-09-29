use among::Among;

/// Errors for append-only file.
#[cfg_attr(feature = "std", derive(thiserror::Error))]
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

  // /// Encode/decode data error.
  // #[error(transparent)]
  // Record(<S::Record as Record>::Error),

  // /// Snapshot error.
  // #[error(transparent)]
  // Snapshot(S::Error),
  /// I/O error.
  #[error(transparent)]
  IO(#[from] std::io::Error),
}

impl core::fmt::Debug for Error {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Display::fmt(self, f)
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
  pub(crate) const fn entry_corrupted<A, B>(len: u32, remaining: u32) -> Among<A, B, Self> {
    Among::Right(Self::EntryTooLarge { len, remaining })
  }
}
