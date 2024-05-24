/// Errors for manifest file.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[cfg_attr(not(feature = "std"), derive(parse_display::Display))]
pub enum Error<F: super::File, M: super::Manifest> {
  /// Manifest has bad magic.
  #[error("manifest has bad magic text")]
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  BadMagicText,
  /// Cannot open manifest because the external magic doesn't match.
  #[error("cannot open manifest because the external magic doesn't match. expected {expected}, found {found}")]
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  BadExternalMagic {
    /// Expected external magic.
    expected: u16,
    /// Found external magic.
    found: u16,
  },
  /// Cannot open manifest because the magic doesn't match.
  #[error(
    "cannot open manifest because the magic doesn't match. expected {expected}, found {found}"
  )]
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  BadMagic {
    /// Expected magic.
    expected: u16,
    /// Found magic.
    found: u16,
  },
  /// Corrupted manifest file: entry checksum mismatch.
  #[error("entry checksum mismatch")]
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  ChecksumMismatch,

  /// Corrupted manifest file: not enough bytes to decode manifest entry.
  #[error("entry data len {len} is greater than the remaining file size {remaining}, manifest file might be corrupted")]
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  EntryTooLarge {
    /// Entry data len.
    len: u32,
    /// Remaining file size.
    remaining: u32,
  },

  /// Encode/decode data error.
  #[cfg_attr(feature = "std", error(transparent))]
  Data(<M::Data as super::Data>::Error),

  /// Manifest error.
  #[cfg_attr(feature = "std", error(transparent))]
  Manifest(M::Error),

  /// I/O error.
  #[cfg_attr(feature = "std", error(transparent))]
  IO(F::Error),
}

#[cfg(not(feature = "std"))]
impl<F: super::File, M: super::Manifest> core::fmt::Display for Error<F, M> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::Data(err) => err.fmt(f),
      Self::Manifest(err) => err.fmt(f),
      Self::IO(err) => err.fmt(f),
    }
  }
}

impl<F: super::File, M: super::Manifest> Error<F, M> {
  /// Create a new `Error` from an I/O error.
  #[inline]
  pub const fn io(err: F::Error) -> Self {
    Self::IO(err)
  }

  /// Create a new `Error` from a data error.
  #[inline]
  pub const fn data(err: <M::Data as super::Data>::Error) -> Self {
    Self::Data(err)
  }

  /// Create a new `Error` from an unknown manifest event.
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
