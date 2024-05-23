// /// Checksum mismatch.
// #[derive(Debug)]
// #[cfg_attr(feature = "std", derive(thiserror::Error))]
// #[cfg_attr(feature = "std", error("checksum mismatch"))]
// pub struct ChecksumMismatch;

// #[cfg(not(feature = "std"))]
// impl core::fmt::Display for ChecksumMismatch {
//   fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
//     write!(f, "checksum mismatch")
//   }
// }

/// Errors for manifest file.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
pub enum Error<F: super::File, D: super::Data> {
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
  #[error("corrupted manifest file")]
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  Corrupted,

  /// Encode/decode data error.
  #[cfg_attr(feature = "std", error(transparent))]
  Data(D::Error),

  // /// Unknown manifest event.
  // #[error(transparent)]
  // #[cfg(feature = "std")]
  // #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  // UnknownManifestEvent(#[from] UnknownManifestEvent),
  /// I/O error.
  #[cfg_attr(feature = "std", error(transparent))]
  IO(F::Error),
}

impl<F: super::File, D: super::Data> Error<F, D> {
  /// Create a new `Error` from an I/O error.
  #[inline]
  pub const fn io(err: F::Error) -> Self {
    Self::IO(err)
  }

  /// Create a new `Error` from a data error.
  #[inline]
  pub const fn data(err: D::Error) -> Self {
    Self::Data(err)
  }
}
