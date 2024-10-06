use buffer::VacantBuffer;

use super::*;

/// The entry in the append-only file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Entry<D> {
  pub(super) flag: EntryFlags,
  pub(super) data: D,
}

impl<D> AsRef<Self> for Entry<D> {
  #[inline]
  fn as_ref(&self) -> &Self {
    self
  }
}

impl<D> Entry<D> {
  /// Create a new creation entry.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::Entry;
  ///
  /// let entry = Entry::<()>::creation(());
  /// ```
  #[inline]
  pub const fn creation(data: D) -> Self {
    Self {
      flag: EntryFlags::creation(),
      data,
    }
  }

  /// Create a new deletion entry.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::Entry;
  ///
  /// let entry = Entry::<()>::deletion(());
  /// ```
  #[inline]
  pub const fn deletion(data: D) -> Self {
    Self {
      flag: EntryFlags::deletion(),
      data,
    }
  }

  /// Create a new creation entry with custom flags.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::{Entry, CustomFlags};
  ///
  /// let entry = Entry::creation_with_custom_flags(CustomFlags::empty(), ());
  /// ```
  #[inline]
  pub const fn creation_with_custom_flags(flag: CustomFlags, data: D) -> Self {
    Self {
      flag: EntryFlags::creation_with_custom_flag(flag),
      data,
    }
  }

  /// Create a new deletion entry with custom flags.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::{Entry, CustomFlags};
  ///
  /// let entry = Entry::deletion_with_custom_flags(CustomFlags::empty(), ());
  /// ```
  #[inline]
  pub const fn deletion_with_custom_flags(flag: CustomFlags, data: D) -> Self {
    Self {
      flag: EntryFlags::deletion_with_custom_flag(flag),
      data,
    }
  }

  /// Create a new entry with given [`EntryFlags`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::{Entry, EntryFlags};
  ///
  /// let entry = Entry::with_flags(EntryFlags::creation(), ());
  /// ```
  #[inline]
  pub const fn with_flags(flag: EntryFlags, data: D) -> Self {
    Self { flag, data }
  }

  /// Get the flag.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::{Entry, EntryFlags, CustomFlags};
  ///
  /// let entry = Entry::creation(());
  ///
  /// assert_eq!(entry.flag(), EntryFlags::creation());
  /// ```
  #[inline]
  pub const fn flag(&self) -> EntryFlags {
    self.flag
  }

  /// Get the data.
  #[inline]
  pub const fn data(&self) -> &D {
    &self.data
  }

  /// Into the data.
  #[inline]
  pub fn into_data(self) -> D {
    self.data
  }
}

/// Record for the [`Entry`].
pub trait Record: Sized {
  /// The error type returned by encoding.
  type Error;

  /// Returns the encoded size of the data.
  fn encoded_size(&self) -> usize;

  /// Encodes the data into the buffer, returning the number of bytes written.
  fn encode(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, Self::Error>;

  /// Decodes the data from the buffer, returning the number of bytes read.
  fn decode(buf: &[u8]) -> Result<(usize, Self), Self::Error>;
}

impl Record for () {
  type Error = core::convert::Infallible;

  #[inline]
  fn encoded_size(&self) -> usize {
    0
  }

  #[inline]
  fn encode(&self, _buf: &mut VacantBuffer<'_>) -> Result<usize, Self::Error> {
    Ok(0)
  }

  #[inline]
  fn decode(_buf: &[u8]) -> Result<(usize, Self), Self::Error> {
    Ok((0, ()))
  }
}

impl<R: Record> Entry<R> {
  #[cfg(feature = "std")]
  #[inline]
  pub(super) fn encode<C>(
    &self,
    data_encoded_len: usize,
    buf: &mut [u8],
    cks: &C,
  ) -> Result<usize, R::Error>
  where
    C: dbutils::checksum::BuildChecksumer,
  {
    use core::ptr::NonNull;

    let mut cursor = 0;
    buf[cursor] = self.flag.value;
    cursor += 1;
    buf[cursor..cursor + LEN_BUF_SIZE].copy_from_slice(&(data_encoded_len as u32).to_le_bytes());
    cursor += LEN_BUF_SIZE;
    let mut vb = unsafe {
      VacantBuffer::new(
        data_encoded_len,
        NonNull::new_unchecked(buf.as_mut_ptr().add(cursor)),
      )
    };
    let encoded = self.data.encode(&mut vb)?;
    debug_assert_eq!(
      data_encoded_len, encoded,
      "invalid data encoded size, expected {} got {}",
      data_encoded_len, encoded,
    );
    cursor += encoded;

    let cks = cks.checksum_one(&buf[..cursor]).to_le_bytes();
    buf[cursor..cursor + CHECKSUM_SIZE].copy_from_slice(&cks);
    cursor += CHECKSUM_SIZE;

    debug_assert_eq!(
      cursor,
      FIXED_ENTRY_LEN + data_encoded_len,
      "invalid encoded size, expected {} got {}",
      cursor,
      FIXED_ENTRY_LEN + data_encoded_len
    );
    Ok(cursor)
  }

  #[cfg(feature = "std")]
  #[inline]
  pub(super) fn decode<C>(buf: &[u8], cks: &C) -> Result<(usize, Self), Option<R::Error>>
  where
    C: dbutils::checksum::BuildChecksumer,
  {
    let flag = EntryFlags { value: buf[0] };

    let mut cursor = 1;
    let len = u32::from_le_bytes(buf[cursor..cursor + LEN_BUF_SIZE].try_into().unwrap());
    cursor += LEN_BUF_SIZE;
    let buf_len = buf.len();
    let cks = cks
      .checksum_one(&buf[..buf_len - CHECKSUM_SIZE])
      .to_le_bytes();
    if cks != buf[buf_len - CHECKSUM_SIZE..buf_len] {
      return Err(None);
    }
    let (read, data) = R::decode(&buf[cursor..cursor + len as usize]).map_err(Some)?;
    debug_assert_eq!(
      read, len as usize,
      "invalid decoded size, expected {} got {}",
      read, len
    );

    Ok((read + cursor, Self { flag, data }))
  }
}
