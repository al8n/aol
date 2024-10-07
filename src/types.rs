use either::Either;

use super::{buffer::VacantBuffer, *};

/// Maybe a reference entry type or an owned entry.
pub struct MaybeEntryRef<'a, R: Record>(Either<Entry<R::Ref<'a>>, Entry<R>>);

impl<'a, R: Record> MaybeEntryRef<'a, R> {
  /// Get the flag.
  #[inline]
  pub const fn flag(&self) -> EntryFlags {
    match &self.0 {
      Either::Left(entry) => entry.flag(),
      Either::Right(entry) => entry.flag(),
    }
  }

  /// Get the record.
  #[inline]
  pub const fn record(&self) -> Either<&R::Ref<'a>, &R> {
    match &self.0 {
      Either::Left(entry) => Either::Left(entry.record()),
      Either::Right(entry) => Either::Right(entry.record()),
    }
  }

  /// Consumes the `MaybeEntryRef`, returning the inner value.
  #[inline]
  pub fn into_inner(self) -> Either<Entry<R::Ref<'a>>, Entry<R>> {
    match self.0 {
      Either::Left(entry) => Either::Left(entry),
      Either::Right(entry) => Either::Right(entry),
    }
  }

  #[inline]
  pub(crate) fn left(ent: Entry<R::Ref<'a>>) -> Self {
    Self(Either::Left(ent))
  }

  #[inline]
  pub(crate) fn right(ent: Entry<R>) -> Self {
    Self(Either::Right(ent))
  }
}

/// The entry in the append-only file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Entry<R> {
  pub(super) flag: EntryFlags,
  pub(super) data: R,
}

impl<R> AsRef<Self> for Entry<R> {
  #[inline]
  fn as_ref(&self) -> &Self {
    self
  }
}

impl<R> Entry<R> {
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
  pub const fn creation(data: R) -> Self {
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
  pub const fn deletion(data: R) -> Self {
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
  pub const fn creation_with_custom_flags(flag: CustomFlags, data: R) -> Self {
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
  pub const fn deletion_with_custom_flags(flag: CustomFlags, data: R) -> Self {
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
  pub const fn with_flags(flag: EntryFlags, data: R) -> Self {
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

  /// Get the record.
  #[inline]
  pub const fn record(&self) -> &R {
    &self.data
  }

  /// Into the record.
  #[inline]
  pub fn into_record(self) -> R {
    self.data
  }
}

/// Record for the [`Entry`].
pub trait Record: Sized {
  /// The error type returned by encoding.
  type Error;

  /// The reference type for the record.
  type Ref<'a>: RecordRef<'a, Error = Self::Error>;

  /// Returns the encoded size of the data.
  fn encoded_size(&self) -> usize;

  /// Encodes the data into the buffer, returning the number of bytes written.
  fn encode(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, Self::Error>;
}

/// The reference type for the record.
pub trait RecordRef<'a>: Sized {
  /// The error type returned.
  type Error;

  /// Decodes the data from the buffer, returning the number of bytes read.
  fn decode(buf: &'a [u8]) -> Result<(usize, Self), Self::Error>;
}

impl Record for () {
  type Error = core::convert::Infallible;
  type Ref<'a> = ();

  #[inline]
  fn encoded_size(&self) -> usize {
    0
  }

  #[inline]
  fn encode(&self, _buf: &mut VacantBuffer<'_>) -> Result<usize, Self::Error> {
    Ok(0)
  }
}

impl RecordRef<'_> for () {
  type Error = core::convert::Infallible;

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
  pub(super) fn decode<'a, C>(
    buf: &'a [u8],
    cks: &C,
  ) -> Result<(usize, Entry<R::Ref<'a>>), Option<<R::Ref<'a> as RecordRef<'a>>::Error>>
  where
    C: dbutils::checksum::BuildChecksumer,
  {
    let buf_len = buf.len();
    let cks = cks
      .checksum_one(&buf[..buf_len - CHECKSUM_SIZE])
      .to_le_bytes();
    if cks != buf[buf_len - CHECKSUM_SIZE..buf_len] {
      return Err(None);
    }

    let flag = EntryFlags { value: buf[0] };

    let mut cursor = 1;
    let len = u32::from_le_bytes(buf[cursor..cursor + LEN_BUF_SIZE].try_into().unwrap());
    cursor += LEN_BUF_SIZE;

    let (read, data) =
      <R::Ref<'_> as RecordRef>::decode(&buf[cursor..cursor + len as usize]).map_err(Some)?;
    debug_assert_eq!(
      read, len as usize,
      "invalid decoded size, expected {} got {}",
      read, len
    );

    Ok((read + cursor, Entry { flag, data }))
  }
}
