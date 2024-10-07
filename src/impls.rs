use core::convert::Infallible;

use dbutils::buffer::VacantBuffer;
use either::Either;

use super::{Entry, MaybeEntryRef, Record, RecordRef, Snapshot};

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

impl Snapshot for () {
  type Record = ();

  type Options = ();

  type Error = Infallible;

  #[inline]
  fn new(_opts: Self::Options) -> Result<Self, Self::Error> {
    Ok(())
  }

  #[inline]
  fn should_rewrite(&self, _size: u64) -> bool {
    false
  }

  #[inline]
  fn validate(
    &self,
    _entry: &Entry<Self::Record>,
  ) -> Result<(), Either<<Self::Record as Record>::Error, Self::Error>> {
    Ok(())
  }

  #[inline]
  fn contains(&self, _entry: &Entry<<Self::Record as Record>::Ref<'_>>) -> bool {
    true
  }

  #[inline]
  fn insert(&mut self, _entry: MaybeEntryRef<'_, Self::Record>) {}

  #[inline]
  fn clear(&mut self) -> Result<(), Self::Error> {
    Ok(())
  }
}

macro_rules! batch_impl {
  ($ty:ty) => {
    type Iter<'a>
      = ::core::slice::Iter<'a, I>
    where
      R: 'a,
      Self: 'a,
      I: AsRef<Entry<R>> + 'a;
    type IntoIter
      = <$ty as ::core::iter::IntoIterator>::IntoIter
    where
      I: Into<Entry<R>>;

    #[inline]
    fn len(&self) -> usize {
      <[I]>::len(self)
    }

    #[inline]
    fn is_empty(&self) -> bool {
      <[I]>::is_empty(self)
    }

    #[inline]
    fn iter<'a>(&'a self) -> Self::Iter<'a>
    where
      R: 'a,
      I: AsRef<Entry<R>> + 'a,
    {
      <[I]>::iter(self)
    }

    #[inline]
    fn into_iter(self) -> Self::IntoIter
    where
      I: Into<Entry<R>>,
    {
      ::core::iter::IntoIterator::into_iter(self)
    }
  };
}

macro_rules! impl_batch_for_vec {
  ($($ty:ty), +$(,)?) => {
    $(
      impl<I, R> $crate::Batch<I, R> for $ty
      where
        I: AsRef<I> + Into<I>,
      {
        batch_impl!($ty);
      }
    )*
  };
}

impl_batch_for_vec!(::std::vec::Vec<I>, ::std::boxed::Box<[I]>,);

#[cfg(feature = "smallvec-wrapper")]
mod sw {
  use smallvec_wrapper::*;

  use super::Entry;

  impl_batch_for_vec!(
    OneOrMore<I>,
    TinyVec<I>,
    TriVec<I>,
    SmallVec<I>,
    MediumVec<I>,
    LargeVec<I>,
    XLargeVec<I>,
    XXLargeVec<I>,
    XXXLargeVec<I>,
  );
}

macro_rules! impl_batch_for_array {
  ($($ty:ty), +$(,)?) => {
    $(
      impl<I, R, const N: usize> $crate::Batch<I, R> for $ty {
        batch_impl!($ty);
      }
    )*
  };
}

impl_batch_for_array!([I; N]);

#[cfg(feature = "smallvec")]
impl_batch_for_array!(::smallvec::SmallVec<[I; N]>);
