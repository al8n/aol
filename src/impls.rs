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
