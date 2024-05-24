use super::*;

impl File for Vec<u8> {
  type Options = Option<usize>;

  type Error = core::convert::Infallible;

  #[cfg(feature = "std")]
  fn open<P: AsRef<std::path::Path>>(
    _path: P,
    opts: Self::Options,
  ) -> Result<(bool, Self), Self::Error>
  where
    Self: Sized,
  {
    Ok((
      true,
      Vec::with_capacity(opts.unwrap_or(super::MANIFEST_DELETIONS_REWRITE_THRESHOLD as usize)),
    ))
  }

  #[cfg(not(feature = "std"))]
  fn open(opts: Self::Options) -> Result<(bool, Self), Self::Error>
  where
    Self: Sized,
  {
    Ok((
      true,
      Vec::with_capacity(opts.unwrap_or(super::MANIFEST_DELETIONS_REWRITE_THRESHOLD as usize)),
    ))
  }

  fn read_exact(&mut self, _buf: &mut [u8]) -> Result<(), Self::Error> {
    unreachable!()
  }

  fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
    self.extend_from_slice(data);
    Ok(())
  }

  fn flush(&mut self) -> Result<(), Self::Error> {
    Ok(())
  }

  fn sync_all(&self) -> Result<(), Self::Error> {
    Ok(())
  }

  fn truncate(&mut self, len: u64) -> Result<(), Self::Error> {
    Vec::truncate(self, len as usize);
    Ok(())
  }

  fn size(&self) -> Result<u64, Self::Error> {
    unreachable!()
  }
}
