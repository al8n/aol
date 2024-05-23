use std::{
  fs::{File as StdFile, OpenOptions},
  io::{self, BufWriter, Read, Write},
  path::PathBuf,
};

use super::*;

impl super::File for StdFile {
  type Options = PathBuf;

  type Error = io::Error;

  fn open(path: &Self::Options) -> Result<(bool, Self), Self::Error>
  where
    Self: Sized,
  {
    let existing = path.exists();
    OpenOptions::new()
      .read(true)
      .create(true)
      .truncate(false)
      .append(true)
      .open(path)
      .map(|f| (existing, f))
  }

  fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), Self::Error> {
    Read::read_exact(self, buf)
  }

  fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
    Write::write_all(self, data)
  }

  fn flush(&mut self) -> Result<(), Self::Error> {
    self.sync_data()
  }

  fn sync_all(&self) -> Result<(), Self::Error> {
    self.sync_all()
  }

  fn truncate(&mut self, len: u64) -> Result<(), Self::Error> {
    self.set_len(len)
  }

  fn size(&self) -> Result<u64, Self::Error> {
    self.metadata().map(|m| m.len()).map_err(Into::into)
  }
}

impl super::File for BufWriter<StdFile> {
  type Options = PathBuf;

  type Error = io::Error;

  fn open(opts: &Self::Options) -> Result<(bool, Self), Self::Error>
  where
    Self: Sized,
  {
    let existing = opts.exists();
    OpenOptions::new()
      .read(true)
      .create(true)
      .truncate(false)
      .append(true)
      .open(opts)
      .map(|f| (existing, BufWriter::new(f)))
  }

  fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), Self::Error> {
    Read::read_exact(self.get_mut(), buf)
  }

  fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
    Write::write_all(self, data)
  }

  fn flush(&mut self) -> Result<(), Self::Error> {
    Write::flush(self).and_then(|_| self.get_mut().sync_data())
  }

  fn sync_all(&self) -> Result<(), Self::Error> {
    self.get_ref().sync_all()
  }

  fn truncate(&mut self, len: u64) -> Result<(), Self::Error> {
    self.get_mut().set_len(len)
  }

  fn size(&self) -> Result<u64, Self::Error> {
    self
      .get_ref()
      .metadata()
      .map(|m| m.len())
      .map_err(Into::into)
  }
}
