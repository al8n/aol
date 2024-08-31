use std::fs::OpenOptions;

use aol::{Batch, Entry};

struct Sample {
  a: u64,
  b: u64,
}

impl aol::Record for Sample {
  type Error = core::convert::Infallible;

  fn encoded_size(&self) -> usize {
    16
  }

  fn encode(&self, buf: &mut [u8]) -> Result<usize, Self::Error> {
    buf[..8].copy_from_slice(&self.a.to_le_bytes());
    buf[8..].copy_from_slice(&self.b.to_le_bytes());
    Ok(16)
  }

  fn decode(buf: &[u8]) -> Result<(usize, Self), Self::Error> {
    let a = u64::from_le_bytes(buf[..8].try_into().unwrap());
    let b = u64::from_le_bytes(buf[8..].try_into().unwrap());
    Ok((16, Self { a, b }))
  }
}

struct SampleSnapshot {
  creations: Vec<Sample>,
  deletions: Vec<Sample>,
}

impl aol::fs::Snapshot for SampleSnapshot {
  type Record = Sample;

  type Options = ();

  type Error = core::convert::Infallible;

  fn new(_opts: Self::Options) -> Result<Self, Self::Error> {
    Ok(Self {
      creations: Vec::new(),
      deletions: Vec::new(),
    })
  }

  fn should_rewrite(&self, _size: u64) -> bool {
    self.deletions.len() > 100
  }

  fn validate(&self, _entry: &Entry<Self::Record>) -> Result<(), Self::Error> {
    Ok(())
  }

  fn insert(&mut self, entry: Entry<Self::Record>) -> Result<(), Self::Error> {
    if entry.flag().is_creation() {
      self.creations.push(entry.into_data());
    } else {
      self.deletions.push(entry.into_data());
    }
    Ok(())
  }

  fn insert_batch<B: Batch<Self::Record>>(&mut self, entries: B) -> Result<(), Self::Error> {
    for entry in entries.into_iter() {
      self.insert(entry)?;
    }
    Ok(())
  }

  fn clear(&mut self) -> Result<(), Self::Error> {
    self.creations.clear();
    self.deletions.clear();
    Ok(())
  }
}

impl aol::memmap::Snapshot for SampleSnapshot {
  type Record = Sample;

  type Options = ();

  type Error = core::convert::Infallible;

  fn new(_opts: Self::Options) -> Result<Self, Self::Error> {
    Ok(Self {
      creations: Vec::new(),
      deletions: Vec::new(),
    })
  }

  fn should_rewrite(&self, _size: usize) -> bool {
    self.deletions.len() > 100
  }

  fn validate(&self, _entry: &Entry<Self::Record>) -> Result<(), Self::Error> {
    Ok(())
  }

  fn insert(&mut self, entry: Entry<Self::Record>) -> Result<(), Self::Error> {
    if entry.flag().is_creation() {
      self.creations.push(entry.into_data());
    } else {
      self.deletions.push(entry.into_data());
    }
    Ok(())
  }

  fn insert_batch<B: Batch<Self::Record>>(&mut self, entries: B) -> Result<(), Self::Error> {
    for entry in entries.into_iter() {
      self.insert(entry)?;
    }
    Ok(())
  }

  fn clear(&mut self) -> Result<(), Self::Error> {
    self.creations.clear();
    self.deletions.clear();
    Ok(())
  }
}

trait AppendLog {
  type Record: aol::Record;
  type Error: std::error::Error;

  fn append(&mut self, entry: Entry<Self::Record>) -> Result<(), Self::Error>;

  fn append_batch(&mut self, entries: Vec<Entry<Self::Record>>) -> Result<(), Self::Error>;

  fn flush(&self) -> Result<(), Self::Error>;

  fn flush_async(&self) -> Result<(), Self::Error>;

  fn sync_all(&self) -> Result<(), Self::Error>;

  fn rewrite(&mut self) -> Result<(), Self::Error>;
}

impl<S: aol::fs::Snapshot> AppendLog for aol::fs::AppendLog<S> {
  type Record = S::Record;
  type Error = aol::fs::Error<S>;

  fn append(&mut self, entry: Entry<Self::Record>) -> Result<(), Self::Error> {
    aol::fs::AppendLog::append(self, entry)
  }

  fn append_batch(&mut self, batch: Vec<Entry<Self::Record>>) -> Result<(), Self::Error> {
    aol::fs::AppendLog::append_batch(self, batch)
  }

  fn flush(&self) -> Result<(), Self::Error> {
    aol::fs::AppendLog::sync_data(self).map_err(Into::into)
  }

  fn flush_async(&self) -> Result<(), Self::Error> {
    aol::fs::AppendLog::sync_data(self).map_err(Into::into)
  }

  fn sync_all(&self) -> Result<(), Self::Error> {
    aol::fs::AppendLog::sync_all(self).map_err(Into::into)
  }

  fn rewrite(&mut self) -> Result<(), Self::Error> {
    aol::fs::AppendLog::rewrite(self).map_err(Into::into)
  }
}

impl<S: aol::memmap::Snapshot> AppendLog for aol::memmap::AppendLog<S> {
  type Record = S::Record;
  type Error = aol::memmap::Error<S>;

  fn append(&mut self, entry: Entry<Self::Record>) -> Result<(), Self::Error> {
    aol::memmap::AppendLog::append(self, entry)
  }

  fn append_batch(&mut self, batch: Vec<Entry<Self::Record>>) -> Result<(), Self::Error> {
    aol::memmap::AppendLog::append_batch(self, batch)
  }

  fn flush(&self) -> Result<(), Self::Error> {
    aol::memmap::AppendLog::flush(self).map_err(Into::into)
  }

  fn flush_async(&self) -> Result<(), Self::Error> {
    aol::memmap::AppendLog::flush_async(self).map_err(Into::into)
  }

  fn sync_all(&self) -> Result<(), Self::Error> {
    aol::memmap::AppendLog::sync_all(self).map_err(Into::into)
  }

  fn rewrite(&mut self) -> Result<(), Self::Error> {
    aol::memmap::AppendLog::rewrite(self).map_err(Into::into)
  }
}

fn basic_write_entry<L: AppendLog<Record = Sample>>(mut l: L) {
  const N: usize = 5001;

  for i in 0..N {
    if i % 3 == 0 {
      l.append(Entry::creation(Sample {
        a: i as u64,
        b: i as u64,
      }))
      .unwrap();
      l.flush_async().unwrap();
    } else if i % 3 == 1 {
      l.append(Entry::deletion(Sample {
        a: i as u64,
        b: i as u64,
      }))
      .unwrap();
      l.flush().unwrap();
    } else {
      let mut batch = Vec::with_capacity(10);
      for j in 0..10 {
        if j % 2 == 0 {
          batch.push(Entry::creation(Sample {
            a: i as u64,
            b: j as u64,
          }));
        } else {
          batch.push(Entry::deletion(Sample {
            a: i as u64,
            b: j as u64,
          }));
        }
      }

      l.append_batch(batch).unwrap();
      l.sync_all().unwrap();
    }
  }
}

#[test]
fn file_basic() {
  use aol::fs::{AppendLog, Options};

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("fs.log");
  let mut open_opts = OpenOptions::new();
  open_opts.read(true).create(true).append(true);
  let l = AppendLog::<SampleSnapshot>::open(&p, (), open_opts, Options::new()).unwrap();
  basic_write_entry(l);

  let mut open_opts = OpenOptions::new();
  open_opts.read(true).create(true).append(true);
  let l = AppendLog::<SampleSnapshot>::open(&p, (), open_opts, Options::new()).unwrap();

  assert_eq!(l.snapshot().creations.len(), 10002);
}

#[test]
fn memmap_basic() {
  use aol::memmap::{AppendLog, Options};

  const GB: usize = 1024 * 1024 * 1024;

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("memmap.log");
  let l = AppendLog::<SampleSnapshot>::map_mut(&p, Options::new(GB), ()).unwrap();
  basic_write_entry(l);

  let l = AppendLog::<SampleSnapshot>::map(&p, Options::new(GB), ()).unwrap();

  assert_eq!(l.snapshot().creations.len(), 10002);
}

fn rewrite<L: AppendLog<Record = Sample>>(mut l: L) {
  const N: usize = 200;

  for i in 0..N {
    if i % 2 == 1 && i < 50 {
      l.append(Entry::deletion(Sample {
        a: i as u64,
        b: i as u64,
      }))
      .unwrap();
      continue;
    }

    l.append(Entry::creation(Sample {
      a: i as u64,
      b: i as u64,
    }))
    .unwrap();
    l.flush_async().unwrap();
  }

  l.rewrite().unwrap();
}

#[test]
fn file_rewrite_policy_skip() {
  use aol::fs::{AppendLog, Options};

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("fs_rewrite_policy.log");
  let mut open_opts = OpenOptions::new();
  open_opts.read(true).create(true).append(true);
  let l = AppendLog::<SampleSnapshot>::open(
    &p,
    (),
    open_opts,
    Options::new().with_rewrite_policy(aol::RewritePolicy::Skip(100)),
  )
  .unwrap();
  rewrite(l);

  let mut open_opts = OpenOptions::new();
  open_opts.read(true).create(true).append(true);
  let l = AppendLog::<SampleSnapshot>::open(&p, (), open_opts, Options::new()).unwrap();

  assert_eq!(l.snapshot().creations.len(), 75);
}

#[test]
fn file_rewrite() {
  use aol::fs::{AppendLog, Options};

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("fs_rewrite_policy.log");
  let mut open_opts = OpenOptions::new();
  open_opts.read(true).create(true).append(true);
  let l = AppendLog::<SampleSnapshot>::open(&p, (), open_opts, Options::new()).unwrap();
  rewrite(l);

  let mut open_opts = OpenOptions::new();
  open_opts.read(true).create(true).append(true);
  let l = AppendLog::<SampleSnapshot>::open(&p, (), open_opts, Options::new()).unwrap();

  assert_eq!(l.snapshot().creations.len(), 175);
}

#[test]
fn memmap_rewrite_policy_skip() {
  use aol::memmap::{AppendLog, Options};

  const GB: usize = 1024 * 1024 * 1024;

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("memmap_rewrite_policy.log");
  let l = AppendLog::<SampleSnapshot>::map_mut(
    &p,
    Options::new(GB).with_rewrite_policy(aol::RewritePolicy::Skip(100)),
    (),
  )
  .unwrap();
  rewrite(l);

  let l = AppendLog::<SampleSnapshot>::map(&p, Options::new(GB), ()).unwrap();

  assert_eq!(l.snapshot().creations.len(), 75);
}

#[test]
fn memmap_rewrite() {
  use aol::memmap::{AppendLog, Options};

  const GB: usize = 1024 * 1024 * 1024;

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("memmap_rewrite.log");
  let l = AppendLog::<SampleSnapshot>::map_mut(&p, Options::new(GB), ()).unwrap();
  rewrite(l);

  let l = AppendLog::<SampleSnapshot>::map(&p, Options::new(GB), ()).unwrap();

  assert_eq!(l.snapshot().creations.len(), 175);
}
