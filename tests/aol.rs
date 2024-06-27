use std::fs::OpenOptions;

use aol::Entry;

struct Sample {
  a: u64,
  b: u64,
}

impl aol::Data for Sample {
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
  type Data = Sample;

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

  fn insert(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error> {
    if entry.flag().is_creation() {
      self.creations.push(entry.into_data());
    } else {
      self.deletions.push(entry.into_data());
    }
    Ok(())
  }

  fn insert_batch(&mut self, entries: Vec<Entry<Self::Data>>) -> Result<(), Self::Error> {
    for entry in entries {
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
  type Data = Sample;

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

  fn insert(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error> {
    if entry.flag().is_creation() {
      self.creations.push(entry.into_data());
    } else {
      self.deletions.push(entry.into_data());
    }
    Ok(())
  }

  fn insert_batch(&mut self, entries: Vec<Entry<Self::Data>>) -> Result<(), Self::Error> {
    for entry in entries {
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
  type Data: aol::Data;
  type Error: std::error::Error;

  fn append(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error>;

  fn append_batch(&mut self, entries: Vec<Entry<Self::Data>>) -> Result<(), Self::Error>;
}

impl<S: aol::fs::Snapshot> AppendLog for aol::fs::AppendLog<S> {
  type Data = S::Data;
  type Error = aol::fs::Error<S>;

  fn append(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error> {
    aol::fs::AppendLog::append(self, entry)
  }

  fn append_batch(&mut self, batch: Vec<Entry<Self::Data>>) -> Result<(), Self::Error> {
    aol::fs::AppendLog::append_batch(self, batch)
  }
}

impl<S: aol::memmap::Snapshot> AppendLog for aol::memmap::AppendLog<S> {
  type Data = S::Data;
  type Error = aol::memmap::Error<S>;

  fn append(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error> {
    aol::memmap::AppendLog::append(self, entry)
  }

  fn append_batch(&mut self, batch: Vec<Entry<Self::Data>>) -> Result<(), Self::Error> {
    aol::memmap::AppendLog::append_batch(self, batch)
  }
}

fn basic_write_entry<L: AppendLog<Data = Sample>>(mut l: L) {
  const N: usize = 5001;

  for i in 0..N {
    if i % 3 == 0 {
      l.append(Entry::creation(Sample {
        a: i as u64,
        b: i as u64,
      }))
      .unwrap();
    } else if i % 3 == 1 {
      l.append(Entry::deletion(Sample {
        a: i as u64,
        b: i as u64,
      }))
      .unwrap();
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
  let mut open_opts = OpenOptions::new();
  open_opts.read(true).create(true).append(true);
  let l = AppendLog::<SampleSnapshot>::map_mut(&p, Options::new(GB), ()).unwrap();
  basic_write_entry(l);

  let mut open_opts = OpenOptions::new();
  open_opts.read(true).create(true).append(true);
  let l = AppendLog::<SampleSnapshot>::map(&p, Options::new(GB), ()).unwrap();

  assert_eq!(l.snapshot().creations.len(), 10002);
}
