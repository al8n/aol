use std::fs::OpenOptions;

use among::Among;
use aol::{buffer::VacantBuffer, Entry, Record};

struct Sample {
  a: u64,
  data: Vec<u8>,
}

impl aol::Record for Sample {
  type Error = core::convert::Infallible;

  fn encoded_size(&self) -> usize {
    8 + 4 + self.data.len()
  }

  fn encode(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, Self::Error> {
    buf.put_u64_le_unchecked(self.a);
    let len = self.data.len() as u32;
    buf.put_u32_le_unchecked(len);
    buf.put_slice_unchecked(&self.data);
    Ok(12 + len as usize)
  }

  fn decode(buf: &[u8]) -> Result<(usize, Self), Self::Error> {
    let a = u64::from_le_bytes(buf[..8].try_into().unwrap());
    let len = u32::from_le_bytes(buf[8..12].try_into().unwrap());
    let data = buf[12..12 + len as usize].to_vec();
    Ok((12 + len as usize, Self { a, data }))
  }
}

struct SampleSnapshot {
  creations: Vec<Sample>,
  deletions: Vec<Sample>,
}

impl aol::Snapshot for SampleSnapshot {
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

  fn clear(&mut self) -> Result<(), Self::Error> {
    self.creations.clear();
    self.deletions.clear();
    Ok(())
  }
}

trait AppendLog {
  type Record: aol::Record;
  type Error;

  fn append(&mut self, entry: Entry<Self::Record>) -> Result<(), Self::Error>;

  fn append_batch(&mut self, entries: Vec<Entry<Self::Record>>) -> Result<(), Self::Error>;

  fn flush(&self) -> Result<(), Self::Error>;

  fn flush_async(&self) -> Result<(), Self::Error>;

  fn sync_all(&self) -> Result<(), Self::Error>;

  fn rewrite(&mut self) -> Result<(), Self::Error>;
}

impl<S: aol::Snapshot> AppendLog for aol::AppendLog<S> {
  type Record = S::Record;
  type Error = Among<<S::Record as Record>::Error, S::Error, aol::Error>;

  fn append(&mut self, entry: Entry<Self::Record>) -> Result<(), Self::Error> {
    aol::AppendLog::append(self, entry)
  }

  fn append_batch(&mut self, batch: Vec<Entry<Self::Record>>) -> Result<(), Self::Error> {
    aol::AppendLog::append_batch(self, batch)
  }

  fn flush(&self) -> Result<(), Self::Error> {
    aol::AppendLog::sync_data(self).map_err(|e| Among::Right(aol::Error::from(e)))
  }

  fn flush_async(&self) -> Result<(), Self::Error> {
    aol::AppendLog::sync_data(self).map_err(|e| Among::Right(aol::Error::from(e)))
  }

  fn sync_all(&self) -> Result<(), Self::Error> {
    aol::AppendLog::sync_all(self).map_err(|e| Among::Right(aol::Error::from(e)))
  }

  fn rewrite(&mut self) -> Result<(), Self::Error> {
    aol::AppendLog::rewrite(self)
  }
}

fn basic_write_entry<L: AppendLog<Record = Sample>>(mut l: L)
where
  L::Error: core::fmt::Debug,
{
  const N: usize = 5001;

  for i in 0..N {
    if i % 3 == 0 {
      l.append(Entry::creation(Sample {
        a: i as u64,
        data: Vec::new(),
      }))
      .unwrap();
      l.flush_async().unwrap();
    } else if i % 3 == 1 {
      l.append(Entry::deletion(Sample {
        a: i as u64,
        data: Vec::new(),
      }))
      .unwrap();
      l.flush().unwrap();
    } else {
      let mut batch = Vec::with_capacity(10);
      for j in 0..10 {
        if j % 2 == 0 {
          batch.push(Entry::creation(Sample {
            a: i as u64,
            data: Vec::new(),
          }));
        } else {
          batch.push(Entry::deletion(Sample {
            a: i as u64,
            data: Vec::new(),
          }));
        }
      }

      l.append_batch(batch).unwrap();
      l.sync_all().unwrap();
    }
  }
}

#[test]
fn test() {
  use aol::EntryFlags;

  let creation = EntryFlags::creation();
  let deletion = EntryFlags::deletion();
  println!("{:?}", creation);
  println!("{:?}", deletion);

  println!("{}", creation.custom_flag());
}

#[test]
#[cfg_attr(miri, ignore)]
fn file_basic() {
  use aol::{AppendLog, Options};

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("fs.log");
  let l = AppendLog::<SampleSnapshot>::open(&p, (), Options::new()).unwrap();
  #[cfg(feature = "filelock")]
  l.lock_exclusive().unwrap();
  basic_write_entry(l);

  let mut open_opts = OpenOptions::new();
  open_opts.read(true).create(true).append(true);
  let l = AppendLog::<SampleSnapshot>::open(&p, (), Options::new()).unwrap();
  #[cfg(feature = "filelock")]
  l.lock_shared().unwrap();
  assert_eq!(l.snapshot().creations.len(), 10002);
  #[cfg(feature = "filelock")]
  l.unlock().unwrap();
}

#[test]
#[cfg_attr(miri, ignore)]
fn file_write_large_entry() {
  use aol::{AppendLog, Options};

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("fs_write_large.log");
  let mut l = AppendLog::<SampleSnapshot>::open(&p, (), Options::new()).unwrap();
  #[cfg(feature = "filelock")]
  l.lock_exclusive().unwrap();

  const N: usize = 50;

  for i in 0..N {
    if i % 4 == 0 {
      l.append(Entry::creation(Sample {
        a: i as u64,
        data: vec![0; 128],
      }))
      .unwrap();
      l.flush_async().unwrap();
    } else if i % 4 == 1 {
      l.append(Entry::deletion(Sample {
        a: i as u64,
        data: vec![0; 128],
      }))
      .unwrap();
      l.flush().unwrap();
    } else if i % 4 == 2 {
      let mut batch = Vec::with_capacity(10);
      for j in 0..10 {
        if j % 2 == 0 {
          batch.push(Entry::creation(Sample {
            a: i as u64,
            data: vec![0; 128],
          }));
        } else {
          batch.push(Entry::deletion(Sample {
            a: i as u64,
            data: vec![0; 128],
          }));
        }
      }

      l.append_batch(batch).unwrap();
      l.sync_all().unwrap();
    } else {
      let batch = [
        Entry::creation(Sample {
          a: i as u64,
          data: Vec::new(),
        }),
        Entry::deletion(Sample {
          a: i as u64,
          data: Vec::new(),
        }),
      ];

      l.append_batch(batch).unwrap();
      l.sync_all().unwrap();
    }
  }

  l.append_batch(vec![]).unwrap();
  l.append_batch([]).unwrap();

  drop(l);

  let mut open_opts = OpenOptions::new();
  open_opts.read(true).create(true).append(true);
  let _l = AppendLog::<SampleSnapshot>::open(&p, (), Options::new()).unwrap();
  #[cfg(feature = "filelock")]
  _l.lock_shared().unwrap();
  #[cfg(feature = "filelock")]
  _l.unlock().unwrap();
}

fn rewrite<L: AppendLog<Record = Sample>>(l: &mut L)
where
  L::Error: core::fmt::Debug,
{
  const N: usize = 200;
  for i in 0..N {
    if i % 2 == 1 && i < 50 {
      l.append(Entry::deletion(Sample {
        a: i as u64,
        data: Vec::new(),
      }))
      .unwrap();
      continue;
    }

    l.append(Entry::creation(Sample {
      a: i as u64,
      data: Vec::new(),
    }))
    .unwrap();
    l.flush_async().unwrap();
  }

  l.rewrite().unwrap();
}

#[test]
#[cfg_attr(miri, ignore)]
fn file_rewrite_policy_skip() {
  use aol::{AppendLog, Options};

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("fs_rewrite_policy_skip.log");
  let mut l = AppendLog::<SampleSnapshot>::open(
    &p,
    (),
    Options::new().with_rewrite_policy(aol::RewritePolicy::Skip(100)),
  )
  .unwrap();
  #[cfg(feature = "filelock")]
  l.try_lock_exclusive().unwrap();
  rewrite(&mut l);

  let mut l =
    AppendLog::<SampleSnapshot>::open(&p, (), Options::new().with_read_only(true)).unwrap();
  #[cfg(feature = "filelock")]
  l.try_lock_shared().unwrap();
  assert_eq!(l.snapshot().creations.len(), 75);
  #[cfg(feature = "filelock")]
  l.unlock().unwrap();
  assert!(l.rewrite().is_err());
}

#[test]
#[cfg_attr(miri, ignore)]
fn file_rewrite() {
  use aol::{AppendLog, Options};

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("fs_rewrite.log");
  let mut l = AppendLog::<SampleSnapshot>::open(&p, (), Options::new()).unwrap();
  #[cfg(feature = "filelock")]
  l.try_lock_exclusive().unwrap();
  rewrite(&mut l);

  let mut l =
    AppendLog::<SampleSnapshot>::open(&p, (), Options::new().with_read_only(true)).unwrap();
  #[cfg(feature = "filelock")]
  l.try_lock_shared().unwrap();
  assert_eq!(l.snapshot().creations.len(), 175);
  #[cfg(feature = "filelock")]
  l.unlock().unwrap();
  assert!(l.rewrite().is_err());
}
