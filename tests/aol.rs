use std::convert::Infallible;

use among::Among;
use aol::{buffer::VacantBuffer, Entry, MaybeEntryRef, Record, RecordRef};
use either::Either;
use smallvec_wrapper::{LargeVec, MediumVec, OneOrMore, SmallVec, TinyVec, XLargeVec, XXLargeVec, XXXLargeVec};

#[derive(Debug)]
struct Sample {
  a: u64,
  record: Vec<u8>,
}

#[derive(Debug)]
struct SampleRef<'a> {
  a: u64,
  record: &'a [u8],
}

impl<'a> RecordRef<'a> for SampleRef<'a> {
  type Error = Infallible;

  fn decode(buf: &'a [u8]) -> Result<(usize, Self), Self::Error> {
    let a = u64::from_le_bytes(buf[..8].try_into().unwrap());
    let len = u32::from_le_bytes(buf[8..12].try_into().unwrap());
    let record = &buf[12..12 + len as usize];
    Ok((12 + len as usize, Self { a, record }))
  }
}

impl aol::Record for Sample {
  type Error = Infallible;
  type Ref<'a> = SampleRef<'a>;

  fn encoded_size(&self) -> usize {
    8 + 4 + self.record.len()
  }

  fn encode(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, Self::Error> {
    buf.put_u64_le_unchecked(self.a);
    let len = self.record.len() as u32;
    buf.put_u32_le_unchecked(len);
    buf.put_slice_unchecked(&self.record);
    Ok(12 + len as usize)
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

  fn validate(&self, _entry: &Entry<Self::Record>) -> Result<(), Either<Infallible, Self::Error>> {
    Ok(())
  }

  fn contains(&self, entry: &Entry<<Self::Record as Record>::Ref<'_>>) -> bool {
    let flag = entry.flag();
    if !flag.is_creation() {
      return false;
    }
    true
  }

  fn insert(&mut self, entry: MaybeEntryRef<'_, Self::Record>) {
    match entry.into_inner() {
      Either::Left(entry) => {
        let r = entry.record();
        if entry.flag().is_creation() {
          self.creations.push(Sample {
            a: r.a,
            record: r.record.to_vec(),
          });
        } else {
          self.deletions.push(Sample {
            a: r.a,
            record: r.record.to_vec(),
          });
        }
      }
      Either::Right(entry) => {
        let r = entry.record();
        if entry.flag().is_creation() {
          self.creations.push(Sample {
            a: r.a,
            record: r.record.to_vec(),
          });
        } else {
          self.deletions.push(Sample {
            a: r.a,
            record: r.record.to_vec(),
          });
        }
      }
    }
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
        record: Vec::new(),
      }))
      .unwrap();
      l.flush_async().unwrap();
    } else if i % 3 == 1 {
      l.append(Entry::deletion(Sample {
        a: i as u64,
        record: Vec::new(),
      }))
      .unwrap();
      l.flush().unwrap();
    } else {
      let mut batch = Vec::with_capacity(10);
      for j in 0..10 {
        if j % 2 == 0 {
          batch.push(Entry::creation(Sample {
            a: i as u64,
            record: Vec::new(),
          }));
        } else {
          batch.push(Entry::deletion(Sample {
            a: i as u64,
            record: Vec::new(),
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
  use aol::Builder;

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("fs.log");

  let l = Builder::<SampleSnapshot>::default()
    .with_create_new(true)
    .with_read(true)
    .with_write(true)
    .build(&p)
    .unwrap();

  #[cfg(feature = "filelock")]
  l.lock_exclusive().unwrap();
  basic_write_entry(l);

  let l = Builder::<SampleSnapshot>::default()
    .with_create(true)
    .with_read(true)
    .with_append(true)
    .build(&p)
    .unwrap();
  #[cfg(feature = "filelock")]
  l.lock_shared().unwrap();
  assert_eq!(l.snapshot().creations.len(), 10002);
  #[cfg(feature = "filelock")]
  l.unlock().unwrap();
}

#[test]
#[cfg_attr(miri, ignore)]
fn file_write_large_entry() {
  use aol::Builder;

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("fs_write_large.log");
  let mut l = Builder::<SampleSnapshot>::default()
    .with_create_new(true)
    .with_read(true)
    .with_append(true)
    .build(&p)
    .unwrap();
  #[cfg(feature = "filelock")]
  l.lock_exclusive().unwrap();

  const N: usize = 50;

  for i in 0..N {
    if i % 4 == 0 {
      l.append(Entry::creation(Sample {
        a: i as u64,
        record: vec![0; 128],
      }))
      .unwrap();
      l.flush_async().unwrap();
    } else if i % 4 == 1 {
      l.append(Entry::deletion(Sample {
        a: i as u64,
        record: vec![0; 128],
      }))
      .unwrap();
      l.flush().unwrap();
    } else if i % 4 == 2 {
      let mut batch = Vec::with_capacity(10);
      for j in 0..10 {
        if j % 2 == 0 {
          batch.push(Entry::creation(Sample {
            a: i as u64,
            record: vec![0; 128],
          }));
        } else {
          batch.push(Entry::deletion(Sample {
            a: i as u64,
            record: vec![0; 128],
          }));
        }
      }

      l.append_batch(batch).unwrap();
      l.sync_all().unwrap();
    } else {
      let batch = [
        Entry::creation(Sample {
          a: i as u64,
          record: Vec::new(),
        }),
        Entry::deletion(Sample {
          a: i as u64,
          record: Vec::new(),
        }),
      ];

      l.append_batch(batch).unwrap();
      l.sync_all().unwrap();
    }
  }

  l.append_batch::<Entry<Sample>, _>(vec![]).unwrap();
  l.append_batch::<Entry<Sample>, _>(OneOrMore::new()).unwrap(); 
  l.append_batch::<Entry<Sample>, _>(TinyVec::new()).unwrap();
  l.append_batch::<Entry<Sample>, _>(SmallVec::new()).unwrap();
  l.append_batch::<Entry<Sample>, _>(MediumVec::new()).unwrap();
  l.append_batch::<Entry<Sample>, _>(LargeVec::new()).unwrap();
  l.append_batch::<Entry<Sample>, _>(XLargeVec::new()).unwrap();
  l.append_batch::<Entry<Sample>, _>(XXLargeVec::new()).unwrap();
  l.append_batch::<Entry<Sample>, _>(XXXLargeVec::new()).unwrap();
  l.append_batch::<Entry<Sample>, _>([]).unwrap();

  drop(l);

  let mut l = Builder::<SampleSnapshot>::default()
    .with_create(true)
    .with_read(true)
    .with_append(true)
    .build(&p)
    .unwrap();
  #[cfg(feature = "filelock")]
  l.lock_shared().unwrap();
  #[cfg(feature = "filelock")]
  l.unlock().unwrap();

  l.append_batch(SmallVec::from_iter(
    [Entry::creation(Sample {
      a: 0,
      record: vec![0; 128],
    }),
    Entry::deletion(Sample {
      a: 0,
      record: vec![0; 128],
    })],
  )).unwrap();
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
        record: Vec::new(),
      }))
      .unwrap();
      continue;
    }

    l.append(Entry::creation(Sample {
      a: i as u64,
      record: Vec::new(),
    }))
    .unwrap();
    l.flush_async().unwrap();
  }

  l.rewrite().unwrap();
}

#[test]
#[cfg_attr(miri, ignore)]
fn file_rewrite_policy_skip() {
  use aol::Builder;

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("fs_rewrite_policy_skip.log");
  let mut l = Builder::<SampleSnapshot>::default()
    .with_create_new(true)
    .with_read(true)
    .with_append(true)
    .with_rewrite_policy(aol::RewritePolicy::Skip(100))
    .build(&p)
    .unwrap();

  #[cfg(feature = "filelock")]
  l.try_lock_exclusive().unwrap();
  rewrite(&mut l);

  let mut l = Builder::<SampleSnapshot>::default()
    .with_snapshot_options::<SampleSnapshot>(())
    .with_read(true)
    .with_read_only(true)
    .build(&p)
    .unwrap();

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
  use aol::Builder;

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("fs_rewrite.log");
  let mut l = Builder::<SampleSnapshot>::default()
    .with_create_new(true)
    .with_read(true)
    .with_append(true)
    .build(&p)
    .unwrap();
  #[cfg(feature = "filelock")]
  l.try_lock_exclusive().unwrap();
  rewrite(&mut l);

  let mut l = Builder::<SampleSnapshot>::default()
    .with_read(true)
    .with_read_only(true)
    .build(&p)
    .unwrap();
  #[cfg(feature = "filelock")]
  l.try_lock_shared().unwrap();
  assert_eq!(l.snapshot().creations.len(), 175);
  #[cfg(feature = "filelock")]
  l.unlock().unwrap();
  assert!(l.rewrite().is_err());
}
