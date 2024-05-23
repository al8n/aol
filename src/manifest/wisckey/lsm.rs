use crate::{CustomFlags, Data, Entry, EntryFlags};

use super::*;

use core::mem;
#[cfg(feature = "std")]
use std::collections::HashMap;

#[cfg(not(feature = "std"))]
use hashbrown::HashMap;

/// Error for [`Manifest`].
#[derive(Debug)]
pub enum Error {
  /// The table already exists.
  TableAlreadyExists(u64),
  /// The table does not exist.
  TableNotFound(u64),
}

impl core::fmt::Display for Error {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::TableAlreadyExists(id) => write!(f, "table {} already exists", id),
      Self::TableNotFound(id) => write!(f, "removes non-existing table {}", id),
    }
  }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

/// Manifest represents the contents of the MANIFEST file in a Badger store.
///
/// The MANIFEST file describes the startup state of the db -- all LSM files and what level they're
/// at.
///
/// It consists of a sequence of ManifestChangeSet objects.  Each of these is treated atomically,
/// and contains a sequence of ManifestChange's (file creations/deletions) which we use to
/// reconstruct the manifest at startup.
pub struct Manifest<D> {
  levels: Vec<LevelManifest>,
  tables: HashMap<u64, TableManifest<D>>,

  creations: u64,
  deletions: u64,
}

impl<D> Default for Manifest<D> {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl<D> Manifest<D> {
  /// Returns a new manifest.
  #[inline]
  pub fn new() -> Self {
    Self {
      levels: Vec::new(),
      tables: HashMap::new(),
      creations: 0,
      deletions: 0,
    }
  }

  /// Returns the levels in the manifest.
  #[inline]
  pub fn levels(&self) -> &[LevelManifest] {
    &self.levels
  }

  /// Returns the tables in the manifest.
  #[inline]
  pub fn tables(&self) -> &HashMap<u64, TableManifest<D>> {
    &self.tables
  }
}

impl<D: Data> crate::Manifest for Manifest<D> {
  type Data = ManifestChange<D>;

  type Error = Error;

  fn insert(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error> {
    if entry.flag().is_deletion() {
      match self.tables.remove(&entry.data.id) {
        None => Err(Error::TableNotFound(entry.data.id)),
        Some(old) => {
          self.levels[old.level as usize]
            .tables
            .remove(&entry.data.id);
          self.deletions += 1;
          Ok(())
        }
      }
    } else {
      match self.tables.get(&entry.data.id) {
        Some(_) => Err(Error::TableAlreadyExists(entry.data.id)),
        None => {
          self.tables.insert(
            entry.data.id,
            TableManifest {
              level: entry.data.level,
              data: entry.data.data,
            },
          );
          while self.levels.len() <= entry.data.level as usize {
            self.levels.push(LevelManifest {
              tables: HashSet::new(),
            });
          }
          self.levels[entry.data.level as usize]
            .tables
            .insert(entry.data.id);
          self.creations += 1;
          Ok(())
        }
      }
    }
  }

  fn into_iter(self) -> impl Iterator<Item = Entry<Self::Data>> {
    self.tables.into_iter().map(|(id, table)| Entry {
      fid: id as u32,
      data: ManifestChange {
        id,
        level: table.level,
        data: table.data,
      },
      flag: EntryFlags::creation(CustomFlags::empty()),
    })
  }

  fn deletions(&self) -> u64 {
    self.deletions
  }

  fn creations(&self) -> u64 {
    self.creations
  }
}

// type ManifestChange struct {
// 	Id             uint64                   `protobuf:"varint,1,opt,name=Id,proto3" json:"Id,omitempty"`
// 	Op             ManifestChange_Operation `protobuf:"varint,2,opt,name=Op,proto3,enum=badgerpb4.ManifestChange_Operation" json:"Op,omitempty"`
// 	Level          uint32                   `protobuf:"varint,3,opt,name=Level,proto3" json:"Level,omitempty"`
// 	KeyId          uint64                   `protobuf:"varint,4,opt,name=key_id,json=keyId,proto3" json:"key_id,omitempty"`
// 	EncryptionAlgo EncryptionAlgo           `protobuf:"varint,5,opt,name=encryption_algo,json=encryptionAlgo,proto3,enum=badgerpb4.EncryptionAlgo" json:"encryption_algo,omitempty"`
// 	Compression    uint32                   `protobuf:"varint,6,opt,name=compression,proto3" json:"compression,omitempty"`
// }

const TABLE_ID_SIZE: usize = mem::size_of::<u64>();
const LEVEL_SIZE: usize = mem::size_of::<u8>();

pub struct ManifestChange<D> {
  id: u64,
  level: u8,
  data: D,
}

impl<D: Data> Data for ManifestChange<D> {
  const ENCODED_SIZE: usize = TABLE_ID_SIZE + LEVEL_SIZE + D::ENCODED_SIZE;

  type Error = D::Error;

  fn encode(&self, buf: &mut [u8]) -> Result<usize, Self::Error> {
    assert!(buf.len() >= Self::ENCODED_SIZE);

    let mut offset = 0;
    buf[offset..offset + TABLE_ID_SIZE].copy_from_slice(&self.id.to_le_bytes());
    offset += TABLE_ID_SIZE;
    buf[offset] = self.level;
    offset += LEVEL_SIZE;
    self
      .data
      .encode(&mut buf[offset..])
      .map(|write| offset + write)
  }

  fn decode(buf: &[u8]) -> Result<(usize, Self), Self::Error> {
    assert!(buf.len() >= Self::ENCODED_SIZE);

    let mut offset = 0;
    let id = u64::from_le_bytes(buf[offset..offset + TABLE_ID_SIZE].try_into().unwrap());
    offset += TABLE_ID_SIZE;
    let level = buf[offset];
    offset += LEVEL_SIZE;
    let (read, data) = D::decode(&buf[offset..])?;
    Ok((offset + read, Self { id, level, data }))
  }
}

/// Contains information about LSM tree levels
/// in the MANIFEST file.
pub struct LevelManifest {
  /// Set of table id's
  tables: HashSet<u64>,
}

/// Contains information about a specific table
/// in the LSM tree.
pub struct TableManifest<D> {
  /// Level of the table
  level: u8,
  data: D,
}
