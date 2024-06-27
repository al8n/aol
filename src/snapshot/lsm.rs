use super::*;

#[cfg(feature = "std")]
use std::collections::{HashMap, HashSet};

#[cfg(not(feature = "std"))]
use hashbrown::{HashMap, HashSet};

const TABLE_ID_SIZE: usize = mem::size_of::<u64>();
const LEVEL_SIZE: usize = mem::size_of::<u8>();

/// Error for [`Snapshot`].
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

/// Snapshot represents the contents of the MANIFEST file in a store.
///
/// The MANIFEST file describes the startup state of the db -- all LSM files and what level they're
/// at.
///
/// It consists of a sequence of [`SnapshotChange`] objects. Each of these is treated atomically,
/// and contains a sequence of SnapshotChange's (file creations/deletions) which we use to
/// reconstruct the append-only at startup.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Snapshot<D> {
  levels: Vec<LevelSnapshot>,
  tables: HashMap<u64, TableSnapshot<D>>,

  creations: u64,
  deletions: u64,
}

impl<D> Default for Snapshot<D> {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl<D> Snapshot<D> {
  /// Returns a new append-only.
  #[inline]
  pub fn new() -> Self {
    Self {
      levels: Vec::new(),
      tables: HashMap::new(),
      creations: 0,
      deletions: 0,
    }
  }

  /// Returns the levels in the append-only.
  #[inline]
  pub fn levels(&self) -> &[LevelSnapshot] {
    &self.levels
  }

  /// Returns the tables in the append-only.
  #[inline]
  pub fn tables(&self) -> &HashMap<u64, TableSnapshot<D>> {
    &self.tables
  }
}

impl<D: Data> super::Snapshot for Snapshot<D> {
  type Data = SnapshotChange<D>;

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
            TableSnapshot {
              level: entry.data.level,
              data: entry.data.data,
            },
          );
          while self.levels.len() <= entry.data.level as usize {
            self.levels.push(LevelSnapshot {
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
      data: SnapshotChange {
        id,
        level: table.level,
        data: table.data,
      },
      flag: EntryFlags::creation(),
    })
  }

  fn deletions(&self) -> u64 {
    self.deletions
  }

  fn creations(&self) -> u64 {
    self.creations
  }
}

/// Represents a change in the append-only.
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SnapshotChange<D> {
  id: u64,
  level: u8,
  data: D,
}

impl<D> SnapshotChange<D> {
  /// Creates a new append-only change.
  #[inline]
  pub const fn new(id: u64, level: u8, data: D) -> Self {
    Self { id, level, data }
  }

  /// Returns the id of the table.
  #[inline]
  pub const fn id(&self) -> u64 {
    self.id
  }

  /// Returns the level of the table.
  #[inline]
  pub const fn level(&self) -> u8 {
    self.level
  }

  /// Returns the data of the table.
  #[inline]
  pub const fn data(&self) -> &D {
    &self.data
  }
}

impl<D: Data> Data for SnapshotChange<D> {
  type Error = D::Error;

  fn encoded_size(&self) -> usize {
    TABLE_ID_SIZE + LEVEL_SIZE + self.data.encoded_size()
  }

  fn encode(&self, buf: &mut [u8]) -> Result<usize, Self::Error> {
    assert!(buf.len() >= self.encoded_size());

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
#[derive(Default, Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct LevelSnapshot {
  /// Set of table id's
  tables: HashSet<u64>,
}

impl LevelSnapshot {
  /// Returns the tables in the level.
  #[inline]
  pub fn tables(&self) -> &HashSet<u64> {
    &self.tables
  }
}

/// Contains information about a specific table
/// in the LSM tree.
#[derive(Default, Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TableSnapshot<D> {
  /// Level of the table
  level: u8,
  data: D,
}

impl<D> TableSnapshot<D> {
  /// Returns the level of the table.
  #[inline]
  pub const fn level(&self) -> u8 {
    self.level
  }

  /// Returns the data of the table.
  #[inline]
  pub const fn data(&self) -> &D {
    &self.data
  }
}
