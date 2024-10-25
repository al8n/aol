use core::mem;
use std::{
  borrow::Borrow,
  cmp::Reverse,
  collections::{BTreeMap, HashSet},
};

use aol::{
  AppendLog, Batch, Builder, CustomFlags, Entry, EntryFlags, MaybeEntryRef, Record, RecordRef,
};
use dbutils::{
  buffer::VacantBuffer,
  error::{IncompleteBuffer, InsufficientBuffer},
};

use among::Among;
use aol::Error;
use derive_more::{AsRef, Deref, From, Into};
use either::Either;
use smallvec_wrapper::LargeVec;
use smol_str::SmolStr;

/// An error that occurs when manipulating the manifest file.
#[derive(Debug, From, Into, Deref, AsRef)]
struct ManifestFileError(Among<ManifestRecordError, ManifestError, Error>);

impl From<ManifestRecordError> for ManifestFileError {
  #[inline]
  fn from(e: ManifestRecordError) -> Self {
    Self(Among::Left(e))
  }
}

impl From<ManifestError> for ManifestFileError {
  #[inline]
  fn from(e: ManifestError) -> Self {
    Self(Among::Middle(e))
  }
}

impl From<Error> for ManifestFileError {
  #[inline]
  fn from(e: Error) -> Self {
    Self(Among::Right(e))
  }
}

impl core::fmt::Display for ManifestFileError {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match &self.0 {
      Among::Left(e) => e.fmt(f),
      Among::Middle(e) => e.fmt(f),
      Among::Right(e) => e.fmt(f),
    }
  }
}

impl core::error::Error for ManifestFileError {}

/// An error that occurs when manipulating the manifest.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
enum ManifestError {
  /// Table not found.
  #[error("table {0} does not exist")]
  TableNotFound(u16),
  /// Table already exists.
  #[error("table {0} already exists")]
  TableAlreadyExists(SmolStr),
  /// Returned when trying to create or delete the default table.
  #[error("cannot create or delete the default table")]
  ReservedTable,
  /// Table name is too long.
  #[error("table name is too long: the maximum length is 255 bytes, but got {0}")]
  LargeTableName(usize),
}

/// An error that occurs when manipulating the manifest record.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
enum ManifestRecordError {
  /// Buffer is too small to encode the manifest record.
  #[error("buffer is too small to encode header")]
  InsufficientBuffer(#[from] InsufficientBuffer),
  /// Not enough bytes to decode the value pointer.
  #[error("not enough bytes to decode record")]
  IncompleteBuffer(#[from] IncompleteBuffer),
  /// Returned when failed to decode a table name.
  #[error("failed to decode table name: {0}")]
  SmolStr(#[from] core::str::Utf8Error),
  /// Returned when decoding unknown manifest event.
  #[error("unknown manifest record type: {0}")]
  UnknownRecordType(#[from] UnknownManifestRecordType),
  /// Returned when there is an invalid entry flag.
  #[error("invalid entry flag: {0}")]
  InvalidEntryFlag(ManifestEntryFlags),
}

/// Unknown manifest event.
#[derive(Clone, Copy, Debug, thiserror::Error)]
#[error("unknown manifest record type: {0}")]
struct UnknownManifestRecordType(pub(crate) u8);

/// The manifest record.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
enum ManifestRecord {
  /// Log record.
  Log {
    /// File ID.
    fid: u32,
    /// Table ID.
    tid: u16,
  },
  /// Table record.
  Table {
    /// Table ID.
    id: u16,
    /// Table name.
    name: SmolStr,
  },
}

impl ManifestRecord {
  /// Creates a new log record.
  #[inline]
  const fn log(fid: u32, tid: u16) -> Self {
    Self::Log { fid, tid }
  }

  /// Creates a new table record.
  #[inline]
  const fn table(table_id: u16, name: SmolStr) -> Self {
    Self::Table { id: table_id, name }
  }
}

impl aol::Record for ManifestRecord {
  type Error = ManifestRecordError;
  type Ref<'a> = ManifestRecordRef<'a>;

  fn encoded_size(&self) -> usize {
    match self {
      Self::Log { .. } => 1 + mem::size_of::<u16>() + mem::size_of::<u32>(),
      Self::Table { name, .. } => 1 + mem::size_of::<u16>() + mem::size_of::<u8>() + name.len(),
    }
  }

  fn encode(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, Self::Error> {
    let encoded_len = self.encoded_size();
    let cap = buf.capacity();
    if cap < encoded_len {
      return Err(InsufficientBuffer::with_information(encoded_len as u64, cap as u64).into());
    }

    match self {
      Self::Log { fid, tid } => {
        let mut cur = 0;
        buf.put_u8(0)?;
        cur += 1;
        buf.put_u32_le(*fid)?;
        cur += 4;
        buf.put_u16_le(*tid)?;
        cur += 2;
        Ok(cur)
      }
      Self::Table { id, name } => {
        let mut cur = 0;
        buf.put_u8(1)?;
        cur += 1;
        buf.put_u16_le(*id)?;
        cur += 2;

        let remaining = buf.remaining();
        let want = 1 + name.len();
        if want > remaining {
          return Err(
            InsufficientBuffer::with_information((cur + want) as u64, (cur + remaining) as u64)
              .into(),
          );
        }

        buf.put_u8(name.len() as u8)?;
        cur += 1;
        buf.put_slice(name.as_bytes())?;
        cur += name.len();
        Ok(cur)
      }
    }
  }
}

/// A reference to the manifest record.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ManifestRecordRef<'a> {
  /// Log record.
  Log {
    /// File ID.
    fid: u32,
    /// Table ID.
    tid: u16,
  },
  /// Table record.
  Table {
    /// Table ID.
    id: u16,
    /// Table name.
    name: &'a str,
  },
}

impl ManifestRecordRef<'_> {
  fn to_owned(&self) -> ManifestRecord {
    match self {
      Self::Log { fid, tid } => ManifestRecord::log(*fid, *tid),
      Self::Table { id, name } => ManifestRecord::table(*id, SmolStr::from(*name)),
    }
  }
}

impl<'a> RecordRef<'a> for ManifestRecordRef<'a> {
  type Error = ManifestRecordError;

  fn decode(buf: &'a [u8]) -> Result<(usize, Self), Self::Error> {
    if buf.is_empty() {
      return Err(IncompleteBuffer::new().into());
    }

    let kind = buf[0];
    let mut cur = 1;
    Ok(match kind {
      0 => {
        let fid = u32::from_le_bytes((&buf[cur..cur + 4]).try_into().unwrap());
        cur += 4;
        let tid = u16::from_le_bytes((&buf[cur..cur + 2]).try_into().unwrap());
        cur += 2;

        (cur, Self::Log { fid, tid })
      }
      1 => {
        let id = u16::from_le_bytes((&buf[cur..cur + 2]).try_into().unwrap());

        cur += 2;
        let len = buf[cur] as usize;
        cur += 1;
        if buf.len() < cur + len {
          return Err(
            IncompleteBuffer::with_information((cur + len) as u64, buf.len() as u64).into(),
          );
        }

        let name = core::str::from_utf8(&buf[cur..cur + len])?;
        cur += len;
        (cur, Self::Table { id, name })
      }
      _ => {
        return Err(Self::Error::UnknownRecordType(UnknownManifestRecordType(
          kind,
        )))
      }
    })
  }
}

/// - The first bit of the manifest entry indicating it is a creation event or a deletion event.
///   - `0`: Creation event.
///   - `1`: Deletion event.
/// - The second bit of the manifest entry indicating it is a table event or not.
///   - `1`: Table event.
/// - The third bit of the manifest entry indicating it is a active log event or not.
///   - `1`: Active log event.
/// - The fourth bit of the manifest entry indicating it is a frozen log event or not.
///   - `1`: Frozen log event.
/// - The fifth bit of the manifest entry indicating it is a bloomfilter or not.
///   - `1`: Bloomfilter log event.
/// - The sixth bit of the manifest entry indicating it is a value log event or not.
///   - `1`: Value log event.
/// - The seventh and eighth bits are reserved for future use.
#[derive(Debug, Clone, Copy, Into, PartialEq, Eq, Hash)]
struct ManifestEntryFlags(EntryFlags);

impl core::fmt::Display for ManifestEntryFlags {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match () {
      _ if self.is_creation() && self.is_active_log() => write!(f, "create_active_log"),
      _ if self.is_creation() && self.is_frozen_log() => write!(f, "create_frozen_log"),
      _ if self.is_creation() && self.is_bloomfilter() => write!(f, "create_bloomfilter"),
      _ if self.is_creation() && self.is_value_log() => write!(f, "create_value_log"),
      _ if self.is_creation() && self.is_table() => write!(f, "create_table"),
      _ if self.is_deletion() && self.is_active_log() => write!(f, "delete_active_log"),
      _ if self.is_deletion() && self.is_frozen_log() => write!(f, "delete_frozen_log"),
      _ if self.is_deletion() && self.is_bloomfilter() => write!(f, "delete_bloomfilter"),
      _ if self.is_deletion() && self.is_value_log() => write!(f, "delete_value_log"),
      _ if self.is_deletion() && self.is_table() => write!(f, "delete_table"),
      _ => unreachable!(),
    }
  }
}

macro_rules! manifest_entry_flags_constructors {
  ($($idx:literal: $name:ident $($log:ident)?), +$(,)?) => {
    paste::paste! {
      const POSSIBLE_FLAGS: &[u8] = &[
        $(
          Self::[< create_ $name $(_ $log)?>]().bits(),
          Self::[< delete_ $name $(_ $log)?>]().bits(),
        )*
      ];
    }

    $(
      paste::paste! {
        #[doc = "Returns a flag indicating it is a creation event for " $name $(" " $log)? "."]
        #[inline]
        const fn [< create_ $name $(_$log)? >]() -> Self {
          Self(EntryFlags::creation_with_custom_flag(CustomFlags::empty().[< with_bit $idx>]()))
        }

        #[doc = "Returns a flag indicating it is a deletion event for " $name $(" " $log)? "."]
        #[inline]
        const fn [< delete_ $name $(_$log)? >]() -> Self {
          Self(EntryFlags::deletion_with_custom_flag(CustomFlags::empty().[< with_bit $idx>]()))
        }

        /// Returns `true` if the flag is a table event.
        #[doc = "Returns `true` if the flag is a " $name $(" " $log)? " event."]
        #[inline]
        const fn [< is_ $name $(_$log)? >](&self) -> bool {
          self.0.custom_flag().[< bit $idx >]()
        }
      }
    )*
  };
}

impl ManifestEntryFlags {
  // Order is important here, as we are using binary search to check if the flag is possible.
  manifest_entry_flags_constructors!(
    1: table,
    2: active log,
    3: frozen log,
    4: bloomfilter,
    5: value log
  );

  #[inline]
  fn is_possible_flag(bits: u8) -> bool {
    Self::POSSIBLE_FLAGS.binary_search(&bits).is_ok()
  }

  /// Returns `true` if the flag is a creation event.
  #[inline]
  const fn is_creation(&self) -> bool {
    self.0.is_creation()
  }

  /// Returns `true` if the flag is a deletion event.
  #[inline]
  const fn is_deletion(&self) -> bool {
    self.0.is_deletion()
  }

  /// Returns the flag in the form of a `u8`.
  #[inline]
  const fn bits(&self) -> u8 {
    self.0.bits()
  }
}

/// An entry in the manifest log.
#[derive(Debug, Into, AsRef, Clone)]
struct ManifestEntry(Entry<ManifestRecord>);

macro_rules! manifest_entry_constructors {
  ($($name: ident $($log:ident)?), +$(,)?) => {
    $(
      paste::paste! {
        #[doc = "Returns an instance which indicates a creation event for " $name $(" " $log)? "."]
        ///
        /// ## Example
        ///
        /// ```rust
        /// use lemondb_core::manifest::ManifestEntry;
        ///
        #[doc = "let entry = ManifestEntry::create_" $name $("_" $log)? "(Default::default(), Default::default());"]
        /// assert!(entry.flag().is_creation());
        /// ```
        #[inline]
        const fn [< create_ $name $("_" $log)?>](fid: u32, tid: u16) -> Self {
          Self(Entry::with_flags(ManifestEntryFlags::[< create_ $name $(_ $log)?>]().0, ManifestRecord::log(fid, tid)))
        }

        #[doc = "Returns an instance which indicates a deletion event for " $name $(" " $log)? "."]
        ///
        /// ## Example
        ///
        /// ```rust
        /// use lemondb_core::manifest::ManifestEntry;
        ///
        #[doc = "let entry = ManifestEntry::delete_" $name $("_" $log)? "(Default::default(), Default::default());"]
        /// assert!(entry.flag().is_deletion());
        /// ```
        #[inline]
        const fn [< delete_ $name $("_" $log)?>](fid: u32, tid: u16) -> Self {
          Self(Entry::with_flags(ManifestEntryFlags::[< delete_ $name $(_ $log)?>]().0, ManifestRecord::log(fid, tid)))
        }
      }
    )*
  };
}

impl ManifestEntry {
  /// Returns an instance which indicates a creation event for a table.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use lemondb_core::manifest::ManifestEntry;
  ///
  /// let entry = ManifestEntry::create_table(Default::default(), Default::default());
  /// assert!(entry.flag().is_creation());
  /// ```
  #[inline]
  const fn create_table(id: u16, name: SmolStr) -> Self {
    Self(Entry::with_flags(
      ManifestEntryFlags::create_table().0,
      ManifestRecord::table(id, name),
    ))
  }

  /// Returns an instance which indicates a deletion event for a table.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use lemondb_core::manifest::ManifestEntry;
  ///
  /// let entry = ManifestEntry::delete_table(Default::default(), Default::default());
  /// assert!(entry.flag().is_deletion());
  /// ```
  #[inline]
  const fn delete_table(id: u16, name: SmolStr) -> Self {
    Self(Entry::with_flags(
      ManifestEntryFlags::delete_table().0,
      ManifestRecord::table(id, name),
    ))
  }

  manifest_entry_constructors!(
    active log,
    frozen log,
    bloomfilter,
    value log,
  );
}

const MANIFEST_DELETIONS_RATIO: usize = 10;
const MANIFEST_DELETIONS_REWRITE_THRESHOLD: usize = 10000;
const DEFAULT_TABLE_NAME: &str = "default";

/// The options for opening a manifest file.
#[viewit::viewit(getters(style = "move"), setters(prefix = "with"))]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ManifestOptions {
  /// The version of the lemon manifest file. Default is `0`.
  #[viewit(
    getter(const, attrs(doc = "Returns the version of the manifest file.")),
    setter(attrs(doc = "Sets the version of the manifest file."))
  )]
  version: u16,
  /// The rewrite threshold for the manifest file. Default is `10000`.
  #[viewit(
    getter(
      const,
      attrs(doc = "Returns the rewrite threshold for the manifest file.")
    ),
    setter(attrs(doc = "Sets the rewrite threshold for the manifest file."))
  )]
  rewrite_threshold: usize,
}

impl Default for ManifestOptions {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl ManifestOptions {
  /// Creates a new manifest options with the default values.
  #[inline]
  const fn new() -> Self {
    Self {
      version: 0,
      rewrite_threshold: MANIFEST_DELETIONS_REWRITE_THRESHOLD,
    }
  }
}

impl aol::Snapshot for Manifest {
  type Record = ManifestRecord;

  type Options = ManifestOptions;

  type Error = ManifestError;

  fn new(opts: Self::Options) -> Result<Self, Self::Error> {
    Ok(Self {
      tables: BTreeMap::new(),
      last_fid: 0,
      last_table_id: 0,
      creations: 0,
      deletions: 0,
      opts,
    })
  }

  fn should_rewrite(&self, _size: u64) -> bool {
    self.deletions > self.opts.rewrite_threshold
      && self.deletions > MANIFEST_DELETIONS_RATIO * self.creations.saturating_sub(self.deletions)
  }

  fn contains(&self, entry: &Entry<ManifestRecordRef<'_>>) -> bool {
    let flag = ManifestEntryFlags(entry.flag());
    if flag.is_creation() {
      match entry.record() {
        ManifestRecordRef::Table { id, .. } => {
          // if the table is in remove state, we should not consider it as existing
          // so even this is a creation entry, we should return false.
          return self.tables.contains_key(&Reverse(*id));
        }
        ManifestRecordRef::Log { tid, fid } => {
          // if the table is in remove state, we should not consider it as existing
          // so even this is a creation entry, we should return false.
          let Some(t) = self.tables.get(&Reverse(*tid)) else {
            return false;
          };

          match () {
            _ if flag.is_active_log() => {
              return t.active_logs.contains(fid);
            }
            _ if flag.is_frozen_log() => {
              return t.frozen_logs.contains(fid);
            }
            _ if flag.is_bloomfilter() => {
              return t.bloomfilters.contains(fid);
            }
            _ if flag.is_value_log() => {
              return t.vlogs.contains(fid);
            }
            _ => unreachable!(),
          }
        }
      }
    }

    false
  }

  fn validate(
    &self,
    entry: &Entry<Self::Record>,
  ) -> Result<(), Either<<Self::Record as Record>::Error, Self::Error>> {
    let flag = entry.flag();

    if !ManifestEntryFlags::is_possible_flag(flag.bits()) {
      return Err(Either::Left(ManifestRecordError::InvalidEntryFlag(
        ManifestEntryFlags(flag),
      )));
    }

    match entry.record() {
      ManifestRecord::Table { id, name } => {
        if name.eq(DEFAULT_TABLE_NAME) {
          return Err(Either::Right(ManifestError::ReservedTable));
        }

        if name.len() > 255 {
          return Err(Either::Right(ManifestError::LargeTableName(name.len())));
        }

        if flag.is_creation() {
          for table in self.tables.values() {
            if table.name.eq(name) && !table.is_removed() {
              return Err(Either::Right(ManifestError::TableAlreadyExists(
                name.clone(),
              )));
            }
          }

          Ok(())
        } else {
          if let Some(table) = self.tables.get(&Reverse(*id)) {
            if table.name.eq(name) {
              return Ok(());
            }
          }

          Err(Either::Right(ManifestError::TableNotFound(*id)))
        }
      }
      ManifestRecord::Log { tid, .. } => {
        if !self.tables.contains_key(&Reverse(*tid)) && 0.ne(tid)
        // we do not create the default table, but default table is always valid
        {
          return Err(Either::Right(ManifestError::TableNotFound(*tid)));
        }

        Ok(())
      }
    }
  }

  fn validate_batch<I, B>(
    &self,
    entries: &B,
  ) -> Result<(), Either<<Self::Record as Record>::Error, Self::Error>>
  where
    B: Batch<I, Self::Record>,
    I: AsRef<Entry<Self::Record>> + Into<Entry<Self::Record>>,
  {
    let mut new_tables = LargeVec::<(u16, &SmolStr)>::new();

    for ent in entries.iter() {
      let entry = ent.as_ref();
      let flag = ManifestEntryFlags(entry.flag());

      if !ManifestEntryFlags::is_possible_flag(flag.bits()) {
        return Err(Either::Left(ManifestRecordError::InvalidEntryFlag(flag)));
      }

      match entry.record() {
        ManifestRecord::Table { id, name } => {
          if name.eq(DEFAULT_TABLE_NAME) {
            return Err(Either::Right(ManifestError::ReservedTable));
          }

          if name.len() > 255 {
            return Err(Either::Right(ManifestError::LargeTableName(name.len())));
          }

          let iter =
            <&LargeVec<_> as core::iter::IntoIterator>::into_iter(&new_tables).map(|(_, n)| *n);
          if flag.is_creation() {
            for table in self.tables.values().map(|t| &t.name).chain(iter) {
              if table.eq(name) {
                return Err(Either::Right(ManifestError::TableAlreadyExists(
                  name.clone(),
                )));
              }
            }

            new_tables.push((*id, name));
            new_tables.sort_unstable_by_key(|&(id, _)| id);
          } else {
            if let Some(table) = self.tables.get(&Reverse(*id)) {
              if table.name.eq(name) {
                continue;
              }
            }

            if let Ok(idx) = new_tables.binary_search_by_key(id, |&(id, _)| id) {
              let (_, old_name) = new_tables[idx];
              if old_name.eq(name) {
                new_tables.remove(idx);
              }
            }

            return Err(Either::Right(ManifestError::TableNotFound(*id)));
          }
        }
        ManifestRecord::Log { tid, .. } => {
          if !self.tables.contains_key(&Reverse(*tid))
            && new_tables.binary_search_by_key(tid, |&(id, _)| id).is_err()
            && 0.ne(tid)
          // we do not create the default table, but default table is always valid
          {
            return Err(Either::Right(ManifestError::TableNotFound(*tid)));
          }
        }
      }
    }

    Ok(())
  }

  #[inline]
  fn insert(&mut self, entry: MaybeEntryRef<'_, Self::Record>) {
    let entry = match entry.into_inner() {
      Either::Left(entry) => entry.map(|r| r.to_owned()),
      Either::Right(entry) => entry,
    };
    self.insert_in(entry)
  }

  fn clear(&mut self) -> Result<(), Self::Error> {
    self.tables.clear();
    self.last_fid = 0;
    self.creations = 0;
    self.deletions = 0;
    Ok(())
  }
}

/// The table manifest.
#[derive(Debug)]
struct TableManifest {
  name: SmolStr,
  id: u16,
  removed: bool,
  vlogs: HashSet<u32>,
  active_logs: HashSet<u32>,
  frozen_logs: HashSet<u32>,
  bloomfilters: HashSet<u32>,
}

impl TableManifest {
  /// Returns the table id.
  #[inline]
  fn id(&self) -> u16 {
    self.id
  }

  /// Returns the table name.
  #[inline]
  fn name(&self) -> &SmolStr {
    &self.name
  }

  /// Returns the value logs id.
  #[inline]
  fn value_logs(&self) -> &HashSet<u32> {
    &self.vlogs
  }

  /// Returns the active logs id.
  #[inline]
  fn active_logs(&self) -> &HashSet<u32> {
    &self.active_logs
  }

  /// Returns the frozen logs id.
  #[inline]
  fn frozen_logs(&self) -> &HashSet<u32> {
    &self.frozen_logs
  }

  /// Returns the bloomfilters id.
  #[inline]
  fn bloomfilters(&self) -> &HashSet<u32> {
    &self.bloomfilters
  }

  #[inline]
  fn new(id: u16, name: SmolStr) -> Self {
    Self {
      name,
      id,
      vlogs: HashSet::new(),
      active_logs: HashSet::new(),
      frozen_logs: HashSet::new(),
      bloomfilters: HashSet::new(),
      removed: false,
    }
  }

  /// Returns `true` if the table is marked as removed.
  #[inline]
  const fn is_removed(&self) -> bool {
    self.removed
  }
}

/// The in-memory snapshot of the manifest file.
#[derive(Debug, Default)]
struct Manifest {
  tables: BTreeMap<Reverse<u16>, TableManifest>,
  last_fid: u32,
  last_table_id: u16,

  // Contains total number of creation and deletion changes in the manifest -- used to compute
  // whether it'd be useful to rewrite the manifest.
  creations: usize,
  deletions: usize,

  opts: ManifestOptions,
}

impl Manifest {
  /// Returns the table with the given ID.
  #[inline]
  fn get_table<Q>(&self, name: &Q) -> Option<&TableManifest>
  where
    SmolStr: Borrow<Q>,
    Q: ?Sized + Ord,
  {
    self
      .tables
      .values()
      .find(|table| table.name.borrow().eq(name))
  }

  /// Returns all the tables
  #[inline]
  fn tables(&self) -> &BTreeMap<Reverse<u16>, TableManifest> {
    &self.tables
  }

  fn insert_in(&mut self, entry: aol::Entry<ManifestRecord>) {
    let flag = ManifestEntryFlags(entry.flag());
    let record = entry.into_record();

    match record {
      ManifestRecord::Log { fid, tid } => {
        if let Some(table) = self.tables.get_mut(&Reverse(tid)) {
          if flag.is_creation() {
            match () {
              _ if flag.is_active_log() => table.active_logs.insert(fid),
              _ if flag.is_frozen_log() => table.frozen_logs.insert(fid),
              _ if flag.is_bloomfilter() => table.bloomfilters.insert(fid),
              _ if flag.is_value_log() => table.vlogs.insert(fid),
              _ => unreachable!(),
            };
            self.creations += 1;
          } else {
            match () {
              _ if flag.is_active_log() => table.active_logs.remove(&fid),
              _ if flag.is_frozen_log() => table.frozen_logs.remove(&fid),
              _ if flag.is_bloomfilter() => table.bloomfilters.remove(&fid),
              _ if flag.is_value_log() => table.vlogs.remove(&fid),
              _ => unreachable!(),
            };
            self.deletions += 1;
          }
        }
      }
      ManifestRecord::Table { id, name } => {
        if flag.is_creation() {
          self.last_table_id = self.last_table_id.max(id);
          self
            .tables
            .insert(Reverse(id), TableManifest::new(id, name));
          self.creations += 1;
        } else {
          self.deletions += 1;
          self.tables.remove(&Reverse(id));
        }
      }
    }
  }
}

fn open_manifest_file<P: AsRef<std::path::Path>>(
  dir: P,
  opts: ManifestOptions,
) -> AppendLog<Manifest> {
  let path = dir.as_ref().join("MANIFEST");
  Builder::new(opts)
    .with_create(true)
    .with_append(true)
    .with_read(true)
    .build(&path)
    .unwrap()
}

#[cfg_attr(test, test)]
#[cfg_attr(miri, ignore)]
fn main() {
  let dir = tempfile::tempdir().unwrap();
  let mut file = open_manifest_file(
    dir.path(),
    ManifestOptions::new().with_rewrite_threshold(1000),
  );

  let fid = 0;
  let tid = 0;

  // Test empty manifest.
  assert!(file.snapshot().tables().is_empty());

  // Mock the database behavior, first create a table, when a table is created
  // a new active log and value log are also created.
  file
    .append_batch([
      ManifestEntry::create_table(tid, "foo".into()),
      ManifestEntry::create_active_log(fid, tid),
      ManifestEntry::create_value_log(fid, tid),
    ])
    .unwrap();

  {
    let manifest = file.snapshot();
    assert_eq!(manifest.tables().len(), 1);

    let table = manifest.get_table("foo").unwrap();
    assert_eq!(table.id(), tid);
    assert_eq!(table.name(), "foo");
    assert!(table.active_logs().contains(&fid));
    assert!(table.value_logs().contains(&fid));
    assert!(table.frozen_logs().is_empty());
    assert!(table.bloomfilters().is_empty());
  }

  // after some time, the active log is frozen and a new active log is created
  file
    .append_batch([
      ManifestEntry::create_frozen_log(fid, tid),
      ManifestEntry::create_bloomfilter(fid, tid),
      ManifestEntry::create_active_log(fid + 1, tid),
    ])
    .unwrap();

  {
    let manifest = file.snapshot();
    assert_eq!(manifest.tables().len(), 1);

    let table = manifest.get_table("foo").unwrap();
    assert_eq!(table.id(), tid);
    assert_eq!(table.name(), "foo");

    let active_logs = table.active_logs();
    assert_eq!(active_logs.len(), 2);
    assert!(active_logs.contains(&(fid + 1)));
    assert!(active_logs.contains(&fid));
    assert!(table.value_logs().contains(&fid));
    assert!(table.frozen_logs().contains(&fid));
    assert!(table.bloomfilters().contains(&fid));
  }

  // after some time, the last reference to the old active log is dropped, then we need to remove
  // the old active log.
  file
    .append(ManifestEntry::delete_active_log(fid, tid).into())
    .unwrap();

  {
    let manifest = file.snapshot();
    assert_eq!(manifest.tables().len(), 1);

    let table = manifest.get_table("foo").unwrap();
    assert_eq!(table.id(), tid);
    assert_eq!(table.name(), "foo");

    let active_logs = table.active_logs();
    assert_eq!(active_logs.len(), 1);
    assert!(!active_logs.contains(&fid));
    assert!(active_logs.contains(&(fid + 1)));
    assert!(table.value_logs().contains(&fid));
    assert!(table.frozen_logs().contains(&fid));
    assert!(table.bloomfilters().contains(&fid));
  }

  // after some time, the frozen log and bloomfilter for fid(0) is garbage collected.
  file
    .append_batch([
      ManifestEntry::delete_frozen_log(fid, tid),
      ManifestEntry::delete_bloomfilter(fid, tid),
    ])
    .unwrap();

  {
    let manifest = file.snapshot();
    assert_eq!(manifest.tables().len(), 1);

    let table = manifest.get_table("foo").unwrap();
    assert_eq!(table.id(), tid);
    assert_eq!(table.name(), "foo");

    let active_logs = table.active_logs();
    assert_eq!(active_logs.len(), 1);
    assert!(!active_logs.contains(&fid));
    assert!(active_logs.contains(&(fid + 1)));
    assert!(table.value_logs().contains(&fid));
    assert!(table.frozen_logs().is_empty());
    assert!(table.bloomfilters().is_empty());
  }

  // after some time, the current value log is full, we need a new one
  let new_vlog_id = fid + 2;
  file
    .append(ManifestEntry::create_value_log(new_vlog_id, tid).into())
    .unwrap();

  {
    let manifest = file.snapshot();
    assert_eq!(manifest.tables().len(), 1);

    let table = manifest.get_table("foo").unwrap();
    assert_eq!(table.id(), tid);
    assert_eq!(table.name(), "foo");

    let active_logs = table.active_logs();
    assert_eq!(active_logs.len(), 1);
    assert!(!active_logs.contains(&fid));
    assert!(active_logs.contains(&(fid + 1)));

    let value_logs = table.value_logs();
    assert!(value_logs.contains(&new_vlog_id));
    assert!(value_logs.contains(&fid));

    assert!(table.frozen_logs().is_empty());
    assert!(table.bloomfilters().is_empty());
  }

  // after some time, the old value log is garbage collected.
  file
    .append(ManifestEntry::delete_value_log(fid, tid).into())
    .unwrap();

  {
    let manifest = file.snapshot();
    assert_eq!(manifest.tables().len(), 1);

    let table = manifest.get_table("foo").unwrap();
    assert_eq!(table.id(), tid);
    assert_eq!(table.name(), "foo");

    let active_logs = table.active_logs();
    assert_eq!(active_logs.len(), 1);
    assert!(!active_logs.contains(&fid));
    assert!(active_logs.contains(&(fid + 1)));

    let value_logs = table.value_logs();
    assert!(value_logs.contains(&new_vlog_id));
    assert!(!value_logs.contains(&fid));

    assert!(table.frozen_logs().is_empty());
    assert!(table.bloomfilters().is_empty());
  }

  // after some time, we create a table
  file
    .append(ManifestEntry::create_table(tid + 1, "bar".into()).into())
    .unwrap();

  {
    let manifest = file.snapshot();
    assert_eq!(manifest.tables().len(), 2);
  }

  // after some time, we delete the table
  file
    .append(ManifestEntry::delete_table(tid + 1, "bar".into()).into())
    .unwrap();

  {
    let manifest = file.snapshot();
    assert_eq!(manifest.tables().len(), 1);
  }

  // Now let's test reopening the manifest file.
  drop(file);
  let mut file = open_manifest_file(
    dir.path(),
    ManifestOptions::new().with_rewrite_threshold(1000),
  );

  {
    let manifest = file.snapshot();
    assert_eq!(manifest.tables().len(), 1);

    let table = manifest.get_table("foo").unwrap();
    assert_eq!(table.id(), tid);
    assert_eq!(table.name(), "foo");

    let active_logs = table.active_logs();
    assert_eq!(active_logs.len(), 1);
    assert!(!active_logs.contains(&fid));
    assert!(active_logs.contains(&(fid + 1)));

    let value_logs = table.value_logs();
    assert!(value_logs.contains(&new_vlog_id));
    assert!(!value_logs.contains(&fid));

    assert!(table.frozen_logs().is_empty());
    assert!(table.bloomfilters().is_empty());
  }

  // Now let us test some bad behavior.

  // 1. try to append an entry with impossible flags
  let flag = ManifestEntryFlags(EntryFlags::creation_with_custom_flag(CustomFlags::all()));
  {
    let ent = ManifestEntry(Entry::with_flags(flag.0, ManifestRecord::log(fid, tid)));
    let ManifestRecordError::InvalidEntryFlag(err) =
      file.append(ent.clone().into()).unwrap_err().unwrap_left()
    else {
      panic!("wrong error")
    };
    assert_eq!(flag, err);

    let ManifestRecordError::InvalidEntryFlag(err) =
      file.append_batch([ent]).unwrap_err().unwrap_left()
    else {
      panic!("wrong error")
    };
    assert_eq!(flag, err);
  }

  // 2. try to create a default table
  {
    let ent = ManifestEntry::create_table(tid, SmolStr::from("default"));
    let ManifestError::ReservedTable = file.append(ent.clone().into()).unwrap_err().unwrap_middle()
    else {
      panic!("wrong error")
    };

    let ManifestError::ReservedTable = file.append_batch([ent]).unwrap_err().unwrap_middle() else {
      panic!("wrong error")
    };
  }

  // Now let us trigger the rewrite
  for i in 10..1510u32 {
    file
      .append(ManifestEntry::delete_active_log(i, 0).into())
      .unwrap();
  }

  {
    let manifest = file.snapshot();
    assert_eq!(manifest.tables().len(), 1, "{:?}", manifest.tables());

    let table = manifest.get_table("foo").unwrap();
    assert_eq!(table.id(), tid);
    assert_eq!(table.name(), "foo");

    let active_logs = table.active_logs();
    assert_eq!(active_logs.len(), 1);
    assert!(!active_logs.contains(&fid));
    assert!(active_logs.contains(&(fid + 1)));

    let value_logs = table.value_logs();
    assert!(value_logs.contains(&new_vlog_id));
    assert!(!value_logs.contains(&fid));

    assert!(table.frozen_logs().is_empty());
    assert!(table.bloomfilters().is_empty());
  }

  drop(file);
  let file = open_manifest_file(
    dir.path(),
    ManifestOptions::new().with_rewrite_threshold(1000),
  );

  {
    let manifest = file.snapshot();
    assert_eq!(manifest.tables().len(), 1, "{:?}", manifest.tables());

    let table = manifest.get_table("foo").unwrap();
    assert_eq!(table.id(), tid);
    assert_eq!(table.name(), "foo");

    let active_logs = table.active_logs();
    assert_eq!(active_logs.len(), 1);
    assert!(!active_logs.contains(&fid));
    assert!(active_logs.contains(&(fid + 1)));

    let value_logs = table.value_logs();
    assert!(value_logs.contains(&new_vlog_id));
    assert!(!value_logs.contains(&fid));

    assert!(table.frozen_logs().is_empty());
    assert!(table.bloomfilters().is_empty());
  }
}
