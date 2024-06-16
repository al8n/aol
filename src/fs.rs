use std::{
  fs::{File, OpenOptions},
  io::{self, BufReader, Read, Write},
  path::PathBuf,
};

use super::{error::Error, *};

const CURRENT_VERSION: u16 = 0;

/// Generic append-only log implementation based on [`std::fs::File`].
///
/// File structure:
///
/// ```text
/// +----------------------+--------------------------+-----------------------+
/// | magic text (4 bytes) | external magic (2 bytes) | magic (2 bytes)       |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// | op (1 bit)           | custom flag (7 bits)     | len (4 bytes)         | data (n bytes)        | checksum (4 bytes)    |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// | op (1 bit)           | custom flag (7 bits)     | len (4 bytes)         | data (n bytes)        | checksum (4 bytes)    |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// | ...                  | ...                      | ...                   | ...                   | ...                   |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// ```
#[derive(Debug)]
pub struct AppendLog<M, C = Crc32> {
  opts: Options,
  filename: PathBuf,
  rewrite_filename: PathBuf,
  file: Option<File>,
  len: u64,
  manifest: M,
  _checksumer: core::marker::PhantomData<C>,
}

impl<M, C> AppendLog<M, C> {
  /// Returns the options of the manifest file.
  #[inline]
  pub const fn options(&self) -> &Options {
    &self.opts
  }

  /// Returns the current manifest.
  #[inline]
  pub const fn manifest(&self) -> &M {
    &self.manifest
  }
}

impl<M: Manifest, C> AppendLog<M, C> {
  /// Flush the manifest file.
  #[inline]
  pub fn flush(&mut self) -> Result<(), Error<io::Error, M>> {
    // unwrap is ok, because this log cannot be used in concurrent environment
    self.file.as_mut().unwrap().flush().map_err(Error::io)
  }

  /// Sync the manifest file.
  #[inline]
  pub fn sync_all(&self) -> Result<(), Error<io::Error, M>> {
    // unwrap is ok, because this log cannot be used in concurrent environment
    self.file.as_ref().unwrap().sync_all().map_err(Error::io)
  }
}

impl<M: Manifest, C: Checksumer> AppendLog<M, C> {
  /// Open and replay the manifest file.
  #[cfg(feature = "std")]
  #[inline]
  pub fn open<P: AsRef<std::path::Path>>(
    path: P,
    manifest_opts: M::Options,
    file_opts: OpenOptions,
    opts: Options,
  ) -> Result<Self, Error<io::Error, M>> {
    let existing = path.as_ref().exists();
    let path = path.as_ref();
    let mut rewrite_path = path.to_path_buf();
    rewrite_path.set_extension("rewrite");
    let file = file_opts.open(path).map_err(Error::io)?;
    Self::open_in(
      path.to_path_buf(),
      rewrite_path,
      file,
      existing,
      opts,
      manifest_opts,
    )
  }

  /// Returns the path to the append-only file.
  #[inline]
  pub fn path(&self) -> &std::path::Path {
    &self.filename
  }

  /// Append an entry to the append-only file.
  #[inline]
  pub fn append(&mut self, ent: Entry<M::Data>) -> Result<(), Error<io::Error, M>> {
    self.append_in(ent)
  }

  /// Append a batch of entries to the append-only file.
  pub fn append_batch(&mut self, entries: Vec<Entry<M::Data>>) -> Result<(), Error<io::Error, M>> {
    if self.manifest.should_rewrite(self.len) {
      self.rewrite()?;
    }

    let total_encoded_size = entries
      .iter()
      .map(|ent| ent.data.encoded_size())
      .sum::<usize>()
      + entries.len() * FIXED_MANIFEST_ENTRY_SIZE;

    macro_rules! encode_batch {
      ($buf:ident) => {{
        let mut cursor = 0;
        for ent in entries {
          cursor += ent
            .encode::<C>(ent.data.encoded_size(), &mut $buf[cursor..])
            .map_err(Error::data)?;
        }
      }};
    }

    // unwrap is ok, because this log cannot be used in concurrent environment
    let file = self.file.as_mut().unwrap();

    if total_encoded_size > MAX_INLINE_SIZE {
      let mut buf = std::vec![0; total_encoded_size];
      encode_batch!(buf);
      file
        .write_all(&buf)
        .and_then(|_| {
          self.len += total_encoded_size as u64;
          if self.opts.sync_on_write {
            file.flush()
          } else {
            Ok(())
          }
        })
        .map_err(Error::io)
    } else {
      let mut buf = [0; MAX_INLINE_SIZE];
      let buf = &mut buf[..total_encoded_size];
      encode_batch!(buf);
      
      file
        .write_all(buf)
        .and_then(|_| {
          self.len += total_encoded_size as u64;
          if self.opts.sync_on_write {
            file.flush()
          } else {
            Ok(())
          }
        })
        .map_err(Error::io)
    }
  }

  fn open_in(
    filename: PathBuf,
    rewrite_filename: PathBuf,
    mut file: File,
    existing: bool,
    opts: Options,
    manifest_opts: M::Options,
  ) -> Result<Self, Error<io::Error, M>> {
    let Options { magic_version, .. } = opts;

    if !existing {
      Self::write_header(&mut file, magic_version)?;

      let len = file.metadata().map_err(Error::io)?.len();
      return Ok(Self {
        filename,
        rewrite_filename,
        file: Some(file),
        manifest: M::open(manifest_opts).map_err(Error::manifest)?,
        _checksumer: core::marker::PhantomData,
        opts,
        len,
      });
    }

    let size = file.metadata().map_err(Error::io)?.len();

    let mut header = [0; MANIFEST_HEADER_SIZE];

    let mut file = BufReader::new(file);
    file.read_exact(&mut header).map_err(Error::io)?;

    if &header[..MAGIC_TEXT_LEN] != MAGIC_TEXT {
      return Err(Error::BadMagicText);
    }

    let external = u16::from_le_bytes(
      header[MAGIC_TEXT_LEN..MAGIC_TEXT_LEN + MAGIC_VERSION_LEN]
        .try_into()
        .unwrap(),
    );
    if external != magic_version {
      return Err(Error::BadExternalMagic {
        expected: magic_version,
        found: external,
      });
    }

    let version = u16::from_le_bytes(
      header[MAGIC_TEXT_LEN + MAGIC_VERSION_LEN..MANIFEST_HEADER_SIZE]
        .try_into()
        .unwrap(),
    );
    if version != CURRENT_VERSION {
      return Err(Error::BadMagic {
        expected: CURRENT_VERSION,
        found: version,
      });
    }

    let mut manifest = M::open(manifest_opts).map_err(Error::manifest)?;

    let mut curosr = 0;
    loop {
      let mut header_buf = [0; ENTRY_HEADER_SIZE];
      match file.read_exact(&mut header_buf) {
        Ok(()) => {
          curosr += ENTRY_HEADER_SIZE;

          let len = u32::from_le_bytes(header_buf[1..].try_into().unwrap()) as usize;
          let entry_size = FIXED_MANIFEST_ENTRY_SIZE + len;

          let remaining = size - MANIFEST_HEADER_SIZE as u64 - curosr as u64;
          let needed = len + CHECKSUM_SIZE;
          if needed as u64 > remaining {
            return Err(Error::entry_corrupted(needed as u32, remaining as u32));
          }

          if entry_size > MAX_INLINE_SIZE {
            let mut buf = std::vec![0; entry_size];
            buf[..ENTRY_HEADER_SIZE].copy_from_slice(&header_buf);
            file
              .read_exact(&mut buf[ENTRY_HEADER_SIZE..])
              .map_err(Error::io)?;
            let ent = Entry::decode::<C>(&buf).map_err(|e| match e {
              Some(e) => Error::data(e),
              None => Error::ChecksumMismatch,
            })?;
            manifest.insert(ent).map_err(Error::manifest)?;
          } else {
            let mut buf = [0; MAX_INLINE_SIZE];
            buf[..ENTRY_HEADER_SIZE].copy_from_slice(&header_buf);
            let buf = &mut buf
              [ENTRY_HEADER_SIZE..ENTRY_HEADER_SIZE + len + CHECKSUM_SIZE];
            file.read_exact(buf).map_err(Error::io)?;
            let ent = Entry::decode::<C>(buf).map_err(|e| match e {
              Some(e) => Error::data(e),
              None => Error::ChecksumMismatch,
            })?;
            manifest.insert(ent).map_err(Error::manifest)?;
          }
          curosr += len + CHECKSUM_SIZE;
        }
        Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => break,
        Err(e) => return Err(Error::io(e)),
      }
    }

    let mut this = Self {
      filename,
      rewrite_filename,
      file: Some(file.into_inner()),
      manifest,
      len: size,
      _checksumer: core::marker::PhantomData,
      opts,
    };

    if this.manifest.should_rewrite(this.len) {
      return this.rewrite().map(|_| this);
    }

    Ok(this)
  }

  #[inline]
  fn write_header(file: &mut File, magic_version: u16) -> Result<(), Error<io::Error, M>> {
    let mut buf = [0; MANIFEST_HEADER_SIZE];
    let mut cur = 0;
    buf[..MAGIC_TEXT_LEN].copy_from_slice(MAGIC_TEXT);
    cur += MAGIC_TEXT_LEN;
    buf[cur..cur + MAGIC_VERSION_LEN].copy_from_slice(&magic_version.to_le_bytes());
    cur += MAGIC_VERSION_LEN;
    buf[cur..MANIFEST_HEADER_SIZE].copy_from_slice(&CURRENT_VERSION.to_le_bytes());
    file.write_all(&buf).map_err(Error::io)?;
    file.flush().map_err(Error::io)
  }

  #[inline]
  fn append_in(&mut self, entry: Entry<M::Data>) -> Result<(), Error<io::Error, M>> {
    if self.manifest.should_rewrite(self.len) {
      self.rewrite()?;
    }

    // unwrap is ok, because this log cannot be used in concurrent environment
    append::<M, C>(self.file.as_mut().unwrap(), &entry, self.opts.sync_on_write)
      .and_then(|len| {
        self.len += len as u64;
        self.manifest.insert(entry).map_err(Error::manifest)
      })
  }

  fn rewrite(&mut self) -> Result<(), Error<io::Error, M>> {
    thread_local! {
      static REWRITE_FILE_NAME: core::cell::RefCell<Option<std::path::PathBuf>> = core::cell::RefCell::new(None);
    }

    let manifest_opts = self.manifest.options().clone();
    let manifest = M::open(manifest_opts).map_err(Error::manifest)?;
    let old = mem::replace(&mut self.manifest, manifest);

    let _ = self.file.take().unwrap();

    let mut new_file = OpenOptions::new()
      .create(true)
      .read(true)
      .write(true)
      .truncate(true)
      .open(&self.rewrite_filename)
      .map_err(Error::io)?;

    Self::write_header(&mut new_file, self.opts.magic_version)?;

    for ent in old.into_iter() {
      if ent.flag.is_creation() {
        append::<M, C>(&mut new_file, &ent, false)
          .and_then(|_| self.manifest.insert(ent).map_err(Error::manifest))?;
      }
    }

    new_file.flush().map_err(Error::io)?;
    new_file.sync_all().map_err(Error::io)?;
    drop(new_file);
    std::fs::rename(&self.rewrite_filename, &self.filename).map_err(Error::io)?;

    let file = OpenOptions::new()
      .create(false)
      .read(true)
      .append(true)
      .open(&self.filename)
      .map_err(Error::io)?;
    self.file = Some(file);
    let len = self.file.as_ref().unwrap().metadata().map_err(Error::io)?.len();
    self.len = len;
    Ok(())
  }
}

fn append<M: Manifest, C: Checksumer>(
  file: &mut File,
  ent: &Entry<M::Data>,
  sync: bool,
) -> Result<usize, Error<io::Error, M>> {
  let encoded_len = ent.data.encoded_size();
  if encoded_len + FIXED_MANIFEST_ENTRY_SIZE > MAX_INLINE_SIZE {
    let mut buf = Vec::with_capacity(encoded_len + FIXED_MANIFEST_ENTRY_SIZE);
    ent
      .encode::<C>(encoded_len, &mut buf)
      .map_err(Error::data)?;
    let len = buf.len();
    file
      .write_all(&buf)
      .and_then(|_| if sync { file.flush().map(|_| len) } else { Ok(len) })
      .map_err(Error::io)
  } else {
    let mut buf = [0; MAX_INLINE_SIZE];
    let buf = &mut buf[..encoded_len + FIXED_MANIFEST_ENTRY_SIZE];
    ent.encode::<C>(encoded_len, buf).map_err(Error::data)?;
    let len = buf.len();
    file
      .write_all(buf)
      .and_then(|_| if sync { file.flush().map(|_| len) } else { Ok(len) })
      .map_err(Error::io)
  }
}
