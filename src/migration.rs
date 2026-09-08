use std::fs;
use std::path::{Path, PathBuf};

use crate::pure::{self, MigrationId, ParseError, StrictOrderError};
use crate::{Error, Result};

pub use pure::{MigrationStatus, Version};

impl std::fmt::Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl AsRef<str> for Version {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl From<&str> for Version {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<String> for Version {
    fn from(s: String) -> Self {
        Self(s)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MigrationFile {
    pub version: Version,
    pub name: String,
    pub path: PathBuf,
    pub up: String,
    pub down: String,
}

impl MigrationFile {
    pub fn label(&self) -> String {
        format!("{}_{}", self.version, self.name)
    }

    fn id(&self) -> MigrationId {
        MigrationId {
            version: self.version.clone(),
            name: self.name.clone(),
        }
    }
}

fn map_parse(err: ParseError, filename: &str) -> Error {
    match err {
        ParseError::Extension => Error::MigrationExtension(filename.to_string()),
        ParseError::Filename => Error::MigrationFilename(filename.to_string()),
        ParseError::VersionDigits => Error::MigrationVersionDigits(filename.to_string()),
        ParseError::Name => Error::MigrationName(filename.to_string()),
        ParseError::Markers => Error::MigrationMarkers,
    }
}

pub fn parse_version_name(filename: &str) -> Result<(Version, String)> {
    pure::parse_version_name(filename).map_err(|e| map_parse(e, filename))
}

pub fn parse_migration(path: &Path) -> Result<MigrationFile> {
    let filename = path
        .file_name()
        .and_then(|s| s.to_str())
        .ok_or_else(|| Error::msg("invalid migration filename"))?;
    let (version, name) = parse_version_name(filename)?;
    let text = fs::read_to_string(path)?;
    let (up, down) = split_up_down(&text)?;
    Ok(MigrationFile {
        version,
        name,
        path: path.to_path_buf(),
        up,
        down,
    })
}

/// Split migration file text into `(up, down)` bodies (no TypeDB I/O).
pub fn parse_migration_body(text: &str) -> Result<(String, String)> {
    split_up_down(text)
}

fn split_up_down(text: &str) -> Result<(String, String)> {
    pure::split_up_down(text).map_err(|e| map_parse(e, ""))
}

pub fn list_migration_files(dir: &Path) -> Result<Vec<MigrationFile>> {
    if !dir.exists() {
        return Ok(Vec::new());
    }
    let mut files = Vec::new();
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("tql") {
            continue;
        }
        files.push(parse_migration(&path)?);
    }
    files.sort_by(|a, b| a.version.cmp(&b.version));
    for i in 1..files.len() {
        if files[i].version == files[i - 1].version {
            return Err(Error::DuplicateVersion(files[i].version.clone()));
        }
    }
    Ok(files)
}

pub fn status_rows(
    files: &[MigrationFile],
    applied: &[Version],
) -> Vec<(MigrationFile, MigrationStatus)> {
    let ids: Vec<MigrationId> = files.iter().map(|f| f.id()).collect();
    let statuses = pure::status_rows(&ids, applied);
    files
        .iter()
        .cloned()
        .zip(statuses.into_iter().map(|(_, s)| s))
        .collect()
}

pub fn check_strict_order(files: &[MigrationFile], applied: &[Version]) -> Result<()> {
    let ids: Vec<MigrationId> = files.iter().map(|f| f.id()).collect();
    match pure::check_strict_order(&ids, applied) {
        Ok(()) => Ok(()),
        Err(StrictOrderError::OutOfOrder {
            pending,
            applied_up_to,
        }) => Err(Error::StrictOrder {
            pending,
            applied_up_to,
        }),
    }
}

pub fn new_migration_path(dir: &Path, name: &str) -> PathBuf {
    let slug = slugify(name);
    let ts = chrono::Utc::now().format("%Y%m%d%H%M%S");
    dir.join(format!("{ts}_{slug}.tql"))
}

pub fn migration_template() -> &'static str {
    "-- migrate:up\n\n\n-- migrate:down\n\n"
}

pub fn slugify(name: &str) -> String {
    pure::slugify(name)
}
