use std::fs;
use std::path::{Path, PathBuf};

use crate::pure::{self, MigrationId, ParseError, StrictOrderError};
use crate::{Error, Result};

pub use pure::{MigrationStatus, Version};

/// One printed row from `status` (dbmate v2.38: files plus applied-without-file).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatusLine {
    /// Migration file present: Applied (`[X]`) or Pending (`[ ]`).
    File {
        file: MigrationFile,
        status: MigrationStatus,
    },
    /// Recorded in the ledger but no matching migration file (`[?]`).
    MissingFile { version: Version },
}

impl StatusLine {
    pub fn version(&self) -> &Version {
        match self {
            StatusLine::File { file, .. } => &file.version,
            StatusLine::MissingFile { version } => version,
        }
    }

    pub fn display_text(&self) -> String {
        match self {
            StatusLine::File { file, status } => {
                let mark = match status {
                    MigrationStatus::Applied => "[X]",
                    MigrationStatus::Pending => "[ ]",
                };
                format!("{mark} {}", file.label())
            }
            StatusLine::MissingFile { version } => {
                format!("[?] {} (file not found)", version.as_str())
            }
        }
    }
}

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
    /// Ordered `(up, down)` sections (dbmate multi-section).
    pub sections: Vec<(String, String)>,
}

impl MigrationFile {
    pub fn label(&self) -> String {
        format!("{}_{}", self.version, self.name)
    }

    /// First section up body (single-section files; ledger helpers).
    pub fn up(&self) -> &str {
        self.sections.first().map(|(u, _)| u.as_str()).unwrap_or("")
    }

    /// First section down body.
    pub fn down(&self) -> &str {
        self.sections.first().map(|(_, d)| d.as_str()).unwrap_or("")
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
        ParseError::SectionMissingDown => Error::MigrationSectionMissingDown,
        ParseError::SectionWrongOrder => Error::MigrationSectionWrongOrder,
        ParseError::SectionMultipleDown => Error::MigrationSectionMultipleDown,
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
    let bytes = fs::read(path)?;
    let text = decode_migration_bytes(&bytes)?;
    let sections = parse_sections(&text)?;
    Ok(MigrationFile {
        version,
        name,
        path: path.to_path_buf(),
        sections,
    })
}

/// Decode migration file bytes as UTF-8, ignoring a leading UTF-8 BOM (dbmate v2.38).
///
/// UTF-16 / UTF-32 files get a clear conversion error instead of a generic parse failure.
fn decode_migration_bytes(bytes: &[u8]) -> Result<String> {
    let bytes = strip_utf8_bom_bytes(bytes);
    match std::str::from_utf8(bytes) {
        Ok(s) => Ok(s.to_string()),
        Err(_) => {
            if let Some(enc) = detect_unsupported_encoding(bytes) {
                return Err(Error::msg(format!(
                    "migration missing -- migrate:up / -- migrate:down (file appears to be {enc}, convert it to UTF-8)"
                )));
            }
            Err(Error::msg(
                "migration file is not valid UTF-8; save it as UTF-8 (dbmate/tqlmate do not accept UTF-16 or UTF-32)",
            ))
        }
    }
}

fn strip_utf8_bom_bytes(bytes: &[u8]) -> &[u8] {
    if bytes.len() >= 3 && bytes[0] == 0xef && bytes[1] == 0xbb && bytes[2] == 0xbf {
        &bytes[3..]
    } else {
        bytes
    }
}

/// Guess UTF-16/UTF-32 when a file is not valid UTF-8 (dbmate `detectUnsupportedEncoding`).
fn detect_unsupported_encoding(bytes: &[u8]) -> Option<&'static str> {
    let is_ascii = |c: u8| c != 0 && c < 0x80;
    if bytes.starts_with(&[0xff, 0xfe, 0x00, 0x00]) {
        return Some("UTF-32LE with a byte order mark");
    }
    if bytes.starts_with(&[0x00, 0x00, 0xfe, 0xff]) {
        return Some("UTF-32BE with a byte order mark");
    }
    if bytes.starts_with(&[0xff, 0xfe]) {
        return Some("UTF-16LE with a byte order mark");
    }
    if bytes.starts_with(&[0xfe, 0xff]) {
        return Some("UTF-16BE with a byte order mark");
    }
    if bytes.len() >= 4 && is_ascii(bytes[0]) && bytes[1..4] == [0, 0, 0] {
        return Some("UTF-32LE without a byte order mark");
    }
    if bytes.len() >= 4 && bytes[0..3] == [0, 0, 0] && is_ascii(bytes[3]) {
        return Some("UTF-32BE without a byte order mark");
    }
    if bytes.len() >= 2 && is_ascii(bytes[0]) && bytes[1] == 0 {
        return Some("UTF-16LE without a byte order mark");
    }
    if bytes.len() >= 2 && bytes[0] == 0 && is_ascii(bytes[1]) {
        return Some("UTF-16BE without a byte order mark");
    }
    None
}

/// Split migration file text into `(up, down)` bodies (no TypeDB I/O).
///
/// Single-section / legacy concat API. Prefer [`parse_migration_sections`] for
/// multi-section files.
pub fn parse_migration_body(text: &str) -> Result<(String, String)> {
    pure::split_up_down(text).map_err(|e| map_parse(e, ""))
}

/// Parse ordered `(up, down)` sections (dbmate v2.37 multi-section semantics).
pub fn parse_migration_sections(text: &str) -> Result<Vec<(String, String)>> {
    parse_sections(text)
}

fn parse_sections(text: &str) -> Result<Vec<(String, String)>> {
    let text = strip_utf8_bom_str(text);
    let sections = pure::parse_sections(text).map_err(|e| {
        if matches!(e, ParseError::Markers) {
            if let Some(enc) = detect_unsupported_encoding(text.as_bytes()) {
                return Error::msg(format!(
                    "migration missing -- migrate:up / -- migrate:down (file appears to be {enc}, convert it to UTF-8)"
                ));
            }
        }
        map_parse(e, "")
    })?;
    Ok(sections.into_iter().map(|s| (s.up, s.down)).collect())
}

fn strip_utf8_bom_str(text: &str) -> &str {
    text.strip_prefix('\u{feff}').unwrap_or(text)
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

/// Applied ledger versions that have no matching migration file (sorted).
pub fn applied_without_files(files: &[MigrationFile], applied: &[Version]) -> Vec<Version> {
    let mut missing = Vec::new();
    for v in applied {
        if !files.iter().any(|f| f.version == *v) {
            missing.push(v.clone());
        }
    }
    missing
}

/// File rows plus `[?]` missing-file rows, sorted by version (dbmate v2.38 `status`).
pub fn status_lines(files: &[MigrationFile], applied: &[Version]) -> Vec<StatusLine> {
    let mut lines: Vec<StatusLine> = status_rows(files, applied)
        .into_iter()
        .map(|(file, status)| StatusLine::File { file, status })
        .collect();
    for version in applied_without_files(files, applied) {
        lines.push(StatusLine::MissingFile { version });
    }
    lines.sort_by(|a, b| a.version().cmp(b.version()));
    lines
}

/// `status --strict`: fail when any applied version has no migration file.
pub fn check_missing_applied_files(files: &[MigrationFile], applied: &[Version]) -> Result<()> {
    let missing = applied_without_files(files, applied);
    if missing.is_empty() {
        return Ok(());
    }
    let kind = if missing.len() == 1 {
        "migration"
    } else {
        "migrations"
    };
    let versions = missing
        .iter()
        .map(|v| v.as_str())
        .collect::<Vec<_>>()
        .join("`, `");
    Err(Error::MissingAppliedMigrationFile { kind, versions })
}

/// Whether the highest applied version has a matching migration file.
pub fn latest_applied_has_file(files: &[MigrationFile], applied: &[Version]) -> bool {
    match applied.last() {
        None => true,
        Some(v) => files.iter().any(|f| f.version == *v),
    }
}

/// Applied list ending at the latest version that still has a file (dbmate non-strict rollback).
pub fn applied_for_rollback(files: &[MigrationFile], applied: &[Version]) -> Vec<Version> {
    let mut last_with_file = None;
    for (i, v) in applied.iter().enumerate() {
        if files.iter().any(|f| f.version == *v) {
            last_with_file = Some(i);
        }
    }
    match last_with_file {
        Some(i) => applied[..=i].to_vec(),
        None => applied.to_vec(),
    }
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
