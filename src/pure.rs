//! Pure migration / ledger helpers — no filesystem, async, or TypeDB.
//!
//! Written for Charon → Aeneas (Lean) extraction. Avoids `HashSet`, `Path`,
//! `thiserror`, and several `str` helpers (`strip_suffix`, `ends_with`,
//! `trim_matches`, `strip_prefix`) that Aeneas does not model yet.
//! Byte-range checks stay explicit (no `RangeInclusive::contains`) for the
//! same reason.

#![allow(dead_code)]
#![allow(clippy::manual_range_contains)]

/// Digit-only migration version string (lexicographic order = chronological timestamps).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Version(pub String);

impl Version {
    pub fn new(s: impl Into<String>) -> Self {
        Self(s.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Lightweight migration identity used by status / order checks (no paths).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MigrationId {
    pub version: Version,
    pub name: String,
}

impl MigrationId {
    pub fn label(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.version.0);
        out.push('_');
        out.push_str(&self.name);
        out
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MigrationStatus {
    Applied,
    Pending,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseError {
    Extension,
    Filename,
    VersionDigits,
    Name,
    Markers,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StrictOrderError {
    OutOfOrder {
        pending: Version,
        applied_up_to: Version,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Section {
    Up,
    Down,
}

fn has_suffix(s: &str, suffix: &str) -> bool {
    let sb = s.as_bytes();
    let suf = suffix.as_bytes();
    if sb.len() < suf.len() {
        return false;
    }
    let start = sb.len() - suf.len();
    let mut i = 0;
    while i < suf.len() {
        if sb[start + i] != suf[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn drop_suffix<'a>(s: &'a str, suffix: &str) -> Option<&'a str> {
    if has_suffix(s, suffix) {
        Some(&s[..s.len() - suffix.len()])
    } else {
        None
    }
}

fn has_prefix(s: &str, prefix: &str) -> bool {
    let sb = s.as_bytes();
    let pre = prefix.as_bytes();
    if sb.len() < pre.len() {
        return false;
    }
    let mut i = 0;
    while i < pre.len() {
        if sb[i] != pre[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn drop_prefix<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
    if has_prefix(s, prefix) {
        Some(&s[prefix.len()..])
    } else {
        None
    }
}

fn find_byte(s: &str, b: u8) -> Option<usize> {
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn split_once_char(s: &str, sep: u8) -> Option<(&str, &str)> {
    match find_byte(s, sep) {
        Some(i) => Some((&s[..i], &s[i + 1..])),
        None => None,
    }
}

fn trim_spaces(s: &str) -> &str {
    let bytes = s.as_bytes();
    let mut start = 0;
    while start < bytes.len() && (bytes[start] == b' ' || bytes[start] == b'\t') {
        start += 1;
    }
    let mut end = bytes.len();
    while end > start && (bytes[end - 1] == b' ' || bytes[end - 1] == b'\t') {
        end -= 1;
    }
    &s[start..end]
}

fn trim_underscores(s: &str) -> &str {
    let bytes = s.as_bytes();
    let mut start = 0;
    while start < bytes.len() && bytes[start] == b'_' {
        start += 1;
    }
    let mut end = bytes.len();
    while end > start && bytes[end - 1] == b'_' {
        end -= 1;
    }
    &s[start..end]
}

fn ends_with_underscore(s: &str) -> bool {
    let bytes = s.as_bytes();
    !bytes.is_empty() && bytes[bytes.len() - 1] == b'_'
}

fn ascii_lower(c: u8) -> u8 {
    if c >= b'A' && c <= b'Z' {
        c + 32
    } else {
        c
    }
}

fn eq_ignore_ascii_case(a: &str, b: &str) -> bool {
    let ab = a.as_bytes();
    let bb = b.as_bytes();
    if ab.len() != bb.len() {
        return false;
    }
    let mut i = 0;
    while i < ab.len() {
        if ascii_lower(ab[i]) != ascii_lower(bb[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn is_ascii_digit_byte(c: u8) -> bool {
    c >= b'0' && c <= b'9'
}

fn is_ascii_digits(s: &str) -> bool {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return false;
    }
    let mut i = 0;
    while i < bytes.len() {
        if !is_ascii_digit_byte(bytes[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn is_ascii_alnum_byte(c: u8) -> bool {
    is_ascii_digit_byte(c) || (c >= b'a' && c <= b'z') || (c >= b'A' && c <= b'Z')
}

/// Parse `VERSION_name.tql` into version digits and name.
pub fn parse_version_name(filename: &str) -> Result<(Version, String), ParseError> {
    let stem = match drop_suffix(filename, ".tql") {
        Some(s) => s,
        None => return Err(ParseError::Extension),
    };
    let (version, rest) = match split_once_char(stem, b'_') {
        Some(pair) => pair,
        None => return Err(ParseError::Filename),
    };
    if version.is_empty() || !is_ascii_digits(version) {
        return Err(ParseError::VersionDigits);
    }
    if rest.is_empty() {
        return Err(ParseError::Name);
    }
    Ok((Version::new(version), rest.to_string()))
}

/// Split migration file text into `(up, down)` bodies.
pub fn split_up_down(text: &str) -> Result<(String, String), ParseError> {
    let mut section = None::<Section>;
    let mut up = String::new();
    let mut down = String::new();
    let mut saw_marker = false;

    // Manual line iteration (byte indices on ASCII newlines / CR).
    let bytes = text.as_bytes();
    let mut i = 0;
    while i <= bytes.len() {
        let start = i;
        while i < bytes.len() && bytes[i] != b'\n' {
            i += 1;
        }
        let mut end = i;
        // Drop CR from CRLF
        if end > start && bytes[end - 1] == b'\r' {
            end -= 1;
        }
        let line = &text[start..end];
        if let Some(marker) = migration_marker(line) {
            section = Some(marker);
            saw_marker = true;
        } else {
            match section {
                Some(Section::Up) => {
                    up.push_str(line);
                    up.push('\n');
                }
                Some(Section::Down) => {
                    down.push_str(line);
                    down.push('\n');
                }
                None => {}
            }
        }
        if i < bytes.len() {
            i += 1; // skip '\n'
        } else {
            break;
        }
    }

    if !saw_marker && up.is_empty() && down.is_empty() {
        return Err(ParseError::Markers);
    }
    Ok((trim_owned(up), trim_owned(down)))
}

fn trim_owned(s: String) -> String {
    // Trim ASCII whitespace from both ends without `str::trim`.
    let bytes = s.as_bytes();
    let mut start = 0;
    while start < bytes.len() && is_ascii_ws(bytes[start]) {
        start += 1;
    }
    let mut end = bytes.len();
    while end > start && is_ascii_ws(bytes[end - 1]) {
        end -= 1;
    }
    s[start..end].to_string()
}

fn is_ascii_ws(c: u8) -> bool {
    c == b' ' || c == b'\t' || c == b'\n' || c == b'\r'
}

fn migration_marker(line: &str) -> Option<Section> {
    let trimmed = trim_spaces(line);
    let after_dashes = drop_prefix(trimmed, "--")?;
    let marker = trim_spaces(after_dashes);
    if eq_ignore_ascii_case(marker, "migrate:up") {
        Some(Section::Up)
    } else if eq_ignore_ascii_case(marker, "migrate:down") {
        Some(Section::Down)
    } else {
        None
    }
}

/// Classify each migration as Applied or Pending based on applied versions.
pub fn status_rows(
    files: &[MigrationId],
    applied: &[Version],
) -> Vec<(MigrationId, MigrationStatus)> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < files.len() {
        let f = files[i].clone();
        let status = if version_in(applied, &f.version) {
            MigrationStatus::Applied
        } else {
            MigrationStatus::Pending
        };
        out.push((f, status));
        i += 1;
    }
    out
}

fn version_in(applied: &[Version], v: &Version) -> bool {
    let mut i = 0;
    while i < applied.len() {
        if &applied[i] == v {
            return true;
        }
        i += 1;
    }
    false
}

/// Pending versions among `files` (not present in `applied`).
pub fn pending_versions(files: &[MigrationId], applied: &[Version]) -> Vec<Version> {
    let rows = status_rows(files, applied);
    let mut out = Vec::new();
    let mut i = 0;
    while i < rows.len() {
        let (id, status) = rows[i].clone();
        match status {
            MigrationStatus::Pending => {
                out.push(id.version);
            }
            MigrationStatus::Applied => {}
        }
        i += 1;
    }
    out
}

/// Applied versions among `files` (present in `applied`).
pub fn applied_among(files: &[MigrationId], applied: &[Version]) -> Vec<Version> {
    let rows = status_rows(files, applied);
    let mut out = Vec::new();
    let mut i = 0;
    while i < rows.len() {
        let (id, status) = rows[i].clone();
        match status {
            MigrationStatus::Applied => {
                out.push(id.version);
            }
            MigrationStatus::Pending => {}
        }
        i += 1;
    }
    out
}

/// True iff no version is both pending and applied for the given file list.
///
/// Derived from `status_rows`: each file gets exactly one status tag.
pub fn pending_applied_disjoint(files: &[MigrationId], applied: &[Version]) -> bool {
    let rows = status_rows(files, applied);
    let mut i = 0;
    let mut ok = true;
    while i < rows.len() {
        // A single status tag cannot be both Applied and Pending.
        match rows[i].1 {
            MigrationStatus::Applied => {}
            MigrationStatus::Pending => {}
        }
        i += 1;
    }
    // Cross-check: Pending rows are not in `applied`, Applied rows are.
    i = 0;
    while i < rows.len() {
        let in_applied = version_in(applied, &rows[i].0.version);
        match rows[i].1 {
            MigrationStatus::Applied => {
                if !in_applied {
                    ok = false;
                }
            }
            MigrationStatus::Pending => {
                if in_applied {
                    ok = false;
                }
            }
        }
        i += 1;
    }
    ok
}

/// Refuse pending migrations whose version is strictly less than max(applied).
pub fn check_strict_order(
    files: &[MigrationId],
    applied: &[Version],
) -> Result<(), StrictOrderError> {
    let max = match max_version(applied) {
        Some(m) => m,
        None => return Ok(()),
    };
    let mut i = 0;
    while i < files.len() {
        let pending = files[i].version.clone();
        if !version_in(applied, &pending) && str_lt(pending.as_str(), max.as_str()) {
            return Err(StrictOrderError::OutOfOrder {
                pending,
                applied_up_to: max,
            });
        }
        i += 1;
    }
    Ok(())
}

fn str_lt(a: &str, b: &str) -> bool {
    a < b
}

fn max_version(applied: &[Version]) -> Option<Version> {
    if applied.is_empty() {
        return None;
    }
    let mut best = 0usize;
    let mut i = 1;
    while i < applied.len() {
        if applied[i] > applied[best] {
            best = i;
        }
        i += 1;
    }
    Some(applied[best].clone())
}

/// Slugify a human migration name into a filesystem-safe suffix.
pub fn slugify(name: &str) -> String {
    let mut out = String::new();
    let bytes = name.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if is_ascii_alnum_byte(c) {
            let lower = ascii_lower(c);
            // ASCII alphanumeric → single UTF-8 char
            out.push(char::from(lower));
        } else if !ends_with_underscore(&out) {
            out.push('_');
        }
        i += 1;
    }
    let trimmed = trim_underscores(&out);
    if trimmed.is_empty() {
        String::from("migration")
    } else {
        trimmed.to_string()
    }
}

/// Header comments written by `dump`, listing applied migration labels.
pub fn dump_header(applied: &[Version], files: &[MigrationId]) -> String {
    let mut out = String::from("-- Schema dumped by tqlmate\n-- Applied migrations:\n");
    if applied.is_empty() {
        out.push_str("--   (none)\n");
    } else {
        let mut i = 0;
        while i < applied.len() {
            let v = &applied[i];
            out.push_str("--   ");
            match find_label(files, v) {
                Some(label) => out.push_str(&label),
                None => out.push_str(v.as_str()),
            }
            out.push('\n');
            i += 1;
        }
    }
    out.push('\n');
    out
}

fn find_label(files: &[MigrationId], v: &Version) -> Option<String> {
    let mut i = 0;
    while i < files.len() {
        if &files[i].version == v {
            return Some(files[i].label());
        }
        i += 1;
    }
    None
}

/// Strip leading blank / comment lines from a dump (load preamble).
pub fn strip_dump_header(text: &str) -> String {
    let mut started = false;
    let mut out = String::new();
    let mut first = true;
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let start = i;
        while i < bytes.len() && bytes[i] != b'\n' {
            i += 1;
        }
        let line = &text[start..i];
        // Consume the newline if present (like `str::lines`).
        if i < bytes.len() {
            i += 1;
        }
        if !started {
            let t = trim_spaces(line);
            if t.is_empty() || has_prefix(t, "--") {
                continue;
            }
            started = true;
        }
        if !first {
            out.push('\n');
        }
        out.push_str(line);
        first = false;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mid(version: &str) -> MigrationId {
        MigrationId {
            version: Version::new(version),
            name: version.into(),
        }
    }

    #[test]
    fn version_name_ok_and_bad() {
        let (v, n) = parse_version_name("20240101120000_create_person.tql").unwrap();
        assert_eq!(v.as_str(), "20240101120000");
        assert_eq!(n, "create_person");
        assert_eq!(
            parse_version_name("abc_name.tql"),
            Err(ParseError::VersionDigits)
        );
        assert_eq!(
            parse_version_name("123_name.sql"),
            Err(ParseError::Extension)
        );
    }

    #[test]
    fn split_markers() {
        let (u, d) = split_up_down(
            "-- migrate:up\ndefine entity x;\n\n-- migrate:down\nundefine entity x;\n",
        )
        .unwrap();
        assert_eq!(u, "define entity x;");
        assert_eq!(d, "undefine entity x;");
        assert_eq!(split_up_down("no markers"), Err(ParseError::Markers));
    }

    #[test]
    fn status_disjoint_and_strict() {
        let files = vec![mid("1"), mid("2"), mid("3")];
        let applied = [Version::new("1"), Version::new("3")];
        assert!(pending_applied_disjoint(&files, &applied));
        let rows = status_rows(&files, &applied);
        assert_eq!(rows[1].1, MigrationStatus::Pending);
        assert!(matches!(
            check_strict_order(&files, &applied),
            Err(StrictOrderError::OutOfOrder { .. })
        ));
    }

    #[test]
    fn slugify_and_dump() {
        assert_eq!(slugify("Create Person"), "create_person");
        assert_eq!(slugify("!!!"), "migration");
        let files = [MigrationId {
            version: Version::new("1"),
            name: "person".into(),
        }];
        let h = dump_header(&[Version::new("1")], &files);
        assert!(h.contains("--   1_person\n"));
        assert_eq!(
            strip_dump_header(&format!("{h}define\n  entity x;\n")),
            "define\n  entity x;"
        );
    }
}
