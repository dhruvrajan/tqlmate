//! Pure migration / ledger helpers — no filesystem, async, or TypeDB.
//!
//! Written for Charon → Aeneas (Lean) extraction. Avoids `HashSet`, `Path`,
//! `thiserror`, and several `str` helpers (`strip_suffix`, `ends_with`,
//! `trim_matches`, `strip_prefix`) that Aeneas does not model yet.
//! Byte-range checks stay explicit (no `RangeInclusive::contains`) for the
//! same reason.
//!
//! # Verified migrate / rollback core
//!
//! [`plan_migrate`] / [`plan_rollback`] decide an ordered [`Plan`] of [`Op`]s.
//! [`step`] / [`run`] interpret plans over abstract [`State`] (applied versions).
//! The TypeDB runner executes a plan under effect axioms (see `verification/README.md`).
//!
//! A parallel **Verus** path (`verification/verus`) proves the same class of
//! migrate/rollback properties on Verus-annotated Rust; CI runs both verifiers
//! until Verus fully supersedes the Aeneas extract story.
#![allow(dead_code)]
#![allow(clippy::manual_range_contains)]
// Prefer explicit `match` / `Vec::new`+`push` so Charon→Aeneas extracts cleanly.
#![allow(clippy::question_mark)]
#![allow(clippy::vec_init_then_push)]

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
    /// Multi-section file: a `-- migrate:up` block has no following `-- migrate:down`.
    SectionMissingDown,
    /// Multi-section file: `-- migrate:down` appears before `-- migrate:up` in a section.
    SectionWrongOrder,
    /// Multi-section file: more than one `-- migrate:down` in a single section.
    SectionMultipleDown,
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

/// One `(up, down)` pair inside a migration file (dbmate multi-section unit).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MigrationSection {
    pub up: String,
    pub down: String,
}

/// Count `-- migrate:up` markers (case-insensitive).
fn count_up_markers(text: &str) -> usize {
    let bytes = text.as_bytes();
    let mut n = 0usize;
    let mut i = 0;
    while i <= bytes.len() {
        let start = i;
        while i < bytes.len() && bytes[i] != b'\n' {
            i += 1;
        }
        let mut end = i;
        if end > start && bytes[end - 1] == b'\r' {
            end -= 1;
        }
        let line = &text[start..end];
        if let Some(Section::Up) = migration_marker(line) {
            n += 1;
        }
        if i < bytes.len() {
            i += 1;
        } else {
            break;
        }
    }
    n
}

/// Split migration file text into `(up, down)` bodies.
///
/// Single-section files (≤1 `migrate:up`) keep the historical permissive
/// concat behaviour. Prefer [`parse_sections`] when executing migrations.
pub fn split_up_down(text: &str) -> Result<(String, String), ParseError> {
    split_up_down_concat(text)
}

/// Historical line scan: every up line goes into one up body, every down into one down.
fn split_up_down_concat(text: &str) -> Result<(String, String), ParseError> {
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

/// Parse migration file text into ordered `(up, down)` sections (dbmate v2.37+).
///
/// * **≤1 `migrate:up`:** same permissive rules as [`split_up_down`] (one section).
/// * **≥2 `migrate:up`:** each section is `migrate:up` … next `migrate:up` / EOF;
///   every section must contain exactly one `migrate:down` after its `migrate:up`.
pub fn parse_sections(text: &str) -> Result<Vec<MigrationSection>, ParseError> {
    if count_up_markers(text) <= 1 {
        let (up, down) = split_up_down_concat(text)?;
        let mut out = Vec::new();
        out.push(MigrationSection { up, down });
        return Ok(out);
    }
    parse_multi_sections(text)
}

/// dbmate-style multi-section parse (≥2 `migrate:up` markers).
fn parse_multi_sections(text: &str) -> Result<Vec<MigrationSection>, ParseError> {
    // Collect byte starts of each `migrate:up` line.
    let bytes = text.as_bytes();
    let mut up_starts: Vec<usize> = Vec::new();
    let mut i = 0;
    while i <= bytes.len() {
        let start = i;
        while i < bytes.len() && bytes[i] != b'\n' {
            i += 1;
        }
        let mut end = i;
        if end > start && bytes[end - 1] == b'\r' {
            end -= 1;
        }
        let line = &text[start..end];
        if let Some(Section::Up) = migration_marker(line) {
            up_starts.push(start);
        }
        if i < bytes.len() {
            i += 1;
        } else {
            break;
        }
    }
    if up_starts.is_empty() {
        return Err(ParseError::Markers);
    }

    let mut sections: Vec<MigrationSection> = Vec::new();
    let mut s_i = 0;
    while s_i < up_starts.len() {
        let begin = up_starts[s_i];
        let end = if s_i + 1 < up_starts.len() {
            up_starts[s_i + 1]
        } else {
            text.len()
        };
        let chunk = &text[begin..end];
        sections.push(parse_one_multi_section(chunk)?);
        s_i += 1;
    }
    Ok(sections)
}

/// Parse one section substring that begins at its `migrate:up` marker.
fn parse_one_multi_section(chunk: &str) -> Result<MigrationSection, ParseError> {
    let mut section = None::<Section>;
    let mut up = String::new();
    let mut down = String::new();
    let mut saw_up = false;
    let mut saw_down = false;

    let bytes = chunk.as_bytes();
    let mut i = 0;
    while i <= bytes.len() {
        let start = i;
        while i < bytes.len() && bytes[i] != b'\n' {
            i += 1;
        }
        let mut end = i;
        if end > start && bytes[end - 1] == b'\r' {
            end -= 1;
        }
        let line = &chunk[start..end];
        if let Some(marker) = migration_marker(line) {
            match marker {
                Section::Up => {
                    if saw_up {
                        // Should not happen: multi split is at up boundaries.
                        return Err(ParseError::SectionWrongOrder);
                    }
                    section = Some(Section::Up);
                    saw_up = true;
                }
                Section::Down => {
                    if !saw_up {
                        return Err(ParseError::SectionWrongOrder);
                    }
                    if saw_down {
                        return Err(ParseError::SectionMultipleDown);
                    }
                    section = Some(Section::Down);
                    saw_down = true;
                }
            }
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
            i += 1;
        } else {
            break;
        }
    }

    if !saw_up {
        return Err(ParseError::Markers);
    }
    if !saw_down {
        return Err(ParseError::SectionMissingDown);
    }
    Ok(MigrationSection {
        up: trim_owned(up),
        down: trim_owned(down),
    })
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

// ---------------------------------------------------------------------------
// Migrate / rollback planning + abstract ledger interpreter (verified core)
// ---------------------------------------------------------------------------

/// Migration file contents as pure data (no filesystem path).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MigrationSpec {
    pub version: Version,
    pub name: String,
    /// Ordered `(up, down)` sections. Ledger version is recorded once after the
    /// last up section; rollback runs downs last-to-first and deletes once.
    pub sections: Vec<MigrationSection>,
}

impl MigrationSpec {
    pub fn label(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.version.0);
        out.push('_');
        out.push_str(&self.name);
        out
    }

    /// Single-section convenience (tests / simple fixtures).
    pub fn single(version: Version, name: String, up: String, down: String) -> Self {
        let mut sections = Vec::new();
        sections.push(MigrationSection { up, down });
        Self {
            version,
            name,
            sections,
        }
    }
}

/// One planned schema effect (executed by the trusted TypeDB runner).
///
/// `record` / `delete` are true only on the last section of a file so the
/// ledger version is written or removed once (dbmate v2.37.0).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    ApplyUp {
        version: Version,
        up: String,
        record: bool,
    },
    ApplyDown {
        version: Version,
        down: String,
        delete: bool,
    },
}

/// Ordered list of ops produced by [`plan_migrate`] / [`plan_rollback`].
pub type Plan = Vec<Op>;

/// Abstract ledger state: applied versions in application order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    pub applied: Vec<Version>,
}

impl State {
    pub fn new(applied: Vec<Version>) -> Self {
        Self { applied }
    }

    pub fn empty() -> Self {
        Self {
            applied: Vec::new(),
        }
    }
}

/// Planning errors (no I/O). Mapped to crate [`Error`](crate::Error) by the runner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlanError {
    EmptyUp(Version),
    EmptyDown {
        version: Version,
        name: String,
    },
    MissingFile(Version),
    StrictOrder {
        pending: Version,
        applied_up_to: Version,
    },
}

/// Interpreter errors when stepping an ill-formed op (defense in depth).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepError {
    EmptyUp(Version),
    EmptyDown(Version),
}

/// True iff `s` is empty or ASCII-whitespace only (no `str::trim`).
pub fn body_is_empty(s: &str) -> bool {
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if !is_ascii_ws(bytes[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn find_spec<'a>(files: &'a [MigrationSpec], v: &Version) -> Option<&'a MigrationSpec> {
    let mut i = 0;
    while i < files.len() {
        if &files[i].version == v {
            return Some(&files[i]);
        }
        i += 1;
    }
    None
}

/// Apply one op to abstract state.
///
/// `ApplyUp` with `record` appends the version; without `record` the abstract
/// ledger is unchanged (intermediate multi-section body). Symmetrically,
/// `ApplyDown` with `delete` removes the last matching version.
///
/// Takes ownership so successful recording `ApplyUp` is a pure `Vec::push`.
pub fn step(state: State, op: Op) -> Result<State, StepError> {
    match op {
        Op::ApplyUp {
            version,
            up,
            record,
        } => {
            if body_is_empty(&up) {
                return Err(StepError::EmptyUp(version));
            }
            if record {
                let mut applied = state.applied;
                applied.push(version);
                Ok(State { applied })
            } else {
                Ok(state)
            }
        }
        Op::ApplyDown {
            version,
            down,
            delete,
        } => {
            if body_is_empty(&down) {
                return Err(StepError::EmptyDown(version));
            }
            if delete {
                let applied = remove_last_matching(&state.applied, &version);
                Ok(State { applied })
            } else {
                Ok(state)
            }
        }
    }
}

/// Clone `applied[0..n]` (stops at `applied.len()` if `n` is larger).
fn prefix_clone(applied: &[Version], n: usize) -> Vec<Version> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < n && i < applied.len() {
        out.push(applied[i].clone());
        i += 1;
    }
    out
}

/// Remove the last occurrence of `v` in `applied` (unchanged if absent).
///
/// Recurses from the end so Aeneas extracts a `partial_fixpoint` that admits
/// induction: if the last element equals `v`, return the prefix; otherwise
/// recurse on the prefix and push the last element back.
pub fn remove_last_matching(applied: &[Version], v: &Version) -> Vec<Version> {
    if applied.is_empty() {
        return Vec::new();
    }
    let last_i = applied.len() - 1;
    if &applied[last_i] == v {
        prefix_clone(applied, last_i)
    } else {
        let mut out = remove_last_matching(&applied[..last_i], v);
        out.push(applied[last_i].clone());
        out
    }
}

/// Run a plan left-to-right (recursive fold — extracts as `partial_fixpoint`).
///
/// `run(s, []) = Ok(s)`; `run(s, op::rest) = step(s, op).and_then(|s'| run(s', rest))`.
pub fn run(state: State, plan: &[Op]) -> Result<State, StepError> {
    if plan.is_empty() {
        Ok(state)
    } else {
        let next = match step(state, plan[0].clone()) {
            Ok(s) => s,
            Err(e) => return Err(e),
        };
        run(next, &plan[1..])
    }
}

/// Pending specs among `files` (not in `applied`), preserving file order.
///
/// Clone-before-check so Aeneas can match borrow contexts.
pub fn pending_specs(files: &[MigrationSpec], applied: &[Version]) -> Vec<MigrationSpec> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < files.len() {
        let f = files[i].clone();
        let is_pending = !version_in(applied, &f.version);
        if is_pending {
            out.push(f);
        }
        i += 1;
    }
    out
}

/// Build ApplyUp ops from pending specs; one op per section; reject empty ups.
///
/// `record` is set only on the last section of each file.
fn plan_ups_from_pending(pending: &[MigrationSpec]) -> Result<Plan, PlanError> {
    let mut plan: Plan = Vec::new();
    let mut i = 0;
    while i < pending.len() {
        let f = &pending[i];
        if f.sections.is_empty() {
            return Err(PlanError::EmptyUp(f.version.clone()));
        }
        let mut j = 0;
        while j < f.sections.len() {
            let up = &f.sections[j].up;
            if body_is_empty(up) {
                return Err(PlanError::EmptyUp(f.version.clone()));
            }
            let record = j + 1 == f.sections.len();
            plan.push(Op::ApplyUp {
                version: f.version.clone(),
                up: up.clone(),
                record,
            });
            j += 1;
        }
        i += 1;
    }
    Ok(plan)
}

/// Plan pending ups: files not in `applied`, in file order (caller sorts files).
///
/// Rejects empty `up` bodies. When `strict`, rejects pending versions `< max(applied)`.
pub fn plan_migrate(
    files: &[MigrationSpec],
    applied: &[Version],
    strict: bool,
) -> Result<Plan, PlanError> {
    if strict {
        match check_strict_order_specs(files, applied) {
            Ok(()) => {}
            Err(StrictOrderError::OutOfOrder {
                pending,
                applied_up_to,
            }) => {
                return Err(PlanError::StrictOrder {
                    pending,
                    applied_up_to,
                });
            }
        }
    }
    let pending = pending_specs(files, applied);
    plan_ups_from_pending(&pending)
}

/// Plan downs for the last applied version (or empty plan if none applied).
///
/// Down sections run last-to-first; `delete` is set only on the final op
/// (first section in the file). Rejects missing file and empty down bodies.
pub fn plan_rollback(files: &[MigrationSpec], applied: &[Version]) -> Result<Plan, PlanError> {
    if applied.is_empty() {
        return Ok(Vec::new());
    }
    let version = applied[applied.len() - 1].clone();
    let m = match find_spec(files, &version) {
        Some(m) => m,
        None => return Err(PlanError::MissingFile(version)),
    };
    if m.sections.is_empty() {
        return Err(PlanError::EmptyDown {
            version: m.version.clone(),
            name: m.name.clone(),
        });
    }
    let mut plan: Plan = Vec::new();
    // Reverse order: last section first.
    let mut j = m.sections.len();
    while j > 0 {
        j -= 1;
        let down = &m.sections[j].down;
        if body_is_empty(down) {
            return Err(PlanError::EmptyDown {
                version: m.version.clone(),
                name: m.name.clone(),
            });
        }
        let delete = j == 0;
        plan.push(Op::ApplyDown {
            version: m.version.clone(),
            down: down.clone(),
            delete,
        });
    }
    Ok(plan)
}

/// Optional status planning: classify each file (same as [`status_rows`] on ids).
pub fn plan_status(
    files: &[MigrationSpec],
    applied: &[Version],
) -> Vec<(MigrationSpec, MigrationStatus)> {
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

fn check_strict_order_specs(
    files: &[MigrationSpec],
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

    fn spec(version: &str, up: &str, down: &str) -> MigrationSpec {
        MigrationSpec::single(
            Version::new(version),
            version.into(),
            up.into(),
            down.into(),
        )
    }

    fn multi(version: &str, sections: &[(&str, &str)]) -> MigrationSpec {
        let mut secs = Vec::new();
        let mut i = 0;
        while i < sections.len() {
            secs.push(MigrationSection {
                up: sections[i].0.into(),
                down: sections[i].1.into(),
            });
            i += 1;
        }
        MigrationSpec {
            version: Version::new(version),
            name: version.into(),
            sections: secs,
        }
    }

    #[test]
    fn plan_migrate_pending_and_idempotent() {
        let files = vec![
            spec("1", "u1", "d1"),
            spec("2", "u2", "d2"),
            spec("3", "u3", "d3"),
        ];
        let applied = [Version::new("1")];
        let plan = plan_migrate(&files, &applied, false).unwrap();
        assert_eq!(plan.len(), 2);
        assert!(matches!(&plan[0], Op::ApplyUp { version, .. } if version.as_str() == "2"));
        assert!(matches!(&plan[1], Op::ApplyUp { version, .. } if version.as_str() == "3"));

        let state = State::new(applied.to_vec());
        let next = run(state, &plan).unwrap();
        assert_eq!(
            next.applied,
            vec![Version::new("1"), Version::new("2"), Version::new("3")]
        );

        let again = plan_migrate(&files, &next.applied, false).unwrap();
        assert!(again.is_empty());
        assert_eq!(run(next.clone(), &again).unwrap(), next);
    }

    #[test]
    fn plan_migrate_rejects_empty_up_and_strict() {
        let files = vec![spec("1", "u1", "d1"), spec("2", "", "d2")];
        assert!(matches!(
            plan_migrate(&files, &[], false),
            Err(PlanError::EmptyUp(v)) if v.as_str() == "2"
        ));

        let files = vec![
            spec("1", "u1", "d1"),
            spec("2", "u2", "d2"),
            spec("3", "u3", "d3"),
        ];
        let applied = [Version::new("1"), Version::new("3")];
        assert!(matches!(
            plan_migrate(&files, &applied, true),
            Err(PlanError::StrictOrder { pending, applied_up_to })
                if pending.as_str() == "2" && applied_up_to.as_str() == "3"
        ));
    }

    #[test]
    fn plan_rollback_inverse_and_edge_cases() {
        let files = vec![spec("1", "u1", "d1"), spec("2", "u2", "d2")];
        let state0 = State::empty();
        let up = plan_migrate(&files, &state0.applied, false).unwrap();
        let state1 = run(state0.clone(), &up[..1]).unwrap();
        assert_eq!(state1.applied, vec![Version::new("1")]);

        let down = plan_rollback(&files, &state1.applied).unwrap();
        assert_eq!(down.len(), 1);
        let back = run(state1, &down).unwrap();
        assert_eq!(back.applied, state0.applied);

        assert!(plan_rollback(&files, &[]).unwrap().is_empty());
        assert!(matches!(
            plan_rollback(&[], &[Version::new("9")]),
            Err(PlanError::MissingFile(v)) if v.as_str() == "9"
        ));
        let empty_down = vec![spec("1", "u1", "")];
        assert!(matches!(
            plan_rollback(&empty_down, &[Version::new("1")]),
            Err(PlanError::EmptyDown { version, .. }) if version.as_str() == "1"
        ));
    }

    #[test]
    fn remove_last_matching_drops_last_occurrence() {
        let a = |s: &str| Version::new(s);
        assert_eq!(remove_last_matching(&[], &a("1")), vec![]);
        assert_eq!(remove_last_matching(&[a("1")], &a("1")), vec![]);
        assert_eq!(
            remove_last_matching(&[a("1"), a("2"), a("1")], &a("1")),
            vec![a("1"), a("2")]
        );
        assert_eq!(
            remove_last_matching(&[a("1"), a("2")], &a("9")),
            vec![a("1"), a("2")]
        );
    }

    #[test]
    fn step_rejects_empty_bodies() {
        assert!(matches!(
            step(
                State::empty(),
                Op::ApplyUp {
                    version: Version::new("1"),
                    up: "  \n".into(),
                    record: true,
                }
            ),
            Err(StepError::EmptyUp(_))
        ));
        assert!(matches!(
            step(
                State::empty(),
                Op::ApplyDown {
                    version: Version::new("1"),
                    down: "".into(),
                    delete: true,
                }
            ),
            Err(StepError::EmptyDown(_))
        ));
    }

    #[test]
    fn parse_sections_single_matches_split() {
        let text = "-- migrate:up\ndefine entity x;\n\n-- migrate:down\nundefine entity x;\n";
        let (u, d) = split_up_down(text).unwrap();
        let secs = parse_sections(text).unwrap();
        assert_eq!(secs.len(), 1);
        assert_eq!(secs[0].up, u);
        assert_eq!(secs[0].down, d);
    }

    #[test]
    fn parse_sections_multi_keeps_pairs() {
        let text = "\
-- migrate:up
define entity a;

-- migrate:down
undefine entity a;

-- migrate:up
define entity b;

-- migrate:down
undefine entity b;
";
        let secs = parse_sections(text).unwrap();
        assert_eq!(secs.len(), 2);
        assert_eq!(secs[0].up, "define entity a;");
        assert_eq!(secs[0].down, "undefine entity a;");
        assert_eq!(secs[1].up, "define entity b;");
        assert_eq!(secs[1].down, "undefine entity b;");
        // Legacy concat still joins in file order (not reverse).
        let (u, d) = split_up_down(text).unwrap();
        assert_eq!(u, "define entity a;\n\ndefine entity b;");
        assert_eq!(d, "undefine entity a;\n\nundefine entity b;");
    }

    #[test]
    fn parse_sections_multi_rejects_missing_down() {
        let text = "-- migrate:up\nA;\n-- migrate:up\nB;\n-- migrate:down\nb;\n";
        assert_eq!(parse_sections(text), Err(ParseError::SectionMissingDown));
    }

    #[test]
    fn plan_multi_section_records_once_rollback_reverses() {
        let files = vec![multi("1", &[("u1", "d1"), ("u2", "d2")])];
        let plan = plan_migrate(&files, &[], false).unwrap();
        assert_eq!(plan.len(), 2);
        assert!(matches!(
            &plan[0],
            Op::ApplyUp {
                up,
                record: false,
                ..
            } if up == "u1"
        ));
        assert!(matches!(
            &plan[1],
            Op::ApplyUp {
                up,
                record: true,
                ..
            } if up == "u2"
        ));
        let next = run(State::empty(), &plan).unwrap();
        assert_eq!(next.applied, vec![Version::new("1")]);

        let down = plan_rollback(&files, &next.applied).unwrap();
        assert_eq!(down.len(), 2);
        assert!(matches!(
            &down[0],
            Op::ApplyDown {
                down,
                delete: false,
                ..
            } if down == "d2"
        ));
        assert!(matches!(
            &down[1],
            Op::ApplyDown {
                down,
                delete: true,
                ..
            } if down == "d1"
        ));
        assert!(run(next, &down).unwrap().applied.is_empty());
    }
}
