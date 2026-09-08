//! `_tqlmate_*` ledger schema: shipped migrations embedded in the binary.
//!
//! Ledger schema evolves via TypeQL files under `ledger/migrations/`, applied by
//! [`ensure`] before user migrations. Versions use 14-digit zero-padded ids in the
//! reserved range `00000000000001`–`00000000999999` (eight leading zeros) so they
//! sort before user `YYYYMMDDHHMMSS` timestamps and never appear as pending user
//! migrations.
//!
//! Ledger upgrades are **forward-only** in the CLI (downs are still required and
//! non-empty). Rolling back ledger types would need instance deletes before
//! `undefine` (TypeDB instances block type undefine).

use std::collections::HashSet;
use std::path::PathBuf;

use futures::StreamExt;
use typedb_driver::{TransactionType, TypeDBDriver};

use crate::migration::{parse_migration_body, parse_version_name, MigrationFile, Version};
use crate::{Error, Result};

pub const ENTITY: &str = "_tqlmate_schema_migration";
pub const ATTR_VERSION: &str = "_tqlmate_version";
pub const ATTR_APPLIED_AT: &str = "_tqlmate_applied_at";

/// 14-digit versions with eight leading zeros are reserved for shipped ledger migrations.
pub const LEDGER_VERSION_LEN: usize = 14;
pub const LEDGER_VERSION_PREFIX: &str = "00000000";

/// `(filename, file body)` baked into the binary. Add a new row when shipping a ledger migration.
const EMBEDDED_LEDGER_MIGRATIONS: &[(&str, &str)] = &[(
    "00000000000001_ledger_init.tql",
    include_str!("migrations/00000000000001_ledger_init.tql"),
)];

/// Action produced by [`plan_ledger_ensure`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LedgerEnsureAction {
    /// Run migrate:up and record the version.
    Apply(Version),
    /// Ledger types already exist (pre-migration bootstrap); record only.
    Stamp(Version),
}

/// True when `version` is in the reserved ledger range (not a user timestamp).
pub fn is_ledger_version(version: &Version) -> bool {
    let s = version.as_str();
    s.len() == LEDGER_VERSION_LEN
        && s.starts_with(LEDGER_VERSION_PREFIX)
        && s.chars().all(|c| c.is_ascii_digit())
}

/// Shipped ledger migrations, sorted by version (same parse rules as user `.tql` files).
pub fn shipped_ledger_migrations() -> Result<Vec<MigrationFile>> {
    let mut files = Vec::with_capacity(EMBEDDED_LEDGER_MIGRATIONS.len());
    for &(filename, text) in EMBEDDED_LEDGER_MIGRATIONS {
        files.push(parse_embedded(filename, text)?);
    }
    files.sort_by(|a, b| a.version.cmp(&b.version));
    for i in 1..files.len() {
        if files[i].version == files[i - 1].version {
            return Err(Error::DuplicateVersion(files[i].version.clone()));
        }
    }
    Ok(files)
}

fn parse_embedded(filename: &str, text: &str) -> Result<MigrationFile> {
    let (version, name) = parse_version_name(filename)?;
    let (up, down) = parse_migration_body(text)?;
    if up.trim().is_empty() {
        return Err(Error::EmptyUp(version));
    }
    if down.trim().is_empty() {
        return Err(Error::EmptyDown { version, name });
    }
    if !is_ledger_version(&version) {
        return Err(Error::msg(format!(
            "shipped ledger migration {filename} must use reserved version \
             {LEDGER_VERSION_PREFIX}… ({LEDGER_VERSION_LEN} digits)"
        )));
    }
    Ok(MigrationFile {
        version,
        name,
        path: PathBuf::from(format!("embedded:{filename}")),
        up,
        down,
    })
}

/// Decide which ledger migrations to apply or stamp.
///
/// `applied = None` means the ledger types are missing (fresh database).
/// `applied = Some(_)` means types exist; the first shipped migration is stamped
/// if it is pending (legacy one-shot bootstrap upgrade path).
pub fn plan_ledger_ensure(
    shipped: &[MigrationFile],
    applied: Option<&[Version]>,
) -> Vec<LedgerEnsureAction> {
    let Some(applied) = applied else {
        return shipped
            .iter()
            .map(|m| LedgerEnsureAction::Apply(m.version.clone()))
            .collect();
    };
    let applied_set: HashSet<&Version> = applied.iter().collect();
    let mut actions = Vec::new();
    for (i, m) in shipped.iter().enumerate() {
        if applied_set.contains(&m.version) {
            continue;
        }
        if i == 0 {
            actions.push(LedgerEnsureAction::Stamp(m.version.clone()));
        } else {
            actions.push(LedgerEnsureAction::Apply(m.version.clone()));
        }
    }
    actions
}

/// Concatenation of all shipped ledger `migrate:up` bodies (current ledger schema).
pub fn bootstrap_schema() -> String {
    shipped_ledger_migrations()
        .expect("shipped ledger migrations must parse")
        .iter()
        .map(|m| m.up.as_str())
        .collect::<Vec<_>>()
        .join("\n")
}

/// Apply pending shipped ledger migrations (idempotent).
pub async fn ensure(driver: &TypeDBDriver, database: &str) -> Result<()> {
    let shipped = shipped_ledger_migrations()?;
    let applied = all_applied_versions(driver, database).await.ok();
    let plan = plan_ledger_ensure(&shipped, applied.as_deref());
    for action in plan {
        match action {
            LedgerEnsureAction::Apply(version) => {
                let m = shipped
                    .iter()
                    .find(|m| m.version == version)
                    .ok_or_else(|| {
                        Error::msg(format!("missing shipped ledger migration {version}"))
                    })?;
                apply_ledger_up(driver, database, m).await?;
            }
            LedgerEnsureAction::Stamp(version) => {
                stamp_ledger(driver, database, &version).await?;
            }
        }
    }
    Ok(())
}

async fn apply_ledger_up(driver: &TypeDBDriver, database: &str, m: &MigrationFile) -> Result<()> {
    let applied_at = chrono::Utc::now().format("%Y-%m-%dT%H:%M:%S").to_string();
    let insert = record_insert(&m.version, &applied_at);
    schema_queries(driver, database, &[m.up.as_str(), insert.as_str()]).await
}

async fn stamp_ledger(driver: &TypeDBDriver, database: &str, version: &Version) -> Result<()> {
    let applied_at = chrono::Utc::now().format("%Y-%m-%dT%H:%M:%S").to_string();
    let insert = record_insert(version, &applied_at);
    schema_queries(driver, database, &[insert.as_str()]).await
}

/// User-facing applied versions (ledger reserved versions filtered out).
pub async fn applied_versions(driver: &TypeDBDriver, database: &str) -> Result<Vec<Version>> {
    let mut versions = all_applied_versions(driver, database).await?;
    versions.retain(|v| !is_ledger_version(v));
    Ok(versions)
}

async fn all_applied_versions(driver: &TypeDBDriver, database: &str) -> Result<Vec<Version>> {
    let tx = driver.transaction(database, TransactionType::Read).await?;
    let query = format!("match $m isa {ENTITY}, has {ATTR_VERSION} $v;");
    let answer = match tx.query(query).await {
        Ok(a) => a,
        Err(e) => {
            let _ = tx.close().await;
            return Err(e.into());
        }
    };
    let mut versions = Vec::new();
    let mut rows = answer.into_rows();
    while let Some(row) = rows.next().await {
        let row = row?;
        let concept = row
            .get("v")?
            .ok_or_else(|| Error::msg("missing version column"))?;
        let version = concept
            .try_get_string()
            .ok_or_else(|| Error::msg("version is not a string"))?
            .to_string();
        versions.push(Version::new(version));
    }
    let _ = tx.close().await;
    versions.sort();
    Ok(versions)
}

pub fn record_insert(version: &Version, applied_at: &str) -> String {
    format!(
        "insert $_ isa {ENTITY}, has {ATTR_VERSION} \"{}\", has {ATTR_APPLIED_AT} {applied_at};",
        version.as_str()
    )
}

pub fn record_delete(version: &Version) -> String {
    format!(
        "match $m isa {ENTITY}, has {ATTR_VERSION} \"{}\"; delete $m;",
        version.as_str()
    )
}

/// Header comments written by `dump`, listing applied migration labels.
pub fn dump_header(applied: &[Version], files: &[MigrationFile]) -> String {
    let mut out = String::from("-- Schema dumped by tqlmate\n-- Applied migrations:\n");
    if applied.is_empty() {
        out.push_str("--   (none)\n");
    } else {
        for v in applied {
            match files.iter().find(|f| &f.version == v) {
                Some(m) => out.push_str(&format!("--   {}\n", m.label())),
                None => out.push_str(&format!("--   {v}\n")),
            }
        }
    }
    out.push('\n');
    out
}

pub fn strip_dump_header(text: &str) -> String {
    text.lines()
        .skip_while(|l| {
            let t = l.trim();
            t.is_empty() || t.starts_with("--")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

pub async fn schema_queries(driver: &TypeDBDriver, database: &str, queries: &[&str]) -> Result<()> {
    let tx = driver
        .transaction(database, TransactionType::Schema)
        .await?;
    for q in queries {
        let trimmed = q.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Err(e) = tx.query(trimmed).await {
            let _ = tx.close().await;
            return Err(e.into());
        }
    }
    tx.commit().await?;
    Ok(())
}
