//! Library surface for the `tqlmate` CLI: URL parsing, migration files, ledger TypeQL, and runner.

pub mod cli;
mod ledger;
mod migration;
/// Pure migration/ledger algorithm (Charon/Aeneas extractable; no I/O).
pub mod pure;
mod runner;
mod url;

pub use ledger::{
    bootstrap_schema, dump_header, is_ledger_version, plan_ledger_ensure, record_delete,
    record_insert, shipped_ledger_migrations, strip_dump_header, LedgerEnsureAction,
    ATTR_APPLIED_AT, ATTR_VERSION, ENTITY, LEDGER_INIT_VERSION, LEDGER_VERSION_LEN,
    LEDGER_VERSION_PREFIX,
};
pub use migration::{
    check_strict_order, list_migration_files, migration_template, new_migration_path,
    parse_migration, parse_migration_body, parse_version_name, slugify, status_rows, MigrationFile,
    MigrationStatus, Version,
};
pub use pure::{
    body_is_empty, pending_specs, plan_migrate, plan_rollback, plan_status, run, step,
    MigrationSpec, Op, Plan, PlanError, State, StepError,
};
pub use runner::{
    abstract_run, default_migrations_dir, default_schema_file, plan_migrate_files,
    plan_rollback_files, resolve_url, resolve_url_from, Opts, Runner,
};
pub use url::{TypeDbUrl, DEFAULT_PASSWORD, DEFAULT_USERNAME};

/// Library error type. The CLI maps this into `anyhow::Error`.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("{0}")]
    Message(String),

    #[error("URL must start with typedb://, e.g. typedb://localhost:1729/mydb (got {0:?})")]
    UrlScheme(String),

    #[error("URL credentials must be user:pass, e.g. typedb://admin:password@localhost:1729/mydb")]
    UrlAuthPair,

    #[error("URL must name a database, e.g. typedb://localhost:1729/mydb")]
    UrlDatabase,

    #[error("no TypeDB URL configured")]
    UrlMissing,

    #[error("invalid port: {0}")]
    UrlPort(String),

    #[error("migration must end in .tql: {0}")]
    MigrationExtension(String),

    #[error("expected VERSION_name.tql: {0}")]
    MigrationFilename(String),

    #[error("version must be digits: {0}")]
    MigrationVersionDigits(String),

    #[error("missing name after version: {0}")]
    MigrationName(String),

    #[error("migration missing -- migrate:up / -- migrate:down")]
    MigrationMarkers,

    #[error("duplicate migration version {0}")]
    DuplicateVersion(Version),

    #[error(
        "strict: pending migration {pending} would apply out of order (applied up to {applied_up_to})"
    )]
    StrictOrder {
        pending: Version,
        applied_up_to: Version,
    },

    #[error("database does not exist: {0} (run create or up)")]
    DatabaseMissing(String),

    #[error("migration {0} has empty migrate:up")]
    EmptyUp(Version),

    #[error("migration {version}_{name} has empty migrate:down")]
    EmptyDown { version: Version, name: String },

    #[error("applied version {0} has no matching migration file")]
    MissingMigrationFile(Version),

    #[error("schema file is empty")]
    EmptySchema,

    #[error("timed out waiting for TypeDB at {address}: {cause}")]
    WaitTimeout { address: String, cause: String },

    #[error(transparent)]
    Io(#[from] std::io::Error),

    #[error(transparent)]
    TypeDb(Box<typedb_driver::Error>),
}

pub type Result<T> = std::result::Result<T, Error>;

impl Error {
    pub fn msg(m: impl Into<String>) -> Self {
        Self::Message(m.into())
    }
}

impl From<typedb_driver::Error> for Error {
    fn from(e: typedb_driver::Error) -> Self {
        Self::TypeDb(Box::new(e))
    }
}
