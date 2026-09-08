use std::path::PathBuf;
use std::time::Duration;

use typedb_driver::{Addresses, Credentials, DriverOptions, DriverTlsConfig, TypeDBDriver};

use crate::ledger::{self, dump_header, schema_queries, strip_dump_header};
use crate::migration::{
    self, list_migration_files, new_migration_path, status_rows, MigrationFile, MigrationStatus,
    Version,
};
use crate::pure::{self, Op, Plan, PlanError, State};
use crate::url::TypeDbUrl;
use crate::{Error, Result};

#[derive(Debug, Clone)]
pub struct Opts {
    /// `None` for commands that never connect (`new`).
    pub url: Option<TypeDbUrl>,
    pub migrations_dir: PathBuf,
    pub schema_file: PathBuf,
    pub strict: bool,
    pub verbose: bool,
    pub wait_timeout: Option<Duration>,
}

pub struct Runner {
    opts: Opts,
    driver: Option<TypeDBDriver>,
}

impl Runner {
    pub fn new(opts: Opts) -> Self {
        Self { opts, driver: None }
    }

    fn url(&self) -> Result<&TypeDbUrl> {
        self.opts.url.as_ref().ok_or(Error::UrlMissing)
    }

    fn database(&self) -> Result<String> {
        Ok(self.url()?.database.clone())
    }

    async fn connect(&mut self) -> Result<&TypeDBDriver> {
        if self.driver.is_none() {
            if let Some(timeout) = self.opts.wait_timeout {
                wait_for_server(self.url()?, timeout, self.opts.verbose).await?;
            }
            self.driver = Some(open_driver(self.url()?).await?);
        }
        self.driver
            .as_ref()
            .ok_or_else(|| Error::msg("internal: driver missing after connect"))
    }

    pub async fn create(&mut self) -> Result<()> {
        let name = self.database()?;
        let verbose = self.opts.verbose;
        let driver = self.connect().await?;
        if driver.databases().contains(name.clone()).await? {
            if verbose {
                eprintln!("database already exists: {name}");
            }
            return Ok(());
        }
        driver.databases().create(name.clone()).await?;
        println!("Created: {name}");
        Ok(())
    }

    pub async fn drop(&mut self) -> Result<()> {
        let name = self.database()?;
        let verbose = self.opts.verbose;
        let driver = self.connect().await?;
        if !driver.databases().contains(name.clone()).await? {
            if verbose {
                eprintln!("database does not exist: {name}");
            }
            return Ok(());
        }
        let db = driver.databases().get(name.clone()).await?;
        db.delete().await?;
        println!("Dropped: {name}");
        Ok(())
    }

    pub async fn new_migration(&self, name: &str) -> Result<PathBuf> {
        std::fs::create_dir_all(&self.opts.migrations_dir)?;
        let path = new_migration_path(&self.opts.migrations_dir, name);
        std::fs::write(&path, migration::migration_template())?;
        println!("Created: {}", path.display());
        Ok(path)
    }

    pub async fn migrate(&mut self) -> Result<()> {
        let db = self.database()?;
        let dir = self.opts.migrations_dir.clone();
        let strict = self.opts.strict;
        let verbose = self.opts.verbose;

        let driver = self.connect().await?;
        if !driver.databases().contains(db.clone()).await? {
            return Err(Error::DatabaseMissing(db));
        }
        ledger::ensure(driver, &db).await?;
        let files = list_migration_files(&dir)?;
        let applied = ledger::applied_versions(driver, &db).await?;
        let plan = plan_migrate_files(&files, &applied, strict)?;
        if plan.is_empty() {
            if verbose {
                eprintln!("Migrations: nothing to apply");
            }
            return Ok(());
        }
        execute_plan(driver, &db, &files, &plan, verbose).await
    }

    pub async fn rollback(&mut self) -> Result<()> {
        let db = self.database()?;
        let dir = self.opts.migrations_dir.clone();
        let verbose = self.opts.verbose;

        let driver = self.connect().await?;
        ledger::ensure(driver, &db).await?;
        let files = list_migration_files(&dir)?;
        let applied = ledger::applied_versions(driver, &db).await?;
        let plan = plan_rollback_files(&files, &applied)?;
        if plan.is_empty() {
            if verbose {
                eprintln!("Rollback: nothing to roll back");
            }
            return Ok(());
        }
        execute_plan(driver, &db, &files, &plan, verbose).await
    }

    pub async fn status(&mut self, quiet: bool) -> Result<bool> {
        let db = self.database()?;
        let dir = self.opts.migrations_dir.clone();
        let strict = self.opts.strict;

        let driver = self.connect().await?;
        let applied = if driver.databases().contains(db.clone()).await? {
            ledger::applied_versions(driver, &db)
                .await
                .unwrap_or_default()
        } else {
            Vec::new()
        };
        let files = list_migration_files(&dir)?;
        if strict {
            migration::check_strict_order(&files, &applied)?;
        }
        let rows = status_rows(&files, &applied);
        let pending = rows.iter().any(|(_, s)| *s == MigrationStatus::Pending);
        if !quiet {
            for (m, status) in &rows {
                let mark = match status {
                    MigrationStatus::Applied => "[X]",
                    MigrationStatus::Pending => "[ ]",
                };
                println!("{mark} {}", m.label());
            }
            if rows.is_empty() {
                println!("No migrations found.");
            }
        }
        Ok(pending)
    }

    pub async fn dump(&mut self) -> Result<()> {
        let db_name = self.database()?;
        let schema_file = self.opts.schema_file.clone();
        let dir = self.opts.migrations_dir.clone();

        let driver = self.connect().await?;
        let db = driver.databases().get(db_name.clone()).await?;
        let schema = db.schema().await?;
        let applied = ledger::applied_versions(driver, &db_name)
            .await
            .unwrap_or_default();
        let files = list_migration_files(&dir)?;

        if let Some(parent) = schema_file.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let mut out = dump_header(&applied, &files);
        out.push_str(schema.trim());
        out.push('\n');
        std::fs::write(&schema_file, out)?;
        println!("Wrote: {}", schema_file.display());
        Ok(())
    }

    pub async fn load(&mut self) -> Result<()> {
        let schema_file = self.opts.schema_file.clone();
        let db = self.database()?;
        let text = std::fs::read_to_string(&schema_file)?;
        let body = strip_dump_header(&text);
        if body.trim().is_empty() {
            return Err(Error::EmptySchema);
        }

        let driver = self.connect().await?;
        if !driver.databases().contains(db.clone()).await? {
            driver.databases().create(db.clone()).await?;
        }
        schema_queries(driver, &db, &[body.as_str()]).await?;
        println!("Loaded: {}", schema_file.display());
        Ok(())
    }

    pub async fn wait(&mut self, timeout: Duration) -> Result<()> {
        wait_for_server(self.url()?, timeout, self.opts.verbose).await
    }

    pub async fn up(&mut self) -> Result<()> {
        self.create().await?;
        self.migrate().await?;
        Ok(())
    }
}

async fn open_driver(url: &TypeDbUrl) -> Result<TypeDBDriver> {
    let addresses = Addresses::try_from_address_str(url.address())?;
    let credentials = Credentials::new(&url.username, &url.password);
    let tls = if url.tls {
        DriverTlsConfig::enabled_with_native_root_ca()
    } else {
        DriverTlsConfig::disabled()
    };
    Ok(TypeDBDriver::new(addresses, credentials, DriverOptions::new(tls)).await?)
}

async fn wait_for_server(url: &TypeDbUrl, timeout: Duration, verbose: bool) -> Result<()> {
    let start = std::time::Instant::now();
    loop {
        match open_driver(url).await {
            Ok(_) => {
                if verbose {
                    eprintln!("TypeDB available at {}", url.address());
                }
                return Ok(());
            }
            Err(e) => {
                if start.elapsed() >= timeout {
                    return Err(Error::WaitTimeout {
                        address: url.address(),
                        cause: e.to_string(),
                    });
                }
                if verbose {
                    eprintln!("waiting for TypeDB at {} ({e})", url.address());
                }
                tokio::time::sleep(Duration::from_millis(500)).await;
            }
        }
    }
}

async fn apply_up(
    driver: &TypeDBDriver,
    database: &str,
    version: &Version,
    up: &str,
    verbose: bool,
) -> Result<()> {
    // Effect axiom (trusted): on success, abstract State gains `version`.
    // Empty-up rejection is decided in [`pure::plan_migrate`]; keep a guard here.
    if pure::body_is_empty(up) {
        return Err(Error::EmptyUp(version.clone()));
    }
    let applied_at = chrono::Utc::now().format("%Y-%m-%dT%H:%M:%S").to_string();
    let insert = ledger::record_insert(version, &applied_at);
    if verbose {
        eprintln!("-> up {version}");
    }
    schema_queries(driver, database, &[up, insert.as_str()]).await
}

async fn apply_down(
    driver: &TypeDBDriver,
    database: &str,
    version: &Version,
    down: &str,
    verbose: bool,
) -> Result<()> {
    // Effect axiom (trusted): on success, abstract State drops last matching `version`.
    if pure::body_is_empty(down) {
        return Err(Error::EmptyDown {
            version: version.clone(),
            name: String::new(),
        });
    }
    let delete = ledger::record_delete(version);
    if verbose {
        eprintln!("-> down {version}");
    }
    schema_queries(driver, database, &[down, delete.as_str()]).await
}

fn map_plan_error(err: PlanError) -> Error {
    match err {
        PlanError::EmptyUp(v) => Error::EmptyUp(v),
        PlanError::EmptyDown { version, name } => Error::EmptyDown { version, name },
        PlanError::MissingFile(v) => Error::MissingMigrationFile(v),
        PlanError::StrictOrder {
            pending,
            applied_up_to,
        } => Error::StrictOrder {
            pending,
            applied_up_to,
        },
    }
}

fn files_to_specs(files: &[MigrationFile]) -> Vec<pure::MigrationSpec> {
    files
        .iter()
        .map(|f| pure::MigrationSpec {
            version: f.version.clone(),
            name: f.name.clone(),
            up: f.up.clone(),
            down: f.down.clone(),
        })
        .collect()
}

/// Pure planning for migrate (decisions only; TypeDB effects happen in [`execute_plan`]).
pub fn plan_migrate_files(
    files: &[MigrationFile],
    applied: &[Version],
    strict: bool,
) -> Result<Plan> {
    let specs = files_to_specs(files);
    pure::plan_migrate(&specs, applied, strict).map_err(map_plan_error)
}

/// Pure planning for rollback.
pub fn plan_rollback_files(files: &[MigrationFile], applied: &[Version]) -> Result<Plan> {
    let specs = files_to_specs(files);
    pure::plan_rollback(&specs, applied).map_err(map_plan_error)
}

/// Execute a plan against TypeDB. **Trusted effect layer:** success ⇒ abstract
/// [`State`] transition; failure ⇒ ledger unchanged (schema tx abort).
async fn execute_plan(
    driver: &TypeDBDriver,
    database: &str,
    files: &[MigrationFile],
    plan: &[Op],
    verbose: bool,
) -> Result<()> {
    for op in plan {
        match op {
            Op::ApplyUp { version, up } => {
                apply_up(driver, database, version, up, verbose).await?;
                let label = files
                    .iter()
                    .find(|f| &f.version == version)
                    .map(|f| f.label())
                    .unwrap_or_else(|| version.as_str().to_string());
                println!("Applied: {label}");
            }
            Op::ApplyDown { version, down } => {
                apply_down(driver, database, version, down, verbose).await?;
                let label = files
                    .iter()
                    .find(|f| &f.version == version)
                    .map(|f| f.label())
                    .unwrap_or_else(|| version.as_str().to_string());
                println!("Rolled back: {label}");
            }
        }
    }
    Ok(())
}

/// Abstract post-state after a successful plan (for tests / mental model).
pub fn abstract_run(applied: &[Version], plan: &[Op]) -> Result<State> {
    let state = State::new(applied.to_vec());
    pure::run(&state, plan).map_err(|e| match e {
        pure::StepError::EmptyUp(v) => Error::EmptyUp(v),
        pure::StepError::EmptyDown(v) => Error::EmptyDown {
            version: v,
            name: String::new(),
        },
    })
}

/// Resolve a connection URL from CLI / env sources (pure; no process env reads).
///
/// Precedence: `cli_url` → `TYPEDB_URL` → `DATABASE_URL` → built-in default.
pub fn resolve_url_from(
    cli_url: Option<&str>,
    typedb_url: Option<&str>,
    database_url: Option<&str>,
) -> Result<TypeDbUrl> {
    let raw = cli_url
        .map(str::to_string)
        .or_else(|| typedb_url.map(str::to_string))
        .or_else(|| database_url.map(str::to_string))
        .unwrap_or_else(|| "typedb://admin:password@localhost:1729/typedb".into());
    TypeDbUrl::parse(&raw)
}

pub fn resolve_url(cli_url: Option<&str>) -> Result<TypeDbUrl> {
    let typedb = std::env::var("TYPEDB_URL").ok();
    let database = std::env::var("DATABASE_URL").ok();
    resolve_url_from(cli_url, typedb.as_deref(), database.as_deref())
}

pub fn default_migrations_dir() -> PathBuf {
    PathBuf::from(
        std::env::var("TQLMATE_MIGRATIONS_DIR").unwrap_or_else(|_| "db/migrations".into()),
    )
}

pub fn default_schema_file() -> PathBuf {
    PathBuf::from(std::env::var("TQLMATE_SCHEMA_FILE").unwrap_or_else(|_| "db/schema.tql".into()))
}
