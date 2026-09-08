# tqlmate

dbmate-style migration CLI for TypeDB 3.x.

## Install

```bash
cargo install tqlmate
```

From a checkout:

```bash
cargo install --path .
# or
cargo build --release   # target/release/tqlmate
```

Requires a TypeDB 3.x server. Default credentials match TypeDB CE (`admin` / `password`).

## URL

```
typedb://[user:pass@]host[:port]/database
typedb://admin:password@localhost:1729/typedb          # default
typedb://localhost:1729/mydb                           # user:pass defaults to admin/password
typedb://localhost/mydb                                # port defaults to 1729
typedb://admin:password@localhost:1729/typedb?tls=true
```

The database is always required — `create` and `drop` act on whatever it names,
so it is never guessed. `new` writes a file locally and needs no URL at all.

Set via `--url` / `-u`, or `TYPEDB_URL` (alias `DATABASE_URL`). Optional `.env` via `--env-file`.

## Commands

| Command | What it does |
|---------|----------------|
| `new <name>` | Create timestamped migration under `db/migrations` |
| `up` | Create database + run pending migrations |
| `create` / `drop` | Create or delete the database |
| `migrate` | Apply pending migrations |
| `rollback` (`down`) | Roll back the latest applied migration |
| `status` | List applied / pending (`--exit-code`, `--quiet`) |
| `dump` | Write live schema to `db/schema.tql` |
| `load` | Load `db/schema.tql` into the database |
| `wait` | Block until TypeDB accepts connections |

Useful flags: `-d/--migrations-dir`, `--schema-file`, `--wait <secs>`, `--strict`, `-v/--verbose`.

## Example

```bash
export TYPEDB_URL='typedb://admin:password@localhost:1729/app'

tqlmate new create_person
# edit db/migrations/*_create_person.tql

tqlmate up
tqlmate status
tqlmate dump
```

Migration file shape:

```typeql
-- migrate:up
define
  entity person, owns name;
  attribute name, value string;

-- migrate:down
undefine
  owns name from person;
  person;
  name;
```

Each up/down runs in one **SCHEMA** transaction together with the ledger write (`_tqlmate_`-prefixed types). If the migration query fails, the transaction is closed and the version is **not** recorded.

`--strict` refuses pending migrations whose version is lower than an already-applied version.

## Notes

- `dump` uses `Database::schema()` (TypeQL `define` text) and prepends applied versions as comments.
- `load` strips those header comments and runs the remainder as one schema query. Prefer `migrate` for incremental changes; `load` is for bootstrapping from a dump.
- **Ledger schema** (`_tqlmate_*` types) is versioned and shipped inside the binary as `src/ledger/migrations/*.tql`. On `ensure` / before user `migrate`, pending ledger migrations apply in order and are recorded with reserved versions `00000000000001`–`00000000999999` (14 digits, eight leading zeros) so they never collide with user `YYYYMMDDHHMMSS` files under `db/migrations`. Ledger upgrades are forward-only in the CLI; each shipped file still needs a real non-empty `-- migrate:down`. To evolve the ledger in a release: add the next zero-padded file under `src/ledger/migrations/`, register it in `EMBEDDED_LEDGER_MIGRATIONS` in `src/ledger/mod.rs`, and ship. **Never remove or renumber** shipped ledger files.
- **Unit** (under `tests/`, next to the Docker suite): `url.rs`, `migration.rs`, `ledger.rs`, `cli.rs`, `spec_parity.rs`. Offline:
  `cargo test --no-default-features --test url --test migration --test ledger --test cli --test spec_parity`
  These must not open TypeDB or Docker. `spec_parity` locks Lean ExtrProperties fixtures to `src/pure.rs` outputs.
- **Formal verification** ([`verification/`](verification/)): Charon+Aeneas extract
  [`src/pure.rs`](src/pure.rs) → `verification/lean/aeneas-generated/`. CI `lake build`
  depends on the Aeneas Lean package and elaborates that extract, proving key properties
  on the **extracted** functions (`ExtrProperties`, Lean **v4.31.0**).
  Release binaries do not need Lean/Charon/Aeneas. See [`verification/README.md`](verification/README.md).
- **Integration** (`tests/typedb_docker.rs` only, feature `typedb-docker`, on by default): TypeDB via [testcontainers](https://testcontainers.com/) (`typedb/typedb:3.12.3`). Requires Docker; fails loudly if unavailable (no silent skip).
- CI (`.github/workflows/ci.yml`, GitHub-hosted runners): jobs `unit` → `integration`, plus parallel `lint`, `verify` (Lean), and `package` (`cargo publish --dry-run`).
- Release: pushing a `v*` tag runs `.github/workflows/release.yml` — unit tests, then cross-platform binaries, then a GitHub Release with those archives attached and a `cargo publish` to crates.io (`CARGO_REGISTRY_TOKEN` secret). Releases are cut from GitHub only, never from a laptop.
