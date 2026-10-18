# tqlmate — Scala 3 + Stainless prototype

**Experiment only — not for merge into the production Rust CLI.**

This tree ports the pure migrate/rollback plan+interpreter core to a
Stainless-verifiable Scala 3 subset, with a thin CLI that uses the official
**TypeDB Java driver 3.13.6**, and a GraalVM **native-image** distribution.

## Layout

| Path | Role |
| --- | --- |
| `verified/src/tqlmate/core/` | Stainless-checked core (`Codes`, `Pure`, `Lemmas`) |
| `runtime-shim/stainless/` | Minimal Stainless API stand-ins for JVM compile |
| `cli/` | Unverified CLI + TypeDB driver + String↔codes bridge |
| `resources/ledger/` | Embedded ledger init migration |
| `native-image/` | GraalVM JNI/resource config (from `native-image-agent`) |
| `scripts/verify.sh` | Download Stainless + verify |
| `build-native.sh` | Assembly JAR + native-image |
| `COMPARISON.md` | Side-by-side with Rust+Verus |
| `verified/VERIFICATION.md` | VC table + assumptions |

## Verify

```bash
./scripts/verify.sh
```

Expect **158/158** VCs valid (see `verified/stainless-report.txt`).

## Run (JVM)

```bash
# from this directory's parent (repo root):
./build-native.sh   # also builds the JAR
java -jar dist/tqlmate-scala.jar --help
java -jar dist/tqlmate-scala.jar new create_person
```

Requires JDK 21+ and network access to `repo.typedb.com` for the driver.

## Native binary (GraalVM)

```bash
# JAVA_HOME must point at GraalVM 21+ with native-image
./build-native.sh
./dist/tqlmate-scala --help
```

**Why GraalVM, not Scala Native:** TypeDB's Java driver needs JNI shared
libraries. GraalVM embeds them; Scala Native cannot load those artifacts.

**Gotcha:** GraalVM skips large DEFLATE-compressed `.so` entries inside the fat
JAR. `build-native.sh` builds a ZIP_STORED companion
`dist/typedb-jni-linux-x86_64.jar` and puts it on the native-image classpath.

## TypeDB

Uses `com.typedb:typedb-driver:3.13.6` from
`https://repo.typedb.com/public/public-release/maven/`.

Commands mirror the Rust CLI where practical: `new`, `up`, `create`, `drop`,
`migrate`, `rollback`/`down`, `status`, `dump`, `load`, `wait`, plus
`--url`, `--migrations-dir`, `--schema-file`, `--strict`, `--wait`, `--verbose`.

## CI

Opt-in workflow: `.github/workflows/scala-stainless.yml`
(`workflow_dispatch` + path filter on `alt/scala-stainless/**`). Does **not**
alter existing Rust CI jobs.
