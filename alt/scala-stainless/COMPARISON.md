# Rust+Verus vs Scala+Stainless — comparison (prototype)

Honest side-by-side for the migrate/rollback **decision core** and a thin CLI.
This Scala tree is an experiment under `alt/scala-stainless/`; production remains Rust.

## Lines of code

| Surface | Rust | Scala (this prototype) |
| --- | --- | --- |
| Pure / verified core | `src/pure.rs` ~1043 LOC (runtime+Aeneas) + `verification/verus` ~739 LOC | `verified/.../{Codes,Pure,Lemmas}.scala` **521 LOC** |
| CLI / effects / I/O | `cli`+`runner`+`migration`+`url`+`ledger`+`main` ~1266 LOC | `cli/` ~942 LOC (+ ~150 LOC runtime-shim) |
| Proof annotation density | High in Verus crate (`ensures`/`decreases`/`proof { }` blocks; many loop invariants) | Medium: `require`/`ensuring`/`decreases`/`@induct`/`check` — less boilerplate than Verus loops |

Scala core is smaller because (1) Stainless `List` already carries size lemmas, (2) parse/split stay in the unverified CLI, (3) versions are `List[BigInt]` codes rather than full String machinery.

## What each prover covered

| Property | Verus | Stainless (this) | Lean/Aeneas |
| --- | --- | --- | --- |
| `step` ApplyUp/Down postconditions | yes | **yes** | yes |
| `run` nil | yes | **yes** | yes |
| `run` ↔ full fold spec (arbitrary plans) | **MISSING** (documented) | **MISSING** (same honesty) | yes (`run_cons`) |
| `remove_last_matching` | yes + lemmas | **yes** + lemmas | yes |
| Empty rollback ∀ files | yes | **yes** | yes |
| Idempotent migrate when up-to-date | fixtures / by construction | **lemma** `migrateIdempotentWhenFullyApplied` | fixtures + ∀ table |
| Round-trip up/down | yes | **yes** | yes |
| Strict-order planning | partial (`version_str_lt` external) | codesLt proved | yes |
| Parse / split / slugify | no (Lean ExtrProperties) | **no** (CLI) | yes (fixtures) |

**Stainless proved that Verus did not (in this repo):** lexicographic `codesLt` / `codesEq` on version codes without an `external_body` string Ord; idempotence lemma stated as `.holds` with `@induct` pending-empty proof.

**Verus / Lean proved that Stainless did not:** parse/split/slugify fixtures; Lean’s fuller `run_cons` ∀; Verus’s ASCII-string emptiness tied to `str@` views (Stainless used code lists instead).

## Spec ergonomics

**Verus** (representative):

```rust
pub fn step(state: State, op: Op) -> (r: Result<State, StepError>)
    requires op_bodies_ascii(op),
    ensures match op {
        Op::ApplyUp { version, up } => { /* … */ },
        Op::ApplyDown { version, down } => { /* … */ },
    },
```

Loop invariants and `proof { assert … }` blocks are frequent; `version_str_lt` is `#[verifier::external_body]`.

**Stainless** (representative):

```scala
def step(state: State, op: Op): Either[StepError, State] = {
  op match {
    case ApplyUp(version, up) =>
      if (bodyIsEmpty(up)) Left(EmptyUp(version))
      else Right(State(state.applied :+ version))
    case ApplyDown(version, down) =>
      if (bodyIsEmpty(down)) Left(EmptyDown(version))
      else Right(State(removeLastMatching(state.applied, version)))
  }
}.ensuring(res => stepPost(state, op, res))
```

Specs read like ordinary Scala. `@induct` lemmas and `check(...)` are lighter than Verus ghost blocks, but Stainless’s `String` story is weaker — hence the `List[BigInt]` encoding.

## Verifier speed

| | Verus (CI script) | Stainless 0.10.3 (local) |
| --- | --- | --- |
| Typical core check | tens of seconds (`--rlimit 80`) | **~7 s wall**, ~0.5 s solver (warm cache); 158 VCs |
| Tooling install | download Verus binary | ~120 MB `stainless-dotty-standalone` zip |

## Binary size & startup

Measured on this Linux x86_64 VM (2026-10-18):

| Artifact | Size | `--help` startup |
| --- | --- | --- |
| Scala GraalVM native-image | **~44 MB** (embeds TypeDB JNI `.so`) | **~4–6 ms** |
| Scala assembly JAR | **~41 MB** | **~236 ms** (JVM) |
| Rust `tqlmate` release | typically **~10–20 MB** class of static Rust bins (not rebuilt here: local Cargo lacks edition2024) | typically low-ms |

Native-image startup is competitive with Rust for offline commands. Image size is larger because of embedded JNI + SubstrateVM.

## Build complexity

| | Rust | Scala prototype |
| --- | --- | --- |
| Day-to-day build | `cargo build --release` | `scala-cli package` / `build-native.sh` |
| Verification | Verus + Lean/Aeneas (two CI jobs) | Stainless only for this alt |
| Native dist | cargo / cross | GraalVM native-image + **uncompressed JNI companion jar** |
| Driver | `typedb-driver` crate | Java driver 3.13.6 from `repo.typedb.com` |

## Gotchas

1. **Stainless `String`:** Prefer ADT/`List[BigInt]` for proofs; bridge to JVM `String` in unverified code.
2. **GraalVM + TypeDB JNI:** Fat-JAR DEFLATE `.so` entries are skipped by native-image; `build-native.sh` adds a ZIP_STORED companion jar. Agent-generated JNI/reflect configs live under `native-image/`.
3. **Runtime shim:** JVM compile uses a tiny `runtime-shim/stainless/{collection,lang,annotation}` stand-in; Stainless verification uses the real Stainless library from the standalone distribution.
4. **Docker smoke:** This VM had **no Docker**; TypeDB container smoke test was **not** run. Native binary was checked through driver init (connection refused to localhost:1729), proving JNI unpack+load works.
5. **Existing CI:** Untouched. Opt-in workflow only: `.github/workflows/scala-stainless.yml`.

## Takeaways

- Stainless can match the **Verus-class migrate/rollback ensures** on a Scala port of the pure core with less annotation noise, at the cost of reshaping data (`Codes`) and leaving parse proofs out.
- Shipping a **real TypeDB client** as a single native binary is feasible with GraalVM, but JNI resource packaging is the main sharp edge (far more fiddly than `cargo build --release`).
- For production, Rust+Verus remains the better default (smaller binary story, existing Lean parity, mature CLI). Scala+Stainless is a credible **research / comparison** track.
