# Formal verification (Aeneas + Lean 4)

Scope: the **pure** migration/ledger algorithm in [`src/pure.rs`](../src/pure.rs)
(version parsing, up/down split, status / strict-order, slugify, dump header).
No TypeDB driver, async, or filesystem I/O.

## What is actually machine-checked today

Be precise — these are three related artefacts, not one claim:

| Layer | Artefact | What CI / `lake build` does |
|-------|----------|------------------------------|
| **(a) Extraction** | Charon + Aeneas translate `src/pure.rs` → [`lean/aeneas-generated/`](lean/aeneas-generated/) (`Types.lean`, `Funs.lean`, `FunsExternal_Template.lean`, …) | **Not** typechecked in CI. Kept as a regeneration artefact (`scripts/extract-aeneas.sh`). Paths under `aeneas-generated/` are marked `linguist-generated` in `.gitattributes` — **do not hand-edit**; regenerate instead. Uncovered `str`/`fmt` helpers sit as axioms in `FunsExternal.lean`. |
| **(b) Spec proofs** | Readable Lean model [`TqlmateExtract.Spec`](lean/TqlmateExtract/Spec.lean) + theorems in [`Properties.lean`](lean/TqlmateExtract/Properties.lean) | **`lake build` checks these.** This is the machine-checked property layer. |
| **(c) Refinement** | Spec ↔ Aeneas `Funs` ↔ Rust | **Future work.** Not claimed. |

So: CI does **not** prove theorems about Aeneas-generated `Funs.lean`, and does **not** by itself mean “the Rust binary was verified.” It proves properties of the Spec model. Drift between Spec and Rust is guarded by **parity fixtures** (below).

## Parity with Rust

[`tests/spec_parity.rs`](../tests/spec_parity.rs) embeds the same concrete vectors as the
`native_decide` examples in `Properties.lean` (`parse_ok_example`, `split_ok_*`,
`strict_order_*`, `slugify_examples`, `dump_strip_roundtrip`, plus the reject cases).
Both sides must stay in lockstep when examples change.

```bash
cargo test --no-default-features --test spec_parity
```

## Toolchain: Aeneas (preferred) — why not Verus

1. Charon `--preset=aeneas` extracts [`verification/extract`](extract/) (thin crate that path-includes `src/pure.rs`).
2. Aeneas emits Lean under `aeneas-generated/` (see (a) above).
3. Properties are proved on Spec (b), with Rust parity tests for the example tables.

Verus was not used as a fallback.

### Pins

| Component | Version |
|-----------|---------|
| Lean 4 | `leanprover/lean4:v4.31.0` ([`lean/lean-toolchain`](lean/lean-toolchain)) |
| Aeneas | `33e3b2b4a5b7fa734fe8bb1282ebad066b38d049` |
| Charon | `f0785b40f11dabae831fad31f819a473f19e4dfb` (Aeneas `charon-pin`) |

Also listed in [`VERSIONS`](VERSIONS).

## Spec theorems (`lake build`)

| Theorem | Meaning |
|---------|---------|
| `pending_applied_disjoint_true` | Status tags consistent: Applied iff version ∈ applied (pending ∩ applied = ∅) |
| `checkStrictOrder_empty_applied` | No applied versions ⇒ strict order OK |
| `parse_rejects_*` | Bad filenames rejected (extension / digits / name / underscore) |
| `parse_ok_example` | Happy-path `VERSION_name.tql` parse |
| `split_rejects_*` / `split_ok_*` | Marker rules for `-- migrate:up` / `down` (incl. case-insensitive) |
| `strict_order_detects_hole` / `strict_order_ok_prefix` | Strict order catches holes below max(applied) |
| `slugify_examples` | Slugify normalization |
| `dump_strip_roundtrip` | Dump header + strip round-trip |

Release / `cargo build --release` never depends on Lean, Charon, or Aeneas.

## Reproduce

### Prove Spec (CI path)

```bash
# Install elan: https://lean-lang.org/lean4/doc/setup.html
cd verification/lean
lake build
```

### Re-extract Rust → Lean with Charon + Aeneas (optional, not CI)

Requires building Charon + Aeneas from the pins above (OCaml 5.3 + the
nightly in Charon’s `rust-toolchain`). Then:

```bash
./verification/scripts/extract-aeneas.sh
```
