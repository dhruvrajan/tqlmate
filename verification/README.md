# Formal verification (Aeneas + Lean 4)

This directory verifies the **pure** migration/ledger algorithm in
[`src/pure.rs`](../src/pure.rs) (version parsing, up/down split, status /
strict-order, slugify, dump header helpers). No TypeDB driver, async, or
filesystem I/O is in scope.

## Toolchain: Aeneas (preferred) — why not Verus

We used **Aeneas** (Rust → Charon LLBC → Lean 4), not Verus:

1. Charon `--preset=aeneas` successfully extracts
   [`verification/extract`](extract/) (thin crate that path-includes
   `src/pure.rs`).
2. Aeneas translates that LLBC to Lean (`aeneas-generated/`). A few
   `str`/`fmt` helpers remain as axioms in `FunsExternal.lean` (Aeneas std
   coverage gap); the algorithmic bodies extract cleanly after rewriting
   the Rust away from unsupported APIs (`strip_suffix`, nested `return` in
   loops, etc.).
3. Machine-checked properties are proved in Lean on
   [`TqlmateExtract.Spec`](lean/TqlmateExtract/Spec.lean), a readable model
   of the same algorithm (pinned Lean **v4.31.0**, matching Aeneas’s
   `backends/lean/lean-toolchain`).

Verus was **not** needed as a fallback.

### Pins

| Component | Version |
|-----------|---------|
| Lean 4 | `leanprover/lean4:v4.31.0` ([`lean/lean-toolchain`](lean/lean-toolchain)) |
| Aeneas | `33e3b2b4a5b7fa734fe8bb1282ebad066b38d049` |
| Charon | `f0785b40f11dabae831fad31f819a473f19e4dfb` (Aeneas `charon-pin`) |

## Proven properties

| Theorem | Meaning |
|---------|---------|
| `pending_applied_disjoint_true` | Status tags are consistent: Applied iff version ∈ applied (so pending ∩ applied = ∅) |
| `checkStrictOrder_empty_applied` | No applied versions ⇒ strict order OK |
| `parse_rejects_*` | Bad filenames rejected (extension / digits / name / underscore) |
| `parse_ok_example` | Happy-path `VERSION_name.tql` parse |
| `split_rejects_*` / `split_ok_*` | Marker rules for `-- migrate:up` / `down` (incl. case-insensitive) |
| `strict_order_detects_hole` / `strict_order_ok_prefix` | Strict order catches holes below max(applied) |
| `slugify_examples` | Slugify normalization |
| `dump_strip_roundtrip` | Dump header + strip round-trip |

CI runs `lake build` in `verification/lean` (Lean only — **not** required to build the release binary).

## Reproduce

### Prove (CI path)

```bash
# Install elan: https://lean-lang.org/lean4/doc/setup.html
cd verification/lean
lake build
```

### Re-extract Rust → Lean with Charon + Aeneas (optional)

Requires building Charon + Aeneas from the pins above (OCaml 5.3 + the
nightly listed in Charon’s `rust-toolchain`). Then:

```bash
./verification/scripts/extract-aeneas.sh
```

Release / `cargo build --release` never depends on Lean, Charon, or Aeneas.
