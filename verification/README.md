# Formal verification (Lean 4 / Aeneas)

Machine-checked properties of the **extracted** pure core (`src/pure.rs`) used by
`src/migration.rs` and `src/ledger/`. Story:

**Rust → Charon → Aeneas → ExtrProperties**

## What is proved

[`lean/TqlmateExtract/ExtrProperties.lean`](lean/TqlmateExtract/ExtrProperties.lean)
states the same fixtures as `tests/spec_parity.rs` against Aeneas-generated
[`lean/aeneas-generated/Funs.lean`](lean/aeneas-generated/Funs.lean) (`Result.reducesTo` +
`native_decide`):

- version/name parse ok and reject cases
- migrate up/down marker split (including case-insensitive)
- strict-order hole detection and ok prefixes
- pending ∩ applied disjointness on a small set
- slugify examples

`tests/spec_parity.rs` mirrors those fixtures (plus dump header / strip round-trip on the Rust pure helpers).

Hand-filled externals live in
[`lean/TqlmateExtract/FunsExternal.lean`](lean/TqlmateExtract/FunsExternal.lean)
(Aeneas’s generated `FunsExternal*.lean` copies are discarded after extract).

`Types.lean` / `Funs.lean` under `lean/TqlmateExtract/` are symlinks into
`aeneas-generated/`.

## Pins

See [`VERSIONS`](VERSIONS). Lake requires Aeneas at the pinned commit
(`backends/lean`); that pulls Mathlib. CI runs `lake update` then `lake exe cache get`.

## Regenerating the extract

Requires Charon + Aeneas on `PATH` (see `VERSIONS`). From the repo root:

```bash
./verification/scripts/extract-aeneas.sh
```

Then:

```bash
cd verification/lean && lake update && lake exe cache get && lake build
```

Re-check examples in `ExtrProperties.lean` if the extract shape changes.
