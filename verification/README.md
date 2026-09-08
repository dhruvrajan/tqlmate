# Formal verification (Lean 4 / Aeneas)

Machine-checked properties of the **extracted** pure core (`src/pure.rs`) used by
`src/migration.rs` / `src/runner.rs`. Story:

**Rust → Charon → Aeneas → ExtrProperties + CoreProperties**

## What is 100% verified (pure plan + interpreter)

[`lean/TqlmateExtract/CoreProperties.lean`](lean/TqlmateExtract/CoreProperties.lean)
proves properties of the extracted migrate/rollback **decision** core:

| Property | Where |
| --- | --- |
| Migrate pending → `run` appends pending in file order; applied prefix preserved | `plan_migrate_then_run_applies_pending`, `run_pending_plan_grows_applied`, `migrate_preserves_applied_prefix` |
| Idempotent migrate (nothing pending ⇒ empty plan / unchanged) | `plan_migrate_idempotent_when_applied`, `plan_migrate_empty_files`, `run_empty_plan_example` |
| Rollback inverse of one up | `migrate_rollback_roundtrip`, `plan_rollback_after_up`, `run_up_then_down_inverse_example` |
| Empty up/down rejected by plan (and by `step`) | `plan_migrate_rejects_empty_up`, `plan_rollback_rejects_empty_down`, `step_rejects_empty_*` |
| Strict order: pending `< max(applied)` errors | `plan_migrate_strict_order_error`, `plan_migrate_strict_ok_prefix` |
| Rollback missing file / empty applied | `plan_rollback_missing_file`, `plan_rollback_empty_applied_forall` (∀ files), examples |

∀-style lemmas (not fixture-only) include:

- `plan_rollback_empty_applied_forall` — empty applied ⇒ empty plan for **any** file slice
- `step_rejects_empty_up_forall` / `step_rejects_empty_down_forall` — empty bodies rejected for **any** state/version when `body_is_empty` holds

Parse/split/slugify fixtures remain in
[`ExtrProperties.lean`](lean/TqlmateExtract/ExtrProperties.lean) (`native_decide`),
mirrored by `tests/spec_parity.rs`.

## What is assumed (effect axioms / FunsExternal / TypeDB)

**Not proved** (trusted / axiomatized):

1. **Effect layer** (`src/runner.rs` `execute_plan` / `apply_up` / `apply_down`, ledger TypeQL):
   - If a TypeDB schema transaction for `ApplyUp { v, up }` succeeds
     (`[up, record_insert]` atomic), the abstract `State` transition
     `step(_, ApplyUp)` happened (version appended).
   - If a transaction for `ApplyDown { v, down }` succeeds
     (`[down, record_delete]`), the abstract `step(_, ApplyDown)` happened
     (last matching version removed).
   - If a transaction fails / aborts, the abstract `State` is unchanged.
2. **FunsExternal** — hand-filled models of Rust/`alloc` primitives Aeneas does
   not generate (`str`/`String` ops, `PartialOrd`, etc.). Wrong models would
   invalidate extract proofs.
3. **Filesystem / CLI / URL / Docker** — listing `.tql` files, clap, TypeDB
   driver, network: outside the pure core.

Honest claim: **core functional correctness under effect assumptions** — Lean
checks plan+`run` on the Aeneas extract; TypeDB is an oracle matching those
ops when effects succeed.

## Architecture

```
CLI / Runner (trusted effects)
  list files + read applied
       │
       ▼
  pure::plan_migrate / plan_rollback   ← verified decisions
       │
       ▼
  execute_plan (TypeDB schema txs)     ← effect axioms
```

Abstract interpreter: `State { applied }` with `step` / `run` over `Op`
(`ApplyUp` / `ApplyDown`).

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

Re-check `ExtrProperties.lean` / `CoreProperties.lean` if the extract shape changes.
