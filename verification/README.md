# Formal verification (Lean 4 / Aeneas)

Machine-checked properties of the **extracted** pure core (`src/pure.rs`) used by
`src/migration.rs` / `src/runner.rs`. Story:

**Rust → Charon → Aeneas → ExtrProperties + CoreProperties**

## What is verified (pure plan + interpreter)

[`lean/TqlmateExtract/CoreProperties.lean`](lean/TqlmateExtract/CoreProperties.lean)
proves properties of the extracted migrate/rollback **decision** core.

### ∀ / inductive theorems (on the extract)

| Claim | Theorem |
| --- | --- |
| `run s [] = Ok s` | `run_nil`, `run_nil_of_empty` |
| `run s (op::rest) = step s op >>= run · rest` | `run_cons`, `run_singleton` |
| ApplyUp nonempty ⇒ `applied' = applied ++ [v]` | `step_apply_up_ok` |
| ApplyUp / ApplyDown empty body ⇒ Err | `step_apply_up_err`, `step_apply_down_err` |
| ApplyDown nonempty ⇒ `remove_last_matching` | `step_apply_down_ok` |
| `remove_last_matching [] v = []`; `[v]` match ⇒ `[]` | `remove_last_matching_nil`, `remove_last_matching_singleton` |
| Empty applied ⇒ empty rollback (∀ files) | `plan_rollback_empty_forall` |
| Empty pending ⇒ empty ups | `plan_ups_from_pending_nil` |
| Nonstrict migrate = `pending_specs` ≫ `plan_ups_from_pending` | `plan_migrate_nonstrict_eq` |
| Strict migrate maps `check_strict_order_specs` Err → `StrictOrder` | `plan_migrate_strict_maps_error` |
| Nonempty rollback = last-version lookup / MissingFile / EmptyDown / ApplyDown | `plan_rollback_nonempty_eq` |
| ∀ nonempty up/down: empty → ApplyUp → ApplyDown → empty | `roundtrip_up_down` |
| One ApplyUp appends version (`run` ∘ `step`) | `run_one_apply_up_appends` |

`remove_last_matching` is recursive from the end (Rust): if the last element equals
`v`, return the prefix; otherwise recurse on the prefix and push the last element
back (absent `v` ⇒ unchanged clone).

### Regression fixtures (`native_decide` only)

These lock concrete extract shapes; they are **not** a substitute for the ∀ table:

`plan_migrate_then_run_applies_pending`, `run_pending_plan_grows_applied`,
`plan_migrate_idempotent_when_applied`, `plan_migrate_rejects_empty_up`,
`plan_rollback_rejects_empty_down`, `plan_migrate_strict_order_error`,
`plan_migrate_strict_ok_prefix`, `plan_rollback_missing_file`,
`plan_rollback_after_up`, `migrate_rollback_roundtrip`,
`step_apply_up_example`, `step_apply_down_removes_last`, etc.

Parse/split/slugify fixtures remain in
[`ExtrProperties.lean`](lean/TqlmateExtract/ExtrProperties.lean), mirrored by
`tests/spec_parity.rs`.

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
(`ApplyUp` / `ApplyDown`). Proof-oriented helpers: `pending_specs`,
`plan_ups_from_pending`, recursive `remove_last_matching`, recursive `run`.

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
