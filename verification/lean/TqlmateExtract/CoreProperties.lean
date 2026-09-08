import Aeneas
import TqlmateExtract.Funs

/-!
# Core migrate/rollback properties (extracted `pure.*`)

∀-style lemmas on planning + the abstract ledger interpreter, plus extract
fixtures aligned with Rust `pure` tests. TypeDB effects are **assumed**
(see `verification/README.md`).
-/

open Aeneas Aeneas.Std Result
open tqlmate_extract

namespace TqlmateExtract.CoreProperties

private instance : BEq pure.PlanError where
  beq
    | .EmptyUp a, .EmptyUp b => a == b
    | .EmptyDown a n, .EmptyDown b m => a == b && n == m
    | .MissingFile a, .MissingFile b => a == b
    | .StrictOrder a b, .StrictOrder c d => a == c && b == d
    | _, _ => false

private instance : BEq pure.StepError where
  beq
    | .EmptyUp a, .EmptyUp b => a == b
    | .EmptyDown a, .EmptyDown b => a == b
    | _, _ => false

private instance : BEq pure.Op where
  beq
    | .ApplyUp v u, .ApplyUp v' u' => v == v' && u == u'
    | .ApplyDown v d, .ApplyDown v' d' => v == v' && d == d'
    | _, _ => false

private instance : BEq pure.State where
  beq a b := a.applied.val == b.applied.val

private instance {α β} [BEq α] [BEq β] : BEq (core.result.Result α β) where
  beq
    | .Ok a, .Ok b => a == b
    | .Err e, .Err f => e == f
    | _, _ => false

private def sliceOf {α} (xs : List α)
    (h : xs.length ≤ Usize.max := by native_decide) : Slice α :=
  Slice.from xs h

private def vecOf {α} (xs : List α)
    (h : xs.length ≤ Usize.max := by native_decide) : alloc.vec.Vec α :=
  alloc.vec.Vec.from xs h

private def mspec (version nm up down : String) : pure.MigrationSpec :=
  { version := version, «name» := nm, up := up, down := down }

private def st (xs : List pure.Version)
    (h : xs.length ≤ Usize.max := by native_decide) : pure.State :=
  { applied := vecOf xs h }

/-! ## ∀-style lemmas on the extract -/

/-- For every file list, rollback with empty `applied` yields an empty plan. -/
theorem plan_rollback_empty_applied_forall (files : Slice pure.MigrationSpec) :
    pure.plan_rollback files (sliceOf ([] : List pure.Version))
      ⦃ r => r = core.result.Result.Ok (alloc.vec.Vec.new pure.Op) ⦄ := by
  unfold pure.plan_rollback sliceOf
  simp [core.slice.Slice.is_empty, Slice.from, Slice.len, Slice.val]
  -- Empty `ListN` coerces to `[]`, so the `is_empty` branch is taken.
  have hnil :
      (Data.ListN.ListN.fromList ([] : List pure.Version)).toList = [] := rfl
  simp [hnil]

/-- If `body_is_empty up` is `ok true`, every `ApplyUp` is rejected. -/
theorem step_rejects_empty_up_forall (s : pure.State) (v : pure.Version)
    (up : String)
    (hEmpty : pure.body_is_empty (stringToStr up) = ok true) :
    pure.step s (pure.Op.ApplyUp v up)
      ⦃ r => r = core.result.Result.Err (pure.StepError.EmptyUp v) ⦄ := by
  unfold pure.step
  simp [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, hEmpty,
        pure.Version.Insts.CoreCloneClone.clone,
        alloc.string.String.Insts.CoreCloneClone.clone]

/-- If `body_is_empty down` is `ok true`, every `ApplyDown` is rejected. -/
theorem step_rejects_empty_down_forall (s : pure.State) (v : pure.Version)
    (down : String)
    (hEmpty : pure.body_is_empty (stringToStr down) = ok true) :
    pure.step s (pure.Op.ApplyDown v down)
      ⦃ r => r = core.result.Result.Err (pure.StepError.EmptyDown v) ⦄ := by
  unfold pure.step
  simp [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, hEmpty,
        pure.Version.Insts.CoreCloneClone.clone,
        alloc.string.String.Insts.CoreCloneClone.clone]

/-- Empty string is an empty migration body. -/
theorem body_is_empty_nil :
    (pure.body_is_empty (toStr "")).reducesTo true := by
  native_decide

/-- Non-empty `"u"` is not an empty migration body. -/
theorem body_is_empty_u :
    (pure.body_is_empty (toStr "u")).reducesTo false := by
  native_decide

/-- Concrete empty-up rejection (feeds `step_rejects_empty_up_forall`). -/
theorem step_rejects_empty_up_string_example :
    (pure.step (st []) (pure.Op.ApplyUp "v" "")).reducesTo
      (core.result.Result.Err (pure.StepError.EmptyUp "v")) := by
  native_decide

/-! ## Interpreter fixtures -/

theorem step_apply_up_example :
    (pure.step (st []) (pure.Op.ApplyUp "1" "define x;")).reducesTo
      (core.result.Result.Ok (st ["1"])) := by
  native_decide

theorem step_apply_down_removes_last :
    (pure.step (st ["1", "2", "1"]) (pure.Op.ApplyDown "1" "undefine;")).reducesTo
      (core.result.Result.Ok (st ["1", "2"])) := by
  native_decide

theorem step_rejects_empty_up_example :
    (pure.step (st ["1"]) (pure.Op.ApplyUp "2" "")).reducesTo
      (core.result.Result.Err (pure.StepError.EmptyUp "2")) := by
  native_decide

theorem step_rejects_empty_down_example :
    (pure.step (st ["1"]) (pure.Op.ApplyDown "1" "")).reducesTo
      (core.result.Result.Err (pure.StepError.EmptyDown "1")) := by
  native_decide

theorem run_empty_plan_example :
    (pure.run (st ["1", "2"]) (sliceOf ([] : List pure.Op))).reducesTo
      (core.result.Result.Ok (st ["1", "2"])) := by
  native_decide

theorem run_singleton_up_example :
    (pure.run (st []) (sliceOf [pure.Op.ApplyUp "1" "u"])).reducesTo
      (core.result.Result.Ok (st ["1"])) := by
  native_decide

theorem run_up_then_down_inverse_example :
    (pure.run (st ["0"])
      (sliceOf [pure.Op.ApplyUp "1" "u", pure.Op.ApplyDown "1" "d"])).reducesTo
      (core.result.Result.Ok (st ["0"])) := by
  native_decide

/-! ## Migrate pending / idempotent -/

theorem plan_migrate_idempotent_when_applied :
    (pure.plan_migrate
      (sliceOf [mspec "1" "a" "u1" "d1", mspec "2" "b" "u2" "d2"])
      (sliceOf ["1", "2"])
      false).reducesTo
      (core.result.Result.Ok (vecOf ([] : List pure.Op))) := by
  native_decide

theorem plan_migrate_empty_files :
    (pure.plan_migrate
      (sliceOf ([] : List pure.MigrationSpec))
      (sliceOf ["1"])
      true).reducesTo
      (core.result.Result.Ok (vecOf ([] : List pure.Op))) := by
  native_decide

theorem plan_migrate_then_run_applies_pending :
    (pure.plan_migrate
      (sliceOf [mspec "1" "a" "u1" "d1", mspec "2" "b" "u2" "d2",
        mspec "3" "c" "u3" "d3"])
      (sliceOf ["1"])
      false).reducesTo
      (core.result.Result.Ok (vecOf [
        pure.Op.ApplyUp "2" "u2",
        pure.Op.ApplyUp "3" "u3"])) := by
  native_decide

theorem run_pending_plan_grows_applied :
    (pure.run (st ["1"])
      (sliceOf [pure.Op.ApplyUp "2" "u2", pure.Op.ApplyUp "3" "u3"])).reducesTo
      (core.result.Result.Ok (st ["1", "2", "3"])) := by
  native_decide

/-! ## Empty up/down rejected by plan -/

theorem plan_migrate_rejects_empty_up :
    (pure.plan_migrate
      (sliceOf [mspec "1" "a" "" "d1"])
      (sliceOf ([] : List pure.Version))
      false).reducesTo
      (core.result.Result.Err (pure.PlanError.EmptyUp "1")) := by
  native_decide

theorem plan_rollback_rejects_empty_down :
    (pure.plan_rollback
      (sliceOf [mspec "1" "a" "u1" ""])
      (sliceOf ["1"])).reducesTo
      (core.result.Result.Err (pure.PlanError.EmptyDown "1" "a")) := by
  native_decide

/-! ## Strict order -/

theorem plan_migrate_strict_order_error :
    (pure.plan_migrate
      (sliceOf [mspec "1" "a" "u1" "d1", mspec "2" "b" "u2" "d2",
        mspec "3" "c" "u3" "d3"])
      (sliceOf ["1", "3"])
      true).reducesTo
      (core.result.Result.Err (pure.PlanError.StrictOrder "2" "3")) := by
  native_decide

theorem plan_migrate_strict_ok_prefix :
    (pure.plan_migrate
      (sliceOf [mspec "1" "a" "u1" "d1", mspec "2" "b" "u2" "d2"])
      (sliceOf ["1"])
      true).reducesTo
      (core.result.Result.Ok (vecOf [pure.Op.ApplyUp "2" "u2"])) := by
  native_decide

/-! ## Rollback edges + inverse -/

theorem plan_rollback_empty_applied_example :
    (pure.plan_rollback
      (sliceOf [mspec "1" "a" "u1" "d1"])
      (sliceOf ([] : List pure.Version))).reducesTo
      (core.result.Result.Ok (vecOf ([] : List pure.Op))) := by
  native_decide

theorem plan_rollback_missing_file :
    (pure.plan_rollback
      (sliceOf ([] : List pure.MigrationSpec))
      (sliceOf ["9"])).reducesTo
      (core.result.Result.Err (pure.PlanError.MissingFile "9")) := by
  native_decide

theorem plan_rollback_after_up :
    (pure.plan_rollback
      (sliceOf [mspec "1" "a" "u1" "d1"])
      (sliceOf ["1"])).reducesTo
      (core.result.Result.Ok (vecOf [pure.Op.ApplyDown "1" "d1"])) := by
  native_decide

/-- Compose migrate → run → rollback → run restores the empty ledger. -/
theorem migrate_rollback_roundtrip :
    (pure.run (st [])
      (sliceOf [pure.Op.ApplyUp "1" "u1"])).reducesTo
      (core.result.Result.Ok (st ["1"])) ∧
    (pure.run (st ["1"])
      (sliceOf [pure.Op.ApplyDown "1" "d1"])).reducesTo
      (core.result.Result.Ok (st [])) := by
  native_decide

/-- Already-applied versions are unchanged by a pending-only plan (order preserved). -/
theorem migrate_preserves_applied_prefix :
    (pure.run (st ["1"])
      (sliceOf [pure.Op.ApplyUp "2" "u2"])).reducesTo
      (core.result.Result.Ok (st ["1", "2"])) := by
  native_decide

end TqlmateExtract.CoreProperties
