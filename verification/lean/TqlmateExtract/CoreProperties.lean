import Aeneas
import TqlmateExtract.Funs

/-!
# Core migrate/rollback properties (extracted `pure.*`)

∀ / inductive theorems on the Aeneas extract, plus a few `native_decide`
regression fixtures. TypeDB effects remain assumed (see `verification/README.md`).

## ∀ theorems (this file)

| Claim | Theorem |
| --- | --- |
| `run s [] = Ok s` | `run_nil`, `run_nil_of_empty` |
| `run s (op::rest) = step s op >>= run · rest` | `run_cons`, `run_singleton` |
| ApplyUp nonempty ⇒ append | `step_apply_up_ok` |
| ApplyUp empty ⇒ Err | `step_apply_up_err` |
| ApplyDown empty ⇒ Err | `step_apply_down_err` |
| ApplyDown nonempty ⇒ `remove_last_matching` | `step_apply_down_ok` |
| `remove_last_matching [v] v = []` | `remove_last_matching_singleton` |
| Empty applied ⇒ empty rollback (∀ files) | `plan_rollback_empty_forall` |
| Empty pending ⇒ empty ups plan | `plan_ups_from_pending_nil` |
| Nonstrict migrate = pending ≫ ups | `plan_migrate_nonstrict_eq` |
| Strict migrate maps check Err | `plan_migrate_strict_maps_error` |
| Up then down on empty restores `[]` | `roundtrip_up_down` |
| One ApplyUp appends the version | `run_one_apply_up_appends` |

Fixtures below lock concrete extract shapes (not a substitute for the ∀ table).
-/

open Aeneas Aeneas.Std Result ControlFlow
open tqlmate_extract

namespace TqlmateExtract.CoreProperties

set_option maxHeartbeats 8000000

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

private theorem len0_le {α} : List.length ([] : List α) ≤ Usize.max := by
  change 0 ≤ Usize.max; native_decide

private theorem len1_le (x : α) : List.length ([x] : List α) ≤ Usize.max := by
  change 1 ≤ Usize.max; native_decide

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

/-! ## Helpers -/

theorem version_eq_refl (v : pure.Version) :
    pure.Version.Insts.CoreCmpPartialEqVersion.eq v v = ok true := by
  unfold pure.Version.Insts.CoreCmpPartialEqVersion.eq
  simp [alloc.string.String.Insts.CoreCmpPartialEqString.eq]

theorem op_clone_id (op : pure.Op) :
    pure.Op.Insts.CoreCloneClone.clone op = ok op := by
  unfold pure.Op.Insts.CoreCloneClone.clone
  cases op <;> simp [pure.Version.Insts.CoreCloneClone.clone,
    alloc.string.String.Insts.CoreCloneClone.clone]

theorem prefix_clone_zero (applied : Slice pure.Version) :
    pure.prefix_clone applied 0#usize = ok (alloc.vec.Vec.new pure.Version) := by
  have h : pure.prefix_clone applied 0#usize
      ⦃ out => out = alloc.vec.Vec.new pure.Version ⦄ := by
    unfold pure.prefix_clone pure.prefix_clone_loop
    apply loop.spec_decr_nat
      (measure := fun (p : alloc.vec.Vec pure.Version × Usize) => p.2.val)
      (inv := fun (p : alloc.vec.Vec pure.Version × Usize) =>
        p.1 = alloc.vec.Vec.new pure.Version ∧ p.2 = 0#usize)
      (post := fun out => out = alloc.vec.Vec.new pure.Version)
    · intro x hx
      rcases hx with ⟨hout, hi⟩
      unfold pure.prefix_clone_loop.body
      simp [hi, hout]
    · simp
  rw [WP.spec_equiv_exists] at h
  rcases h with ⟨out, hout, heq⟩
  simpa [heq] using hout

/-! ## ∀ `remove_last_matching` (Rust: drop last match, else keep) -/

/-- Empty applied ⇒ empty result. -/
theorem remove_last_matching_nil (v : pure.Version) :
    pure.remove_last_matching (Slice.from ([] : List pure.Version) len0_le) v =
      ok (alloc.vec.Vec.new pure.Version) := by
  rw [pure.remove_last_matching.eq_1]
  simp [core.slice.Slice.is_empty, Slice.from_val]

/-- Last (only) element equals `v` ⇒ empty (prefix of length 0). -/
theorem remove_last_matching_singleton (v : pure.Version) :
    pure.remove_last_matching (Slice.from [v] (len1_le v)) v =
      ok (alloc.vec.Vec.new pure.Version) := by
  rw [pure.remove_last_matching.eq_1]
  have hempty : core.slice.Slice.is_empty (Slice.from [v] (len1_le v)) = ok false := by
    simp only [core.slice.Slice.is_empty]
    have hlen : (Slice.from [v] (len1_le v)).length = 1 := rfl
    have hne : ¬ (1 = 0) := by decide
    simp [hlen, hne]
  rw [hempty]
  simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
  have hlen1 : (Slice.from [v] (len1_le v)).len = 1#usize := by
    apply UScalar.eq_of_val_eq; rfl
  have hsub01 : (1#usize - 1#usize) = ok 0#usize := rfl
  have hsub : ((Slice.from [v] (len1_le v)).len - 1#usize) = ok 0#usize := by
    simpa [hlen1] using hsub01
  simp only [hsub, bind_tc_ok]
  have hidx : Slice.index_usize (Slice.from [v] (len1_le v)) 0#usize = ok v := by
    have h := Slice.index_usize_spec (Slice.from [v] (len1_le v)) 0#usize
      (by simp [Slice.from_val])
    rw [WP.spec_equiv_exists] at h
    rcases h with ⟨x, hx, heq⟩
    have : x = v := by
      have g : (Slice.from [v] (len1_le v)).val[0]'(by simp [Slice.from_val]) = v := by
        simp [Slice.from_val]
      exact heq.trans g
    simpa [this] using hx
  simp only [hidx, bind_tc_ok, version_eq_refl, ↓reduceIte]
  exact prefix_clone_zero _

/-! ## ∀ `run` fold -/

/-- `run s [] = Ok s`. -/
theorem run_nil (s : pure.State) :
    pure.run s (Slice.from ([] : List pure.Op) len0_le) =
      ok (core.result.Result.Ok s) := by
  rw [pure.run.eq_1]
  simp [core.slice.Slice.is_empty, Slice.from_val]

theorem run_nil_of_empty (s : pure.State) (plan : Slice pure.Op)
    (he : plan.val = []) :
    pure.run s plan = ok (core.result.Result.Ok s) := by
  rw [pure.run.eq_1]
  have hempty : core.slice.Slice.is_empty plan = ok true := by
    simp only [core.slice.Slice.is_empty]
    have : plan.length = 0 := by simpa using congrArg List.length he
    simp [this]
  rw [hempty]
  simp only [bind_tc_ok, ↓reduceIte]

/-- Singleton fold: `run s [op] = (do let r ← step s op; ok r)`. -/
theorem run_singleton (s : pure.State) (op : pure.Op) :
    pure.run s (Slice.from [op] (len1_le op)) =
      (do
        let r ← pure.step s op
        ok r) := by
  rw [pure.run.eq_1]
  have hempty : core.slice.Slice.is_empty (Slice.from [op] (len1_le op)) = ok false := by
    simp only [core.slice.Slice.is_empty]
    have hlen : (Slice.from [op] (len1_le op)).length = 1 := rfl
    have hne : ¬ (1 = 0) := by decide
    simp [hlen, hne]
  rw [hempty]
  simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
  have hidx : Slice.index_usize (Slice.from [op] (len1_le op)) 0#usize = ok op := by
    have h := Slice.index_usize_spec (Slice.from [op] (len1_le op)) 0#usize
      (by simp [Slice.from_val])
    rw [WP.spec_equiv_exists] at h
    rcases h with ⟨x, hx, heq⟩
    have hxop : x = op := by
      have : (Slice.from [op] (len1_le op)).val[0]'(by simp [Slice.from_val]) = op := by
        simp [Slice.from_val]
      exact heq.trans this
    simpa [hxop] using hx
  simp only [hidx, bind_tc_ok, op_clone_id]
  congr 1
  funext r
  cases r with
  | Ok s' =>
    simp only
    rw [Slice.index_SliceIndexRangeFromUsizeSliceInst]
    have hrange :=
      core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec
        (r := { start := 1#usize }) (s := Slice.from [op] (len1_le op))
        (by change 1 ≤ _; have : (Slice.from [op] (len1_le op)).length = 1 := rfl; omega)
    rw [WP.spec_equiv_exists] at hrange
    rcases hrange with ⟨s1, hs1eq, hval, _hlen⟩
    have hempty1 : s1.val = [] := by simpa [Slice.from_val] using hval
    rw [hs1eq, bind_tc_ok, run_nil_of_empty s' s1 hempty1]
  | Err e =>
    rfl

/-- Cons fold: `run s (op::rest) = step s op >>= run · rest`. -/
theorem run_cons (s : pure.State) (op : pure.Op) (rest : List pure.Op)
    (h : List.length (op :: rest) ≤ Usize.max)
    (hrest : rest.length ≤ Usize.max) :
    pure.run s (Slice.from (op :: rest) h) =
      (do
        let r ← pure.step s op
        match r with
        | core.result.Result.Ok s' => pure.run s' (Slice.from rest hrest)
        | core.result.Result.Err e => ok (core.result.Result.Err e)) := by
  rw [pure.run.eq_1]
  have hempty : core.slice.Slice.is_empty (Slice.from (op :: rest) h) = ok false := by
    simp only [core.slice.Slice.is_empty]
    have hlen : (Slice.from (op :: rest) h).length = Nat.succ rest.length := by
      simp [Slice.from_val]
    have hne : ¬ (Nat.succ rest.length = 0) := Nat.succ_ne_zero _
    simp [hlen, hne]
  rw [hempty]
  simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
  have hidx : Slice.index_usize (Slice.from (op :: rest) h) 0#usize = ok op := by
    have hs := Slice.index_usize_spec (Slice.from (op :: rest) h) 0#usize
      (by simp [Slice.from_val])
    rw [WP.spec_equiv_exists] at hs
    rcases hs with ⟨x, hx, heq⟩
    have : x = op := by
      have g : (Slice.from (op :: rest) h).val[0]'(by simp [Slice.from_val]) = op := by
        simp [Slice.from_val]
      exact heq.trans g
    simpa [this] using hx
  simp only [hidx, bind_tc_ok, op_clone_id]
  congr 1; funext r
  cases r with
  | Ok s' =>
    simp only
    rw [Slice.index_SliceIndexRangeFromUsizeSliceInst]
    have hbound : ({ start := 1#usize } : core.ops.range.RangeFrom Usize).start ≤
        (Slice.from (op :: rest) h).length := by
      change 1 ≤ (Slice.from (op :: rest) h).length
      have : (Slice.from (op :: rest) h).length = rest.length + 1 := by
        simp [Slice.from_val]
      omega
    have hrange :=
      core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec
        (r := { start := 1#usize }) (s := Slice.from (op :: rest) h) hbound
    rw [WP.spec_equiv_exists] at hrange
    rcases hrange with ⟨s1, hs1eq, hval, _⟩
    have hvals : s1.val = rest := by simpa [Slice.from_val] using hval
    have hs1 : s1 = Slice.from rest hrest := by
      apply Slice.ext
      simpa [Slice.from_val] using hvals
    rw [hs1eq, bind_tc_ok, hs1]
  | Err e =>
    rfl

/-! ## ∀ `step` -/

/-- Non-empty up ⇒ `applied' = applied ++ [v]`. -/
theorem step_apply_up_ok (s : pure.State) (v : pure.Version) (up : String)
    (hne : pure.body_is_empty (stringToStr up) = ok false)
    (hroom : s.applied.val.length < Usize.max) :
    pure.step s (pure.Op.ApplyUp v up)
      ⦃ r => ∃ applied',
          r = core.result.Result.Ok { applied := applied' } ∧
          applied'.val = s.applied.val ++ [v] ⦄ := by
  unfold pure.step
  simp [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, hne]
  apply WP.spec_bind
    (Pₘ := fun (applied' : alloc.vec.Vec pure.Version) =>
      applied'.val = s.applied.val ++ [v])
  · exact alloc.vec.Vec.push_spec s.applied v hroom
  · intro applied' happ
    simp [happ]

/-- Empty up ⇒ `Err EmptyUp`. -/
theorem step_apply_up_err (s : pure.State) (v : pure.Version) (up : String)
    (he : pure.body_is_empty (stringToStr up) = ok true) :
    pure.step s (pure.Op.ApplyUp v up)
      ⦃ r => r = core.result.Result.Err (pure.StepError.EmptyUp v) ⦄ := by
  unfold pure.step
  simp [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, he]

/-- Empty down ⇒ `Err EmptyDown`. -/
theorem step_apply_down_err (s : pure.State) (v : pure.Version) (down : String)
    (he : pure.body_is_empty (stringToStr down) = ok true) :
    pure.step s (pure.Op.ApplyDown v down)
      ⦃ r => r = core.result.Result.Err (pure.StepError.EmptyDown v) ⦄ := by
  unfold pure.step
  simp [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, he]

/--
Non-empty down ⇒ result is `Ok` of `remove_last_matching` on `applied`
(last matching `v` removed; unchanged if absent — see Rust `remove_last_matching`).
-/
theorem step_apply_down_ok (s : pure.State) (v : pure.Version) (down : String)
    (hne : pure.body_is_empty (stringToStr down) = ok false)
    (hrem : ∃ applied',
      pure.remove_last_matching (alloc.vec.Vec.deref s.applied) v = ok applied') :
    pure.step s (pure.Op.ApplyDown v down)
      ⦃ r => ∃ applied',
          pure.remove_last_matching (alloc.vec.Vec.deref s.applied) v = ok applied' ∧
          r = core.result.Result.Ok { applied := applied' } ⦄ := by
  unfold pure.step
  simp [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, hne]
  rcases hrem with ⟨applied', hrem⟩
  simp [hrem]

/-! ## ∀ planning -/

/-- Empty applied ⇒ empty rollback plan (∀ files). -/
theorem plan_rollback_empty_forall (files : Slice pure.MigrationSpec) :
    pure.plan_rollback files (Slice.from ([] : List pure.Version) len0_le)
      ⦃ r => r = core.result.Result.Ok (alloc.vec.Vec.new pure.Op) ⦄ := by
  unfold pure.plan_rollback
  simp [core.slice.Slice.is_empty, Slice.from_val]

/-- Empty pending ⇒ empty ups plan. -/
theorem plan_ups_from_pending_nil :
    pure.plan_ups_from_pending
        (Slice.from ([] : List pure.MigrationSpec) len0_le)
      ⦃ r => r = core.result.Result.Ok (alloc.vec.Vec.new pure.Op) ⦄ := by
  unfold pure.plan_ups_from_pending pure.plan_ups_from_pending_loop
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec pure.Op × Usize) =>
      (Slice.from ([] : List pure.MigrationSpec) len0_le).length - p.2.val)
    (inv := fun (p : alloc.vec.Vec pure.Op × Usize) =>
      p.1 = alloc.vec.Vec.new pure.Op ∧ p.2.val = 0)
    (post := fun r => r = core.result.Result.Ok (alloc.vec.Vec.new pure.Op))
  · intro x hx
    rcases hx with ⟨hp, hi⟩
    unfold pure.plan_ups_from_pending_loop.body
    simp [Slice.len, Slice.from_val, hi, hp]
  · simp

/-- Definitional: nonstrict migrate is pending filter then ups. -/
theorem plan_migrate_nonstrict_eq
    (files : Slice pure.MigrationSpec) (applied : Slice pure.Version) :
    pure.plan_migrate files applied false =
      (do
        let pending ← pure.pending_specs files applied
        pure.plan_ups_from_pending (alloc.vec.Vec.deref pending)) := by
  unfold pure.plan_migrate
  rfl

/-- Strict `plan_migrate` propagates `check_strict_order_specs` errors. -/
theorem plan_migrate_strict_maps_error
    (files : Slice pure.MigrationSpec) (applied : Slice pure.Version)
    (pending applied_up_to : pure.Version)
    (h : pure.check_strict_order_specs files applied =
      ok (core.result.Result.Err
        (pure.StrictOrderError.OutOfOrder pending applied_up_to))) :
    pure.plan_migrate files applied true
      ⦃ r => r = core.result.Result.Err
          (pure.PlanError.StrictOrder pending applied_up_to) ⦄ := by
  unfold pure.plan_migrate
  simp [h]

/--
Nonempty applied: rollback unfolds to last-version lookup
(`MissingFile` / `EmptyDown` / single `ApplyDown`) — definitional shape of the extract.
-/
theorem plan_rollback_nonempty_eq
    (files : Slice pure.MigrationSpec) (applied : Slice pure.Version)
    (hne : ¬ applied.val = []) :
    pure.plan_rollback files applied =
      (do
        let i := Slice.len applied
        let i1 ← i - 1#usize
        let v ← Slice.index_usize applied i1
        let version ← pure.Version.Insts.CoreCloneClone.clone v
        let o ← pure.find_spec files version
        match o with
        | none => ok (core.result.Result.Err (pure.PlanError.MissingFile version))
        | some m =>
          let s ← alloc.string.String.Insts.CoreOpsDerefDerefStr.deref m.down
          let b1 ← pure.body_is_empty s
          if b1 then
            let v1 ← pure.Version.Insts.CoreCloneClone.clone m.version
            let s1 ← alloc.string.String.Insts.CoreCloneClone.clone m.name
            ok (core.result.Result.Err (pure.PlanError.EmptyDown v1 s1))
          else
            let v1 ← pure.Version.Insts.CoreCloneClone.clone m.version
            let s1 ← alloc.string.String.Insts.CoreCloneClone.clone m.down
            let plan ← alloc.vec.Vec.push (alloc.vec.Vec.new pure.Op)
              (pure.Op.ApplyDown v1 s1)
            ok (core.result.Result.Ok plan)) := by
  unfold pure.plan_rollback
  have hempty : core.slice.Slice.is_empty applied = ok false := by
    simp only [core.slice.Slice.is_empty]
    have : ¬ applied.length = 0 := by
      intro hlen
      apply hne
      simpa [Slice.length] using (List.length_eq_zero_iff.mp hlen)
    simp [this]
  rw [hempty]
  simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ## Round-trip & migrate-then-run -/

/--
∀ `v` with nonempty up/down: empty → ApplyUp → ApplyDown → empty applied.
-/
theorem roundtrip_up_down (v : pure.Version) (up down : String)
    (hneU : pure.body_is_empty (stringToStr up) = ok false)
    (hneD : pure.body_is_empty (stringToStr down) = ok false) :
    (do
      let r1 ← pure.step ⟨alloc.vec.Vec.new pure.Version⟩ (pure.Op.ApplyUp v up)
      match r1 with
      | core.result.Result.Ok s => pure.step s (pure.Op.ApplyDown v down)
      | core.result.Result.Err e => ok (core.result.Result.Err e))
      = ok (core.result.Result.Ok ⟨alloc.vec.Vec.new pure.Version⟩) := by
  have hlen0 : (alloc.vec.Vec.new pure.Version).val.length = 0 := by
    simp [alloc.vec.Vec.new]
  have hroom : (alloc.vec.Vec.new pure.Version).val.length < Usize.max := by
    simp [hlen0]; native_decide
  have hup :=
    step_apply_up_ok ⟨alloc.vec.Vec.new pure.Version⟩ v up hneU hroom
  rw [WP.spec_equiv_exists] at hup
  rcases hup with ⟨r1, hr1, applied', hr1eq, happ⟩
  have happ' : applied'.val = [v] := by simpa [hlen0] using happ
  simp [hr1, hr1eq]
  unfold pure.step
  simp [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, hneD]
  have hslice : alloc.vec.Vec.deref applied' = Slice.from [v] (len1_le v) := by
    apply Slice.ext
    simp [alloc.vec.Vec.deref, Slice.from_val, happ']
  rw [hslice, remove_last_matching_singleton]
  simp only [bind_tc_ok]

/--
One successful ApplyUp appends the version (migrate-then-run base case).
Combined with `run_cons` / `plan_migrate_nonstrict_eq`, pending ups grow `applied`
in file order.
-/
theorem run_one_apply_up_appends (s : pure.State) (v : pure.Version) (up : String)
    (hne : pure.body_is_empty (stringToStr up) = ok false)
    (hroom : s.applied.val.length < Usize.max) :
    pure.run s (Slice.from [pure.Op.ApplyUp v up] (len1_le _))
      ⦃ r => ∃ applied',
          r = core.result.Result.Ok { applied := applied' } ∧
          applied'.val = s.applied.val ++ [v] ⦄ := by
  have hrun := run_singleton s (pure.Op.ApplyUp v up)
  have hstep := step_apply_up_ok s v up hne hroom
  rw [WP.spec_equiv_exists] at hstep
  rcases hstep with ⟨rstep, hrstep, applied', hrsteq, happ⟩
  rw [hrun, hrstep]
  simp only [bind_tc_ok]
  exact ⟨applied', by simp [hrsteq], happ⟩

/-! ## Regression fixtures (`native_decide`) -/

theorem body_is_empty_nil :
    (pure.body_is_empty (toStr "")).reducesTo true := by
  native_decide

theorem body_is_empty_u :
    (pure.body_is_empty (toStr "u")).reducesTo false := by
  native_decide

theorem step_apply_up_example :
    (pure.step (st []) (pure.Op.ApplyUp "1" "define x;")).reducesTo
      (core.result.Result.Ok (st ["1"])) := by
  native_decide

theorem step_apply_down_removes_last :
    (pure.step (st ["1", "2", "1"]) (pure.Op.ApplyDown "1" "undefine;")).reducesTo
      (core.result.Result.Ok (st ["1", "2"])) := by
  native_decide

theorem run_empty_plan_example :
    (pure.run (st ["1", "2"]) (sliceOf ([] : List pure.Op))).reducesTo
      (core.result.Result.Ok (st ["1", "2"])) := by
  native_decide

theorem run_up_then_down_inverse_example :
    (pure.run (st ["0"])
      (sliceOf [pure.Op.ApplyUp "1" "u", pure.Op.ApplyDown "1" "d"])).reducesTo
      (core.result.Result.Ok (st ["0"])) := by
  native_decide

theorem plan_migrate_idempotent_when_applied :
    (pure.plan_migrate
      (sliceOf [mspec "1" "a" "u1" "d1", mspec "2" "b" "u2" "d2"])
      (sliceOf ["1", "2"])
      false).reducesTo
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

theorem migrate_rollback_roundtrip :
    (pure.run (st [])
      (sliceOf [pure.Op.ApplyUp "1" "u1"])).reducesTo
      (core.result.Result.Ok (st ["1"])) ∧
    (pure.run (st ["1"])
      (sliceOf [pure.Op.ApplyDown "1" "d1"])).reducesTo
      (core.result.Result.Ok (st [])) := by
  native_decide

theorem remove_last_matching_singleton_example :
    (pure.remove_last_matching (sliceOf (["X"] : List pure.Version)) "X").reducesTo
      (alloc.vec.Vec.new pure.Version) := by
  native_decide

end TqlmateExtract.CoreProperties
