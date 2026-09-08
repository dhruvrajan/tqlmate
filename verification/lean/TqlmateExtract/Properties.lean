import TqlmateExtract.Spec

/-!
# Spec properties (readable twin of the extract)

These theorems are about `TqlmateExtract.Spec`. The CI-critical proofs about the
**Aeneas extract** live in `ExtrProperties.lean` (same concrete fixtures).

Keep these `native_decide` examples in lockstep with `tests/spec_parity.rs` and
`ExtrProperties.lean`.
-/
namespace TqlmateExtract.Properties

open TqlmateExtract.Spec

private instance : DecidableEq (Except ParseError (String × String)) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
    if h : x = y then .isTrue (by cases h; rfl)
    else .isFalse (by intro e; cases e; exact h rfl)
  | .error e₁, .error e₂ =>
    if h : e₁ = e₂ then .isTrue (by cases h; rfl)
    else .isFalse (by intro e; cases e; exact h rfl)
  | .ok _, .error _ => .isFalse (by intro e; cases e)
  | .error _, .ok _ => .isFalse (by intro e; cases e)

private instance : DecidableEq (Except StrictOrderError Unit) := fun a b =>
  match a, b with
  | .ok (), .ok () => .isTrue rfl
  | .error e₁, .error e₂ =>
    if h : e₁ = e₂ then .isTrue (by cases h; rfl)
    else .isFalse (by intro e; cases e; exact h rfl)
  | .ok _, .error _ => .isFalse (by intro e; cases e)
  | .error _, .ok _ => .isFalse (by intro e; cases e)

/-- Pending ∩ applied classifications are empty (consistent with `applied`). -/
theorem pending_applied_disjoint_true (files : List MigrationId) (applied : List String) :
    pendingAppliedDisjoint files applied = true := by
  induction files with
  | nil => simp [pendingAppliedDisjoint, statusRows]
  | cons f rest ih =>
    simp [pendingAppliedDisjoint, statusRows] at ih ⊢
    constructor
    · cases h : versionIn applied f.version <;> simp [*]
    · exact ih

/-- Empty applied list always passes strict order. -/
theorem checkStrictOrder_empty_applied (files : List MigrationId) :
    checkStrictOrder files [] = .ok () := by
  simp [checkStrictOrder, maxVersion?]

/-- Filenames without `.tql` are rejected. -/
theorem parse_rejects_bad_extension (name : String) (h : ¬ endsWithSuffix name ".tql") :
    parseVersionName name = .error .extension := by
  simp [parseVersionName, dropSuffix, h]

theorem parse_rejects_non_digit_version_example :
    parseVersionName "abc_name.tql" = .error .versionDigits := by
  native_decide

theorem parse_rejects_empty_name_example :
    parseVersionName "123_.tql" = .error .name := by
  native_decide

theorem parse_rejects_no_underscore_example :
    parseVersionName "nope.tql" = .error .filename := by
  native_decide

theorem parse_rejects_wrong_extension_example :
    parseVersionName "123_name.sql" = .error .extension := by
  native_decide

theorem split_rejects_no_markers :
    splitUpDown "no markers here" = .error .markers := by
  native_decide

theorem split_rejects_empty :
    splitUpDown "" = .error .markers := by
  native_decide

theorem parse_ok_example :
    parseVersionName "20240101120000_create_person.tql" =
      .ok ("20240101120000", "create_person") := by
  native_decide

theorem split_ok_example :
    splitUpDown "-- migrate:up\ndefine x;\n-- migrate:down\nundefine x;\n" =
      .ok ("define x;", "undefine x;") := by
  native_decide

theorem split_ok_case_insensitive :
    splitUpDown "-- MIGRATE:UP\ndefine x;\n-- Migrate:Down\nundefine x;\n" =
      .ok ("define x;", "undefine x;") := by
  native_decide

theorem strict_order_detects_hole :
    checkStrictOrder
        [{ version := "1", name := "a" },
         { version := "2", name := "b" },
         { version := "3", name := "c" }]
        ["1", "3"] =
      .error (.outOfOrder "2" "3") := by
  native_decide

theorem strict_order_ok_prefix :
    checkStrictOrder
        [{ version := "1", name := "a" },
         { version := "2", name := "b" },
         { version := "3", name := "c" }]
        ["1", "2"] =
      .ok () := by
  native_decide

theorem slugify_examples :
    slugify "Create Person" = "create_person" ∧
    slugify "!!!" = "migration" ∧
    slugify "a__b" = "a_b" := by
  native_decide

theorem dump_strip_roundtrip :
    let files : List MigrationId := [{ version := "1", name := "person" }]
    let h := dumpHeader ["1"] files
    stripDumpHeader (h ++ "define\n  entity x;") = "define\n  entity x;" := by
  native_decide

end TqlmateExtract.Properties
