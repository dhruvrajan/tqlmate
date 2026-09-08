import Aeneas
import TqlmateExtract.Funs

/-!
# Properties of Aeneas-extracted `pure.*` (from `src/pure.rs`)

These theorems target `tqlmate_extract.pure.*` in `aeneas-generated/Funs.lean`.
CI `lake build` elaborates Funs and checks this file.

Concrete examples stay aligned with `tests/spec_parity.rs` / Spec `Properties`.
-/

open Aeneas Aeneas.Std Result
open tqlmate_extract

namespace TqlmateExtract.ExtrProperties

private instance : BEq pure.ParseError where
  beq
    | .Extension, .Extension => true
    | .Filename, .Filename => true
    | .VersionDigits, .VersionDigits => true
    | .Name, .Name => true
    | .Markers, .Markers => true
    | _, _ => false

private instance {α β} [BEq α] [BEq β] : BEq (core.result.Result α β) where
  beq
    | .Ok a, .Ok b => a == b
    | .Err e, .Err f => e == f
    | _, _ => false

private instance : BEq pure.StrictOrderError where
  beq
    | .OutOfOrder a b, .OutOfOrder c d => a == c && b == d

private def mig (version : String) (nm : String) : pure.MigrationId :=
  { version := version, «name» := nm }

private def sliceOf {α} (xs : List α)
    (h : xs.length ≤ Usize.max := by native_decide) : Slice α :=
  Slice.from xs h

/-! ## Parse rejects / ok -/

theorem parse_rejects_wrong_extension_example :
    (pure.parse_version_name (toStr "123_name.sql")).reducesTo
      (core.result.Result.Err pure.ParseError.Extension) := by
  native_decide

theorem parse_rejects_non_digit_version_example :
    (pure.parse_version_name (toStr "abc_name.tql")).reducesTo
      (core.result.Result.Err pure.ParseError.VersionDigits) := by
  native_decide

theorem parse_rejects_empty_name_example :
    (pure.parse_version_name (toStr "123_.tql")).reducesTo
      (core.result.Result.Err pure.ParseError.Name) := by
  native_decide

theorem parse_rejects_no_underscore_example :
    (pure.parse_version_name (toStr "nope.tql")).reducesTo
      (core.result.Result.Err pure.ParseError.Filename) := by
  native_decide

theorem parse_ok_example :
    (pure.parse_version_name (toStr "20240101120000_create_person.tql")).reducesTo
      (core.result.Result.Ok ("20240101120000", "create_person")) := by
  native_decide

/-! ## Split up/down markers -/

theorem split_rejects_no_markers :
    (pure.split_up_down (toStr "no markers here")).reducesTo
      (core.result.Result.Err pure.ParseError.Markers) := by
  native_decide

theorem split_rejects_empty :
    (pure.split_up_down (toStr "")).reducesTo
      (core.result.Result.Err pure.ParseError.Markers) := by
  native_decide

theorem split_ok_example :
    (pure.split_up_down
      (toStr "-- migrate:up\ndefine x;\n-- migrate:down\nundefine x;\n")).reducesTo
      (core.result.Result.Ok ("define x;", "undefine x;")) := by
  native_decide

theorem split_ok_case_insensitive :
    (pure.split_up_down
      (toStr "-- MIGRATE:UP\ndefine x;\n-- Migrate:Down\nundefine x;\n")).reducesTo
      (core.result.Result.Ok ("define x;", "undefine x;")) := by
  native_decide

/-! ## Strict order -/

theorem strict_order_detects_hole :
    (pure.check_strict_order
      (sliceOf [mig "1" "a", mig "2" "b", mig "3" "c"])
      (sliceOf ["1", "3"])).reducesTo
      (core.result.Result.Err (pure.StrictOrderError.OutOfOrder "2" "3")) := by
  native_decide

theorem strict_order_ok_prefix :
    (pure.check_strict_order
      (sliceOf [mig "1" "a", mig "2" "b", mig "3" "c"])
      (sliceOf ["1", "2"])).reducesTo
      (core.result.Result.Ok ()) := by
  native_decide

theorem check_strict_order_empty_applied :
    (pure.check_strict_order
      (sliceOf [mig "1" "a"])
      (sliceOf ([] : List String))).reducesTo
      (core.result.Result.Ok ()) := by
  native_decide

/-! ## Pending ∩ applied -/

theorem pending_applied_disjoint_example :
    (pure.pending_applied_disjoint
      (sliceOf [mig "1" "a", mig "2" "b"])
      (sliceOf ["1"])).reducesTo true := by
  native_decide

/-! ## Slugify -/

theorem slugify_examples :
    (pure.slugify (toStr "Create Person")).reducesTo "create_person" ∧
    (pure.slugify (toStr "!!!")).reducesTo "migration" ∧
    (pure.slugify (toStr "a__b")).reducesTo "a_b" := by
  native_decide

end TqlmateExtract.ExtrProperties
