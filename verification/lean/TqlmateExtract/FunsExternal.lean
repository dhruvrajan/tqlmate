import Aeneas
import TqlmateExtract.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open tqlmate_extract

/-- Decode Aeneas `Str` (`Slice U8`) as Lean `String` (UTF-8). -/
def strToString (s : Str) : String :=
  String.fromUTF8! <| ByteArray.mk <| Array.mk <|
    s.val.map fun (u : U8) => UInt8.ofNat u.val

/-- Encode Lean `String` as Aeneas `Str`. -/
def stringToStr (s : String) : Str :=
  if h : s.toByteArray.size ≤ U32.max then
    toStr s h
  else
    toStr "" (by decide +native)

private def cmpU8List : List U8 → List U8 → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | x :: xs, y :: ys =>
    if x.val < y.val then .lt
    else if y.val < x.val then .gt
    else cmpU8List xs ys

@[rust_fun "core::char::convert::{core::convert::From<char, u8>}::from"]
def Char.Insts.CoreConvertFromU8.from (x : Std.U8) : Result Char :=
  ok (Char.ofNat x.val)

@[rust_fun "core::cmp::impls::{core::cmp::PartialOrd<&'1 @A, &'0 @B>}::lt"]
def Shared1A.Insts.CoreCmpPartialOrdShared0B.lt
    {A : Type} {B : Type} (PartialOrdInst : core.cmp.PartialOrd A B)
    (a : A) (b : B) : Result Bool :=
  PartialOrdInst.lt a b

@[rust_fun "core::fmt::{core::fmt::Display<str>}::fmt"]
def Str.Insts.CoreFmtDisplay.fmt
    (_ : Str) (fmt : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), fmt)

@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type}
    (o : Option T) :
    Result (core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T) :=
  match o with
  | some v => ok (.Continue v)
  | none => ok (.Break none)

@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (T : Type) (r : Option core.convert.Infallible) : Result (Option T) :=
  match r with
  | none => ok none
  | some i => nomatch i

@[rust_fun "core::str::{str}::len"]
def core.str.Str.len (s : Str) : Result Std.Usize := ok (Slice.len s)

@[rust_fun "core::str::{str}::is_empty"]
def core.str.Str.is_empty (s : Str) : Result Bool :=
  ok (decide (Slice.length s = 0))

@[rust_fun "core::str::{str}::as_bytes"]
def core.str.Str.as_bytes (s : Str) : Result (Slice Std.U8) := ok s

@[rust_fun "core::str::traits::{core::cmp::PartialEq<str, str>}::eq"]
def Str.Insts.CoreCmpPartialEqStr.eq (a b : Str) : Result Bool := ok (a == b)

@[rust_fun "core::str::traits::{core::cmp::PartialOrd<str, str>}::partial_cmp"]
def Str.Insts.CoreCmpPartialOrdStr.partial_cmp
    (a b : Str) : Result (Option Ordering) :=
  ok (some (cmpU8List a.val b.val))

@[rust_fun
  "core::str::traits::{core::ops::index::Index<str, @I, @Clause0_Output>}::index"]
def Str.Insts.CoreOpsIndexIndex.index
    {I : Type} {Clause0_Output : Type}
    (sliceindexSliceIndexIStrClause0_OutputInst :
      core.slice.index.SliceIndex I Str Clause0_Output)
    (s : Str) (i : I) : Result Clause0_Output :=
  sliceindexSliceIndexIStrClause0_OutputInst.index i s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::index_mut"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.index_mut
    (r : core.ops.range.Range Std.Usize) (s : Str) :
    Result (Str × (Str → Str)) :=
  core.slice.index.SliceIndexRangeUsizeSlice.index_mut (T := U8) r s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::index"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.index
    (r : core.ops.range.Range Std.Usize) (s : Str) : Result Str :=
  core.slice.index.SliceIndexRangeUsizeSlice.index (T := U8) r s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::get_unchecked_mut"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked_mut
    (_ : core.ops.range.Range Std.Usize) (_ : MutRawPtr Str) :
    Result (MutRawPtr Str) := fail undef

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::get_unchecked"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked
    (_ : core.ops.range.Range Std.Usize) (_ : ConstRawPtr Str) :
    Result (ConstRawPtr Str) := fail undef

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::get_mut"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_mut
    (r : core.ops.range.Range Std.Usize) (s : Str) :
    Result ((Option Str) × (Option Str → Str)) :=
  core.slice.index.SliceIndexRangeUsizeSlice.get_mut (T := U8) r s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, str, str>}::get"]
def core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get
    (r : core.ops.range.Range Std.Usize) (s : Str) : Result (Option Str) :=
  core.slice.index.SliceIndexRangeUsizeSlice.get (T := U8) r s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, str, str>}::index_mut"]
def core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexStrStr.index_mut
    (r : core.ops.range.RangeTo Std.Usize) (s : Str) :
    Result (Str × (Str → Str)) :=
  core.slice.index.SliceIndexRangeToUsizeSlice.index_mut (T := U8) r s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, str, str>}::index"]
def core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexStrStr.index
    (r : core.ops.range.RangeTo Std.Usize) (s : Str) : Result Str :=
  core.slice.index.SliceIndexRangeToUsizeSlice.index (T := U8) r s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, str, str>}::get_unchecked_mut"]
def core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked_mut
    (_ : core.ops.range.RangeTo Std.Usize) (_ : MutRawPtr Str) :
    Result (MutRawPtr Str) := fail undef

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, str, str>}::get_unchecked"]
def core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked
    (_ : core.ops.range.RangeTo Std.Usize) (_ : ConstRawPtr Str) :
    Result (ConstRawPtr Str) := fail undef

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, str, str>}::get_mut"]
def core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_mut
    (r : core.ops.range.RangeTo Std.Usize) (s : Str) :
    Result ((Option Str) × (Option Str → Str)) :=
  core.slice.index.SliceIndexRangeToUsizeSlice.get_mut (T := U8) r s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, str, str>}::get"]
def core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexStrStr.get
    (r : core.ops.range.RangeTo Std.Usize) (s : Str) : Result (Option Str) :=
  core.slice.index.SliceIndexRangeToUsizeSlice.get (T := U8) r s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::index_mut"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.index_mut
    (r : core.ops.range.RangeFrom Std.Usize) (s : Str) :
    Result (Str × (Str → Str)) :=
  core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut (T := U8) r s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::index"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.index
    (r : core.ops.range.RangeFrom Std.Usize) (s : Str) : Result Str :=
  core.slice.index.SliceIndexRangeFromUsizeSlice.index (T := U8) r s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::get_unchecked_mut"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked_mut
    (_ : core.ops.range.RangeFrom Std.Usize) (_ : MutRawPtr Str) :
    Result (MutRawPtr Str) := fail undef

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::get_unchecked"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked
    (_ : core.ops.range.RangeFrom Std.Usize) (_ : ConstRawPtr Str) :
    Result (ConstRawPtr Str) := fail undef

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::get_mut"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_mut
    (r : core.ops.range.RangeFrom Std.Usize) (s : Str) :
    Result ((Option Str) × (Option Str → Str)) :=
  core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut (T := U8) r s

@[rust_fun
  "core::str::traits::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, str, str>}::get"]
def core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexStrStr.get
    (r : core.ops.range.RangeFrom Std.Usize) (s : Str) : Result (Option Str) :=
  core.slice.index.SliceIndexRangeFromUsizeSlice.get (T := U8) r s

@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqString.eq
    (a b : String) : Result Bool := ok (a == b)

@[rust_fun "alloc::string::{core::cmp::Ord<alloc::string::String>}::cmp"]
def alloc.string.String.Insts.CoreCmpOrd.cmp
    (a b : String) : Result Ordering := ok (compare a b)

@[rust_fun "alloc::string::{alloc::string::String}::new"]
def alloc.string.String.new : Result String := ok ""

@[rust_fun "alloc::string::{alloc::string::String}::push_str"]
def alloc.string.String.push_str (s : String) (t : Str) : Result String :=
  ok (s ++ strToString t)

@[rust_fun "alloc::string::{alloc::string::String}::push"]
def alloc.string.String.push (s : String) (c : Char) : Result String :=
  ok (s.push c)

@[rust_fun "alloc::string::{alloc::string::String}::as_bytes"]
def alloc.string.String.as_bytes (s : String) : Result (Slice Std.U8) :=
  ok (stringToStr s)

@[rust_fun "alloc::string::{alloc::string::String}::is_empty"]
def alloc.string.String.is_empty (s : String) : Result Bool := ok s.isEmpty

@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (s : String) : Result String :=
  ok s

@[rust_fun "alloc::string::{core::fmt::Debug<alloc::string::String>}::fmt"]
def alloc.string.String.Insts.CoreFmtDebug.fmt
    (_ : String) (fmt : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), fmt)

@[rust_fun
  "alloc::string::{core::ops::index::Index<alloc::string::String, @I, @Clause0_Output>}::index"]
def alloc.string.String.Insts.CoreOpsIndexIndex.index
    {I : Type} {Clause0_Output : Type}
    (coresliceindexSliceIndexIStrClause0_OutputInst :
      core.slice.index.SliceIndex I Str Clause0_Output)
    (s : String) (i : I) : Result Clause0_Output :=
  coresliceindexSliceIndexIStrClause0_OutputInst.index i (stringToStr s)

@[rust_fun
  "alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref"]
def alloc.string.String.Insts.CoreOpsDerefDerefStr.deref
    (s : String) : Result Str :=
  ok (stringToStr s)

unsafe def alloc.string.ToString.Blanket.to_string.impl
    {T : Type} (_ : core.fmt.Display T) (x : T) : Result String :=
  ok (strToString (unsafeCast x))

@[implemented_by alloc.string.ToString.Blanket.to_string.impl,
  rust_fun "alloc::string::{alloc::string::ToString<@T>}::to_string"]
opaque alloc.string.ToString.Blanket.to_string
    {T : Type} (corefmtDisplayInst : core.fmt.Display T) : T → Result String

@[rust_fun
  "alloc::string::{core::convert::From<alloc::string::String, &'0 str>}::from"]
def alloc.string.String.Insts.CoreConvertFromShared0Str.from
    (s : Str) : Result String :=
  ok (strToString s)
