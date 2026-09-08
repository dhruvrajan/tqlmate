/-
  Spec: Lean model of `src/pure.rs` (tqlmate migration/ledger algorithm).
  Faithful formalization of the pure algorithm Charon/Aeneas extracts from Rust.
-/

namespace TqlmateExtract.Spec

inductive ParseError where
  | extension
  | filename
  | versionDigits
  | name
  | markers
  deriving DecidableEq, Repr

inductive MigrationStatus where
  | applied
  | pending
  deriving DecidableEq, Repr

structure MigrationId where
  version : String
  name : String
  deriving DecidableEq, Repr

def MigrationId.label (m : MigrationId) : String :=
  m.version ++ "_" ++ m.name

def isAsciiDigit (c : Char) : Bool :=
  decide ('0' ≤ c) && decide (c ≤ '9')

def isAsciiDigits (s : String) : Bool :=
  !s.isEmpty && s.all isAsciiDigit

/-- List-based helpers (Lean 4.31 `String.take`/`drop` return slices). -/
def takeN (s : String) (n : Nat) : String :=
  String.ofList (s.toList.take n)

def dropN (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

def endsWithSuffix (s suf : String) : Bool :=
  s.length ≥ suf.length && dropN s (s.length - suf.length) == suf

def dropSuffix (s suf : String) : Option String :=
  if endsWithSuffix s suf then some (takeN s (s.length - suf.length)) else none

def startsWithPref (s pref : String) : Bool :=
  takeN s pref.length == pref

def trimSpaces (s : String) : String :=
  let chars := s.toList
  let dropL := chars.dropWhile fun c => c == ' ' || c == '\t'
  let dropR := dropL.reverse.dropWhile fun c => c == ' ' || c == '\t'
  String.ofList dropR.reverse

def parseVersionName (filename : String) : Except ParseError (String × String) :=
  match dropSuffix filename ".tql" with
  | none => .error .extension
  | some stem =>
    match stem.splitOn "_" with
    | [] => .error .filename
    | [_] => .error .filename
    | version :: rest =>
      let name := String.intercalate "_" rest
      if version.isEmpty || !isAsciiDigits version then
        .error .versionDigits
      else if name.isEmpty then
        .error .name
      else
        .ok (version, name)

def eqIgnoreAsciiCase (a b : String) : Bool :=
  a.length == b.length &&
    (List.zip a.toList b.toList).all fun p => p.1.toLower == p.2.toLower

/-- `some true` = up, `some false` = down. -/
def migrationMarker (line : String) : Option Bool :=
  let trimmed := trimSpaces line
  if !startsWithPref trimmed "--" then none
  else
    let marker := trimSpaces (dropN trimmed 2)
    if eqIgnoreAsciiCase marker "migrate:up" then some true
    else if eqIgnoreAsciiCase marker "migrate:down" then some false
    else none

def trimOwned (s : String) : String :=
  let chars := s.toList
  let isWs (c : Char) := c == ' ' || c == '\t' || c == '\n' || c == '\r'
  let dropL := chars.dropWhile isWs
  let dropR := dropL.reverse.dropWhile isWs
  String.ofList dropR.reverse

def splitUpDown (text : String) : Except ParseError (String × String) :=
  Id.run do
    let mut sec : Option Bool := none
    let mut up : String := ""
    let mut down : String := ""
    let mut saw := false
    for line0 in text.splitOn "\n" do
      let line :=
        if endsWithSuffix line0 "\r" then takeN line0 (line0.length - 1) else line0
      match migrationMarker line with
      | some up? =>
        sec := some up?
        saw := true
      | none =>
        match sec with
        | some true => up := up ++ line ++ "\n"
        | some false => down := down ++ line ++ "\n"
        | none => pure ()
    if !saw && up.isEmpty && down.isEmpty then
      return .error .markers
    return .ok (trimOwned up, trimOwned down)

def versionIn (applied : List String) (v : String) : Bool :=
  applied.contains v

def statusRows (files : List MigrationId) (applied : List String) :
    List (MigrationId × MigrationStatus) :=
  files.map fun f =>
    let st := if versionIn applied f.version then .applied else .pending
    (f, st)

def pendingVersions (files : List MigrationId) (applied : List String) : List String :=
  (statusRows files applied).filterMap fun p =>
    match p.2 with
    | .pending => some p.1.version
    | .applied => none

def appliedAmong (files : List MigrationId) (applied : List String) : List String :=
  (statusRows files applied).filterMap fun p =>
    match p.2 with
    | .applied => some p.1.version
    | .pending => none

def pendingAppliedDisjoint (files : List MigrationId) (applied : List String) : Bool :=
  (statusRows files applied).all fun p =>
    let ina := versionIn applied p.1.version
    match p.2 with
    | .applied => ina
    | .pending => !ina

def maxVersion? (applied : List String) : Option String :=
  applied.foldl (init := (none : Option String)) fun acc v =>
    match acc with
    | none => some v
    | some b => some (if b < v then v else b)

inductive StrictOrderError where
  | outOfOrder (pending appliedUpTo : String)
  deriving DecidableEq, Repr

def checkStrictOrder (files : List MigrationId) (applied : List String) :
    Except StrictOrderError Unit :=
  match maxVersion? applied with
  | none => .ok ()
  | some max =>
    let rec go : List MigrationId → Except StrictOrderError Unit
      | [] => .ok ()
      | f :: rest =>
        if !versionIn applied f.version && decide (f.version < max) then
          .error (.outOfOrder f.version max)
        else
          go rest
    go files

def endsWithUnderscore (s : String) : Bool :=
  endsWithSuffix s "_"

def trimUnderscores (s : String) : String :=
  let chars := s.toList
  let dropL := chars.dropWhile (· == '_')
  let dropR := dropL.reverse.dropWhile (· == '_')
  String.ofList dropR.reverse

def slugify (name : String) : String :=
  let step := name.toList.foldl (init := "") fun out c =>
    if c.isAlphanum then out.push c.toLower
    else if endsWithUnderscore out then out
    else out.push '_'
  let trimmed := trimUnderscores step
  if trimmed.isEmpty then "migration" else trimmed

def dumpHeader (applied : List String) (files : List MigrationId) : String :=
  let header := "-- Schema dumped by tqlmate\n-- Applied migrations:\n"
  let body :=
    if applied.isEmpty then "--   (none)\n"
    else
      String.join <| applied.map fun v =>
        match files.find? (fun m => m.version == v) with
        | some m => s!"--   {m.label}\n"
        | none => s!"--   {v}\n"
  header ++ body ++ "\n"

def stripDumpHeader (text : String) : String :=
  let lines := text.splitOn "\n"
  let rest := lines.dropWhile fun l =>
    let t := trimSpaces l
    t.isEmpty || startsWithPref t "--"
  String.intercalate "\n" rest

end TqlmateExtract.Spec
