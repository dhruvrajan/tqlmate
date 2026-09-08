#!/usr/bin/env bash
# Re-extract src/pure.rs via Charon → Aeneas → Lean.
# Requires: charon and aeneas on PATH (pins in verification/VERSIONS).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
EXTRACT="$ROOT/verification/extract"
OUT="$ROOT/verification/lean/aeneas-generated"
LEAN="$ROOT/verification/lean"

command -v charon >/dev/null || { echo "charon not on PATH"; exit 1; }
command -v aeneas >/dev/null || { echo "aeneas not on PATH"; exit 1; }

cd "$EXTRACT"
charon cargo --preset=aeneas
mkdir -p "$OUT"
rm -f "$OUT"/*.lean
# Prefer computable defs so ExtrProperties can `native_decide` / `reducesTo`.
aeneas -backend lean -split-files -gen-lib-entry -all-computable -dest "$OUT" tqlmate_extract.llbc \
  || aeneas -backend lean -split-files -gen-lib-entry -dest "$OUT" tqlmate_extract.llbc

# Discard generated FunsExternal template — filled models live at
# TqlmateExtract/FunsExternal.lean and must not be overwritten by extract.
rm -f "$OUT/FunsExternal.lean" "$OUT/FunsExternal_Template.lean"

# Aeneas currently emits PartialOrd.lt/gt.default applied to the whole trait
# impl; Lean models expect the `partial_cmp` field. Normalize after extract.
if [[ -f "$OUT/Funs.lean" ]]; then
  python3 - "$OUT/Funs.lean" <<'PY'
import re, sys
path = sys.argv[1]
text = open(path).read()
pat = re.compile(
    r"(core\.cmp\.PartialOrd\.(?:lt|gt|le|ge)\.default)\s+(\w+(?:\.\w+)*)(?!\.partial_cmp)"
)
text2, n = pat.subn(r"\1 \2.partial_cmp", text)
open(path, "w").write(text2)
print(f"patched PartialOrd.default calls: {n}")
PY
  # Drop noncomputable section if -all-computable was unavailable.
  sed -i '/noncomputable section/d' "$OUT/Funs.lean"
fi

# Keep module path imports resolving: TqlmateExtract/{Types,Funs}.lean → generated.
ln -sfn ../aeneas-generated/Types.lean "$LEAN/TqlmateExtract/Types.lean"
ln -sfn ../aeneas-generated/Funs.lean "$LEAN/TqlmateExtract/Funs.lean"

echo "Wrote Lean artefacts under $OUT (and refreshed TqlmateExtract symlinks)"
