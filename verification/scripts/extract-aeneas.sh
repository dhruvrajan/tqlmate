#!/usr/bin/env bash
# Re-extract src/pure.rs via Charon → Aeneas → Lean.
# Requires: charon and aeneas on PATH (pins in verification/README.md).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
EXTRACT="$ROOT/verification/extract"
OUT="$ROOT/verification/lean/aeneas-generated"

command -v charon >/dev/null || { echo "charon not on PATH"; exit 1; }
command -v aeneas >/dev/null || { echo "aeneas not on PATH"; exit 1; }

cd "$EXTRACT"
charon cargo --preset=aeneas
mkdir -p "$OUT"
rm -f "$OUT"/*.lean
aeneas -backend lean -split-files -gen-lib-entry -dest "$OUT" tqlmate_extract.llbc
# Keep template + a filled FunsExternal (axioms for uncovered std helpers).
if [[ -f "$OUT/FunsExternal_Template.lean" && ! -f "$OUT/FunsExternal.lean" ]]; then
  cp "$OUT/FunsExternal_Template.lean" "$OUT/FunsExternal.lean"
fi
echo "Wrote Lean artefacts under $OUT"
