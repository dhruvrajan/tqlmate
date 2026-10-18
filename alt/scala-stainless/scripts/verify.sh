#!/usr/bin/env bash
# Run Stainless on the verified core. Downloads stainless-dotty-standalone if needed.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
VERIFIED="$ROOT/verified/src"
CACHE="${STAINLESS_HOME:-$ROOT/.stainless}"
VERSION="${STAINLESS_VERSION:-0.10.3}"
ZIP_NAME="stainless-dotty-standalone-${VERSION}-linux.zip"
URL="https://github.com/epfl-lara/stainless/releases/download/v${VERSION}/${ZIP_NAME}"

mkdir -p "$CACHE"
STAINLESS_BIN=""
if [[ -x "$CACHE/stainless" ]]; then
  STAINLESS_BIN="$CACHE/stainless"
elif [[ -n "${STAINLESS_HOME:-}" && -x "${STAINLESS_HOME}/stainless" ]]; then
  STAINLESS_BIN="${STAINLESS_HOME}/stainless"
elif [[ -x /tmp/dl/stainless ]]; then
  STAINLESS_BIN=/tmp/dl/stainless
fi

if [[ -z "$STAINLESS_BIN" ]]; then
  echo "Downloading Stainless ${VERSION}…"
  tmp="$(mktemp -d)"
  curl -fL --retry 3 -o "$tmp/stainless.zip" "$URL"
  unzip -qo "$tmp/stainless.zip" -d "$CACHE"
  STAINLESS_BIN="$CACHE/stainless"
  if [[ ! -x "$STAINLESS_BIN" ]]; then
    STAINLESS_BIN="$(find "$CACHE" -type f -name stainless -perm -u+x | head -1)"
  fi
  rm -rf "$tmp"
fi

if [[ ! -x "$STAINLESS_BIN" ]]; then
  echo "error: stainless binary not found" >&2
  exit 1
fi

OUT="$ROOT/verified/stainless-report.txt"
mkdir -p "$(dirname "$OUT")"

echo "Running Stainless ($STAINLESS_BIN) on verified core…"
START=$(date +%s.%N)
set +e
"$STAINLESS_BIN" --no-colors --timeout=60 \
  "$VERIFIED/tqlmate/core/Codes.scala" \
  "$VERIFIED/tqlmate/core/Pure.scala" \
  "$VERIFIED/tqlmate/core/Lemmas.scala" \
  | tee "$OUT"
status=${PIPESTATUS[0]}
set -e
END=$(date +%s.%N)
WALL=$(python3 -c "print(f'{float('$END')-float('$START'):.2f}')")
echo "wall_sec=$WALL" | tee -a "$OUT"

echo "Report written to $OUT (exit $status)"
exit "$status"
