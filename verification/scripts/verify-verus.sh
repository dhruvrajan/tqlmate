#!/usr/bin/env bash
# Verify the Verus migrate/rollback core (verification/verus).
#
# Usage (from repo root):
#   ./verification/scripts/verify-verus.sh
#
# Env:
#   VERUS           path to `verus` binary (default: verus on PATH, or ~/verus/verus-x86-linux/verus)
#   VERUS_VERSION   release tag suffix, e.g. 0.2026.09.20.aef82ed (used only when auto-installing)
#   VERUS_RLIMIT    SMT resource limit (default: 80)

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CORE="$ROOT/verification/verus/src/lib.rs"
if [[ -f "$ROOT/verification/VERSIONS" ]]; then
  # shellcheck disable=SC1090
  VERUS_VERSION="${VERUS_VERSION:-$(grep -E '^verus=' "$ROOT/verification/VERSIONS" | cut -d= -f2)}"
fi
VERUS_VERSION="${VERUS_VERSION:-0.2026.09.20.aef82ed}"
VERUS_RLIMIT="${VERUS_RLIMIT:-80}"

resolve_verus() {
  if [[ -n "${VERUS:-}" ]]; then
    echo "$VERUS"
    return
  fi
  if command -v verus >/dev/null 2>&1; then
    command -v verus
    return
  fi
  local candidate="$HOME/verus/verus-x86-linux/verus"
  if [[ -x "$candidate" ]]; then
    echo "$candidate"
    return
  fi
  return 1
}

install_verus_linux() {
  local dest="$HOME/verus"
  local zip="/tmp/verus-${VERUS_VERSION}-x86-linux.zip"
  local url="https://github.com/verus-lang/verus/releases/download/release/${VERUS_VERSION}/verus-${VERUS_VERSION}-x86-linux.zip"
  mkdir -p "$dest"
  echo "Downloading Verus ${VERUS_VERSION} ..."
  curl -sL -o "$zip" "$url"
  unzip -qo "$zip" -d "$dest"
  # Install matching rustup toolchain if needed.
  local verus_bin="$dest/verus-x86-linux/verus"
  if ! "$verus_bin" --version >/dev/null 2>&1; then
    # Parse toolchain hint from verus error, or use known pin.
    rustup install 1.98.1-x86_64-unknown-linux-gnu >/dev/null
  fi
  echo "$verus_bin"
}

VERUS_BIN="$(resolve_verus || true)"
if [[ -z "${VERUS_BIN}" ]]; then
  if [[ "$(uname -s)" == "Linux" && "$(uname -m)" == "x86_64" ]]; then
    VERUS_BIN="$(install_verus_linux)"
  else
    echo "error: verus not found; install from https://github.com/verus-lang/verus/releases" >&2
    echo "       then set VERUS=/path/to/verus" >&2
    exit 1
  fi
fi

# Ensure toolchain (verus prints instructions if missing).
if ! "$VERUS_BIN" --version >/dev/null 2>&1; then
  rustup install 1.98.1-x86_64-unknown-linux-gnu
fi

echo "Using: $VERUS_BIN"
"$VERUS_BIN" --version || true
echo "Verifying $CORE ..."
"$VERUS_BIN" --crate-type=lib "$CORE" --rlimit "$VERUS_RLIMIT" --triggers-mode silent
