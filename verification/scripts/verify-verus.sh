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
VERSIONS_FILE="$ROOT/verification/VERSIONS"

if [[ -f "$VERSIONS_FILE" ]]; then
  VERUS_VERSION="${VERUS_VERSION:-$(grep -E '^verus=' "$VERSIONS_FILE" | cut -d= -f2)}"
  VERUS_RUST_TOOLCHAIN="${VERUS_RUST_TOOLCHAIN:-$(grep -E '^verus_rust_toolchain=' "$VERSIONS_FILE" | cut -d= -f2)}"
fi
VERUS_VERSION="${VERUS_VERSION:-0.2026.09.20.aef82ed}"
VERUS_RUST_TOOLCHAIN="${VERUS_RUST_TOOLCHAIN:-1.98.1-x86_64-unknown-linux-gnu}"
VERUS_RLIMIT="${VERUS_RLIMIT:-80}"

# Official release asset for the pinned version (Linux x86_64).
verus_linux_zip_url() {
  echo "https://github.com/verus-lang/verus/releases/download/release/${VERUS_VERSION}/verus-${VERUS_VERSION}-x86-linux.zip"
}

resolve_verus() {
  if [[ -n "${VERUS:-}" ]]; then
    if [[ ! -x "$VERUS" ]]; then
      echo "error: VERUS=$VERUS is not an executable file" >&2
      return 1
    fi
    printf '%s\n' "$VERUS"
    return 0
  fi
  if command -v verus >/dev/null 2>&1; then
    command -v verus
    return 0
  fi
  local candidate="$HOME/verus/verus-x86-linux/verus"
  if [[ -x "$candidate" ]]; then
    printf '%s\n' "$candidate"
    return 0
  fi
  return 1
}

install_verus_linux() {
  local dest="$HOME/verus"
  local zip="/tmp/verus-${VERUS_VERSION}-x86-linux.zip"
  local url
  url="$(verus_linux_zip_url)"
  local verus_bin="$dest/verus-x86-linux/verus"

  mkdir -p "$dest"

  # Progress / diagnostics must go to stderr so command substitution only captures the path.
  echo "Downloading Verus ${VERUS_VERSION} ..." >&2
  echo "  URL: $url" >&2
  # -f: fail on HTTP errors; -S: show error; -L: follow redirects to release-assets.
  if ! curl -fsSL -o "$zip" "$url"; then
    echo "error: failed to download Verus zip from $url" >&2
    echo "       check verification/VERSIONS verus= pin against" >&2
    echo "       https://github.com/verus-lang/verus/releases" >&2
    return 1
  fi
  if [[ ! -s "$zip" ]]; then
    echo "error: downloaded zip is missing or empty: $zip" >&2
    return 1
  fi

  echo "Unpacking to $dest ..." >&2
  if ! unzip -qo "$zip" -d "$dest"; then
    echo "error: unzip failed for $zip" >&2
    return 1
  fi

  if [[ ! -f "$verus_bin" ]]; then
    echo "error: expected Verus binary not found after unzip: $verus_bin" >&2
    echo "       zip contents:" >&2
    unzip -l "$zip" >&2 || true
    return 1
  fi
  chmod +x "$verus_bin"
  if [[ ! -x "$verus_bin" ]]; then
    echo "error: Verus binary is not executable: $verus_bin" >&2
    return 1
  fi

  # Install matching rustup toolchain if Verus cannot start yet.
  if ! "$verus_bin" --version >/dev/null 2>&1; then
    echo "Installing rustup toolchain ${VERUS_RUST_TOOLCHAIN} for Verus ..." >&2
    if ! command -v rustup >/dev/null 2>&1; then
      echo "error: rustup not found; install rustup then: rustup install ${VERUS_RUST_TOOLCHAIN}" >&2
      return 1
    fi
    rustup install "$VERUS_RUST_TOOLCHAIN"
  fi

  # Only the binary path goes to stdout (for command substitution).
  printf '%s\n' "$verus_bin"
}

ensure_toolchain() {
  local verus_bin="$1"
  if ! "$verus_bin" --version >/dev/null 2>&1; then
    echo "Installing rustup toolchain ${VERUS_RUST_TOOLCHAIN} for Verus ..." >&2
    if ! command -v rustup >/dev/null 2>&1; then
      echo "error: rustup not found; install rustup then: rustup install ${VERUS_RUST_TOOLCHAIN}" >&2
      return 1
    fi
    rustup install "$VERUS_RUST_TOOLCHAIN"
  fi
  if ! "$verus_bin" --version >/dev/null 2>&1; then
    echo "error: $verus_bin still cannot run after toolchain install" >&2
    "$verus_bin" --version >&2 || true
    return 1
  fi
}

# Capture only stdout (the path). resolve/install send diagnostics to stderr.
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

if [[ ! -x "$VERUS_BIN" ]]; then
  echo "error: resolved Verus path is not executable: '$VERUS_BIN'" >&2
  exit 1
fi

ensure_toolchain "$VERUS_BIN"

echo "Using: $VERUS_BIN" >&2
"$VERUS_BIN" --version >&2
echo "Verifying $CORE ..." >&2
"$VERUS_BIN" --crate-type=lib "$CORE" --rlimit "$VERUS_RLIMIT" --triggers-mode silent
