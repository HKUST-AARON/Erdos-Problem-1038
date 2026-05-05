#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
: "${MATHLIB_WORKSPACE:?Set MATHLIB_WORKSPACE=/path/to/mathlib and retry.}"
JOBS="${LEAN_JOBS:-6}"
BUILD="${FORCING1836_BOX_BUILD:-/tmp/erdos1038_forcing1836_box_olean}"
LEAN_DIR="$ROOT/lean"

rm -rf "$BUILD"
mkdir -p "$BUILD/box_arith_chunks"
find "$LEAN_DIR/box_arith_chunks" -name 'Forcing1836BoxArith*.lean' | sort > "$BUILD/chunks.txt"

echo "checking $(wc -l < "$BUILD/chunks.txt") forcing_1836 box arithmetic chunks with jobs=$JOBS"
(cd "$MATHLIB_WORKSPACE" && \
  cat "$BUILD/chunks.txt" | xargs -P "$JOBS" -I{} bash -c '
    build="$0"
    lean_dir="$1"
    src="$2"
    base="$(basename "$src" .lean)"
    lake env lean -R "$lean_dir" -o "$build/box_arith_chunks/$base.olean" "$src" >/dev/null
  ' "$BUILD" "$LEAN_DIR" {})

echo "checking finite_atoms/forcing_1836/lean/Forcing1836BoxData.lean"
(cd "$MATHLIB_WORKSPACE" && \
  LEAN_PATH="$BUILD${LEAN_PATH:+:$LEAN_PATH}" \
    lake env lean -R "$LEAN_DIR" "$LEAN_DIR/Forcing1836BoxData.lean")
