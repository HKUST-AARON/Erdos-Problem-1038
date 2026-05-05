#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
: "${MATHLIB_WORKSPACE:?Set MATHLIB_WORKSPACE=/path/to/mathlib and retry.}"
JOBS="${PIECEWISE_BOX_JOBS:-8}"
LEAN_ROOT="$ROOT/lean"
BUILD="/tmp/erdos1038_piecewise_box_list_olean"
rm -rf "$BUILD"
mkdir -p "$BUILD"
cd "$MATHLIB_WORKSPACE"
lake env lean -R "$LEAN_ROOT" -o "$BUILD/PiecewiseFiveAtom181460Mathlib.olean" "$LEAN_ROOT/PiecewiseFiveAtom181460Mathlib.lean"
LEAN_PATH="$BUILD" lake env lean -R "$LEAN_ROOT" -o "$BUILD/PiecewiseFiveAtom181460BoxCore.olean" "$LEAN_ROOT/PiecewiseFiveAtom181460BoxCore.lean"
LEAN_PATH="$BUILD" lake env lean -R "$LEAN_ROOT" -o "$BUILD/PiecewiseFiveAtom181460BoxListCore.olean" "$LEAN_ROOT/PiecewiseFiveAtom181460BoxListCore.lean"
find "$LEAN_ROOT/box_list_chunks" -name 'PiecewiseFiveAtom181460BoxList*.lean' | sort > "$BUILD/chunks.txt"
echo "checking $(wc -l < "$BUILD/chunks.txt") piecewise Lean box-list chunks with jobs=$JOBS"
cat "$BUILD/chunks.txt" | xargs -P "$JOBS" -I{} bash -c 'LEAN_PATH="$0" lake env lean -R "$1" "$2" >/dev/null' "$BUILD" "$LEAN_ROOT" {}
echo "all piecewise Lean box-list chunks passed"
