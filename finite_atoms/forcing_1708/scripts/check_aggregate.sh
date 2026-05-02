#!/usr/bin/env bash
set -euo pipefail
: "${MATHLIB_WORKSPACE:?Set MATHLIB_WORKSPACE=/path/to/mathlib and retry.}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_ROOT="$ROOT/lean"
BUILD_DIR="${LEAN_BUILD_DIR:-/tmp/erdos1038_forcing1708_olean}"
rm -rf "$BUILD_DIR"
mkdir -p "$BUILD_DIR/box_arith_chunks" "$BUILD_DIR/geometry_chunks" "$BUILD_DIR/coverage_chunks" "$BUILD_DIR/analytic_precondition_chunks"
compile_module() {
  local rel="$1"
  local out="$2"
  (cd "$MATHLIB_WORKSPACE" && lake env lean -R "$LEAN_ROOT" -o "$BUILD_DIR/$out.olean" "$LEAN_ROOT/$rel.lean")
}
compile_list() {
  local list_file="$1"
  local jobs="${LEAN_JOBS:-4}"
  xargs -n 2 -P "$jobs" bash -c 'compile_one() {
    local rel="$1"
    local out="$2"
    cd "$MATHLIB_WORKSPACE" && lake env lean -R "$LEAN_ROOT" -o "$BUILD_DIR/$out.olean" "$LEAN_ROOT/$rel.lean"
  }; compile_one "$0" "$1"' < "$list_file"
}
LIST_FILE="$BUILD_DIR/modules.txt"
: > "$LIST_FILE"
for n in $(seq 0 19); do i=$(printf "%02d" "$n"); echo "box_arith_chunks/Forcing1708BoxArith$i box_arith_chunks/Forcing1708BoxArith$i" >> "$LIST_FILE"; done
for n in $(seq 0 9); do i=$(printf "%02d" "$n"); echo "geometry_chunks/Forcing1708Geometry$i geometry_chunks/Forcing1708Geometry$i" >> "$LIST_FILE"; done
for n in $(seq 0 14); do i=$(printf "%02d" "$n"); echo "coverage_chunks/Forcing1708CoverageA$i coverage_chunks/Forcing1708CoverageA$i" >> "$LIST_FILE"; done
for n in $(seq 0 19); do i=$(printf "%02d" "$n"); echo "analytic_precondition_chunks/Forcing1708AnalyticPre$i analytic_precondition_chunks/Forcing1708AnalyticPre$i" >> "$LIST_FILE"; done
export MATHLIB_WORKSPACE LEAN_ROOT BUILD_DIR
compile_list "$LIST_FILE"
check_index() {
  local rel="$1"
  (cd "$MATHLIB_WORKSPACE" && LEAN_PATH="$BUILD_DIR${LEAN_PATH:+:$LEAN_PATH}" lake env lean -R "$LEAN_ROOT" "$LEAN_ROOT/$rel.lean")
}
check_index "Forcing1708BoxData"
check_index "Forcing1708GeometryIndex"
check_index "Forcing1708CoverageIndex"
check_index "Forcing1708AnalyticPreconditionsIndex"
