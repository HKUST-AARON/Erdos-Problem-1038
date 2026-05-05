#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
: "${MATHLIB_WORKSPACE:?Set MATHLIB_WORKSPACE=/path/to/mathlib and retry.}"

if [[ ! -d "$MATHLIB_WORKSPACE" ]]; then
  echo "Mathlib workspace not found: $MATHLIB_WORKSPACE" >&2
  exit 1
fi

export MATHLIB_WORKSPACE

run_lean() {
  local file="$1"
  echo "checking ${file#$REPO_ROOT/}"
  (cd "$MATHLIB_WORKSPACE" && lake env lean "$file")
}

run_lean "$REPO_ROOT/finite_atoms/common/lean/FiniteAtomFramework.lean"
run_lean "$REPO_ROOT/finite_atoms/common/lean/StandardReduction.lean"
run_lean "$REPO_ROOT/finite_atoms/route_1807100/lean/Route1807100Closure.lean"

check_piecewise_181460_route() {
  local piece="$REPO_ROOT/finite_atoms/piecewise_five_atom_181460_560/lean"
  local route="$REPO_ROOT/finite_atoms/route_181460_560/lean/Route181460Closure.lean"
  local build="${PIECEWISE_ROUTE_BUILD:-/tmp/erdos1038_piecewise_dispatch_olean}"
  local jobs="${PIECEWISE_BOX_JOBS:-8}"
  echo "checking finite_atoms/piecewise_five_atom_181460_560/lean/PiecewiseFiveAtom181460Mathlib.lean"
  rm -rf "$build"
  mkdir -p "$build/box_list_chunks"
  (cd "$MATHLIB_WORKSPACE" && \
    lake env lean -R "$piece" \
      -o "$build/PiecewiseFiveAtom181460Mathlib.olean" \
      "$piece/PiecewiseFiveAtom181460Mathlib.lean")
  echo "checking finite_atoms/piecewise_five_atom_181460_560/lean/PiecewiseFiveAtom181460Weights.lean"
  (cd "$MATHLIB_WORKSPACE" && \
    LEAN_PATH="$build" lake env lean -R "$piece" \
      -o "$build/PiecewiseFiveAtom181460Weights.olean" \
      "$piece/PiecewiseFiveAtom181460Weights.lean")
  (cd "$MATHLIB_WORKSPACE" && \
    LEAN_PATH="$build" lake env lean -R "$piece" \
      -o "$build/PiecewiseFiveAtom181460BoxCore.olean" \
      "$piece/PiecewiseFiveAtom181460BoxCore.lean")
  (cd "$MATHLIB_WORKSPACE" && \
    LEAN_PATH="$build" lake env lean -R "$piece" \
      -o "$build/PiecewiseFiveAtom181460BoxListCore.olean" \
      "$piece/PiecewiseFiveAtom181460BoxListCore.lean")
  find "$piece/box_list_chunks" -name 'PiecewiseFiveAtom181460BoxList*.lean' | sort > "$build/chunks.txt"
  echo "checking $(wc -l < "$build/chunks.txt") piecewise Lean box-list chunks with jobs=$jobs"
  (cd "$MATHLIB_WORKSPACE" && \
    cat "$build/chunks.txt" | xargs -P "$jobs" -I{} bash -c '
      src="$2"
      base="$(basename "$src" .lean)"
      LEAN_PATH="$0" lake env lean -R "$1" -o "$0/box_list_chunks/$base.olean" "$src" >/dev/null
    ' "$build" "$piece" {})
  echo "checking finite_atoms/piecewise_five_atom_181460_560/lean/PiecewiseFiveAtom181460Formal.lean"
  (cd "$MATHLIB_WORKSPACE" && \
    LEAN_PATH="$build" lake env lean -R "$piece" \
      -o "$build/PiecewiseFiveAtom181460Formal.olean" \
      "$piece/PiecewiseFiveAtom181460Formal.lean")
  mkdir -p "$build/finite_atoms/common/lean"
  (cd "$MATHLIB_WORKSPACE" && \
    lake env lean -R "$REPO_ROOT" \
      -o "$build/finite_atoms/common/lean/StandardReduction.olean" \
      "$REPO_ROOT/finite_atoms/common/lean/StandardReduction.lean")
  echo "checking finite_atoms/route_181460_560/lean/Route181460Closure.lean"
  (cd "$MATHLIB_WORKSPACE" && \
    LEAN_PATH="$build:$REPO_ROOT${LEAN_PATH:+:$LEAN_PATH}" \
      lake env lean -R "$REPO_ROOT" "$route")
}

check_piecewise_181460_route

run_lean "$REPO_ROOT/finite_atoms/five_atom_1807100/lean/FiveAtom1807100Formal.lean"
run_lean "$REPO_ROOT/finite_atoms/five_atom_1807100/lean/FiveAtom1807100Mathlib.lean"
echo "checking finite_atoms/five_atom_1807100/lean/FiveAtom1807100BoxCertificate.lean"
FIVE_ROOT="$REPO_ROOT/finite_atoms/five_atom_1807100/lean"
FIVE_BUILD="/tmp/erdos1038_five_atom_olean"
rm -rf "$FIVE_BUILD"
mkdir -p "$FIVE_BUILD"
(cd "$MATHLIB_WORKSPACE" && \
  lake env lean -R "$FIVE_ROOT" \
    -o "$FIVE_BUILD/FiveAtom1807100Mathlib.olean" \
    "$FIVE_ROOT/FiveAtom1807100Mathlib.lean")
(cd "$MATHLIB_WORKSPACE" && \
  LEAN_PATH="$FIVE_BUILD" \
  lake env lean -R "$FIVE_ROOT" \
    "$FIVE_ROOT/FiveAtom1807100BoxCertificate.lean")
run_lean "$REPO_ROOT/finite_atoms/five_atom_1807100/lean/FiveAtom1807100Route.lean"

run_lean "$REPO_ROOT/finite_atoms/forcing_1708/lean/Forcing1708Formal.lean"
run_lean "$REPO_ROOT/finite_atoms/forcing_1708/lean/Forcing1708AnalyticKernel.lean"
run_lean "$REPO_ROOT/finite_atoms/forcing_1708/lean/Forcing1708Mathlib.lean"

"$REPO_ROOT/finite_atoms/forcing_1708/scripts/check_aggregate.sh"

"$REPO_ROOT/finite_atoms/piecewise_five_atom_181460_560/scripts/verify_piecewise_181460_560_test.sh"

echo "all finite-atom certificate checks passed"
