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
run_lean "$REPO_ROOT/finite_atoms/route_181460_560/lean/Route181460Closure.lean"
run_lean "$REPO_ROOT/finite_atoms/piecewise_five_atom_181460_560/lean/PiecewiseFiveAtom181460Formal.lean"
run_lean "$REPO_ROOT/finite_atoms/piecewise_five_atom_181460_560/lean/PiecewiseFiveAtom181460Weights.lean"
run_lean "$REPO_ROOT/finite_atoms/piecewise_five_atom_181460_560/lean/PiecewiseFiveAtom181460Mathlib.lean"

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

# Piecewise 560-block five-atom tail candidate (M = 1.814600, conditional support).
"$REPO_ROOT/finite_atoms/piecewise_five_atom_181460_560/scripts/verify_piecewise_181460_560_test.sh"

echo "all finite-atom certificate checks passed"
