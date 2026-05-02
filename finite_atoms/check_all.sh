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
run_lean "$REPO_ROOT/finite_atoms/route_1806304/lean/Route1806304Closure.lean"

run_lean "$REPO_ROOT/finite_atoms/five_atom_1806304/lean/FiveAtom1806304Formal.lean"
run_lean "$REPO_ROOT/finite_atoms/five_atom_1806304/lean/FiveAtom1806304Mathlib.lean"
echo "checking finite_atoms/five_atom_1806304/lean/FiveAtom1806304BoxCertificate.lean"
FIVE_ROOT="$REPO_ROOT/finite_atoms/five_atom_1806304/lean"
FIVE_BUILD="/tmp/erdos1038_five_atom_olean"
rm -rf "$FIVE_BUILD"
mkdir -p "$FIVE_BUILD"
(cd "$MATHLIB_WORKSPACE" && \
  lake env lean -R "$FIVE_ROOT" \
    -o "$FIVE_BUILD/FiveAtom1806304Mathlib.olean" \
    "$FIVE_ROOT/FiveAtom1806304Mathlib.lean")
(cd "$MATHLIB_WORKSPACE" && \
  LEAN_PATH="$FIVE_BUILD" \
  lake env lean -R "$FIVE_ROOT" \
    "$FIVE_ROOT/FiveAtom1806304BoxCertificate.lean")
run_lean "$REPO_ROOT/finite_atoms/five_atom_1806304/lean/FiveAtom1806304Route.lean"

run_lean "$REPO_ROOT/finite_atoms/forcing_1708/lean/Forcing1708Formal.lean"
run_lean "$REPO_ROOT/finite_atoms/forcing_1708/lean/Forcing1708AnalyticKernel.lean"
run_lean "$REPO_ROOT/finite_atoms/forcing_1708/lean/Forcing1708Mathlib.lean"

"$REPO_ROOT/finite_atoms/forcing_1708/scripts/check_aggregate.sh"

echo "all finite-atom certificate checks passed"
