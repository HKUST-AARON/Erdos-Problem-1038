# Erdős Problem 1038

Lean formal proof artifacts for [Erdős Problem #1038](https://www.erdosproblems.com/1038).

## Problem

Determine the infimum and supremum of

```text
| { x ∈ ℝ : |f(x)| < 1 } |
```

where `f ∈ ℝ[x]` ranges over all non-constant monic polynomials whose roots are all real and lie in `[-1, 1]`.

## Current Lean formalization

The current formalized certificate is in:

```text
finite_atoms/five_atom_1806304/
```

It formalizes the five-atom tail-block certificate with:

```text
M = 1.806304
```

Main Lean files:

```text
finite_atoms/five_atom_1806304/lean/FiveAtom1806304Formal.lean
finite_atoms/five_atom_1806304/lean/FiveAtom1806304Mathlib.lean
```

Additional proof routes can be added later as separate folders.
