# Erdős Problem 1038

Lean work for [Erdős Problem #1038](https://www.erdosproblems.com/1038).

## Problem

For a non-constant monic polynomial `f` whose roots are all real and lie in `[-1, 1]`, determine the infimum and supremum of

```text
| { x ∈ ℝ : |f(x)| < 1 } |.
```

Equivalently, for the logarithmic potential attached to the empirical root measure, one studies the length of the positive set `{ U > 0 }`.

## What is here now

The first checked block is a five-atom tail certificate at

```text
M = 1.806304
```

It belongs to the finite-atom dual-certificate route. The idea is to place a small positive measure outside a candidate positive set and prove that its logarithmic potential is positive on the allowed support of the primal measure. The symmetry identity for logarithmic potentials then forces at least one point in each moving finite set to lie in `{ U > 0 }`. Sweeping the parameter gives extra length.

Folder:

```text
finite_atoms/five_atom_1806304/
```

Lean files:

```text
finite_atoms/five_atom_1806304/lean/FiveAtom1806304Formal.lean
finite_atoms/five_atom_1806304/lean/FiveAtom1806304Mathlib.lean
```

Later finite-atom certificates, two-interval certificates, and global-dual attempts will go in separate folders.
