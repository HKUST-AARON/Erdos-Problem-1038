# Erdős Problem 1038

Lean work for [Erdős Problem #1038](https://www.erdosproblems.com/1038).

## Problem

For a non-constant monic polynomial `f` whose roots are all real and lie in `[-1, 1]`, determine the infimum and supremum of

```text
| { x ∈ ℝ : |f(x)| < 1 } |.
```

## What is here now

The first checked block is a five-atom tail certificate at

```text
M = 1.806304
```

Folder:

```text
finite_atoms/five_atom_1806304/
```

Lean files:

```text
finite_atoms/five_atom_1806304/lean/FiveAtom1806304Formal.lean
finite_atoms/five_atom_1806304/lean/FiveAtom1806304Mathlib.lean
```

I will keep later finite-atom certificates, two-interval certificates, and global-dual attempts in separate folders.
