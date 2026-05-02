# Erdős Problem 1038

Lean certificate work for [Erdős Problem #1038](https://www.erdosproblems.com/1038).

## Problem

For a non-constant monic polynomial $f$ whose roots are all real and lie in $[-1,1]$, determine the infimum and supremum of

$$
\bigl\lvert \{x\in\mathbb{R}:\ |f(x)|<1\}\bigr\rvert .
$$

Equivalently, for the logarithmic potential attached to the empirical root measure, one studies the length of the positive set $\{U>0\}$.

## Current result recorded here

The current finite-atom certificate route records the conditional target

$$
M=1.806304.
$$

The route has two checked finite certificate blocks:

1. A two-parameter forcing branch before the tail block.
2. A five-atom tail block, including a full pole-free one-variable interval-box certificate.

The exact route arithmetic is also checked:

```text
1.708 + (1.806304 - 1.708) = 1.806304
1.806304 < 1.836
```

The standard minimizer reduction and the logarithmic-potential duality/sweep
framework are external mathematical inputs from the notes/comments. This
repository formalizes the finite certificate pieces and the route arithmetic
around them.

## How to cite this package in a forum comment

Use the five-atom folder as the direct reference:

[finite_atoms/five_atom_1806304](https://github.com/HKUST-AARON/Erdos-Problem-1038/tree/main/finite_atoms/five_atom_1806304)

A concise description is:

> This is a Lean-checked finite-certificate package for the conditional
> $M=1.806304$ finite-atom update. It includes the forcing-branch aggregate
> checks, the five-atom tail certificate, and an unconditional pole-free
> one-variable interval-box proof for the five-atom potential.

### Five-atom tail block

The first checked block is the five-atom tail certificate at

$$
M=1.806304.
$$

It belongs to the finite-atom dual-certificate route. The idea is to place a small positive measure outside a candidate positive set and prove that its logarithmic potential is positive on the allowed support of the primal measure. The symmetry identity for logarithmic potentials then forces at least one point in each moving finite set to lie in $\lbrace U>0\rbrace$. Sweeping the parameter gives extra length.

Folder:

```text
finite_atoms/five_atom_1806304/
```

Lean files:

```text
finite_atoms/five_atom_1806304/lean/FiveAtom1806304Mathlib.lean
finite_atoms/five_atom_1806304/lean/FiveAtom1806304BoxCertificate.lean
finite_atoms/five_atom_1806304/lean/FiveAtom1806304Formal.lean
finite_atoms/five_atom_1806304/lean/FiveAtom1806304Route.lean
```

### Forcing branch before the tail block

The second checked block is the two-parameter forcing branch used before the
five-atom tail argument:

$$
a\in[-1.7,-\sqrt2],\qquad b=s(1.82+a),\qquad s\in[0,1],
$$

$$
\nu_{a,b}=\delta_a+(1.395-b)\delta_b+C(a,b)\delta_{1.071-b},
$$

where $C(a,b)$ is chosen by $U_{\nu_{a,b}}(-1)=10^{-4}$.

Folder:

```text
finite_atoms/forcing_1708/
```

This folder contains:

- fixed-constant and domain-arithmetic Lean proofs;
- the generic `Real.log` interval-box soundness lemma;
- exact rational arithmetic checks for 980 boxes;
- finite coverage checks for 23010 elementary cells;
- box-wise scaled-log analytic precondition checks for the recorded logarithmic bounds.

### Common finite-atom framework

The shared finite dual-forcing implication is in:

```text
finite_atoms/common/lean/FiniteAtomFramework.lean
```

It proves the three-atom and five-atom selector lemmas used after the duality
identity turns positivity of the dual potential into a positive weighted sum.

### Route closure

The finite-route bookkeeping entry point is in:

```text
finite_atoms/route_1806304/lean/Route1806304Closure.lean
```

It proves the exact closing arithmetic

```text
1.708 + (1.806304 - 1.708) = 1.806304
1.806304 < 1.836
```

and packages the final route as an implication from the long forcing
contribution, the tail contribution, and the disjoint-additivity rule.

Later stronger finite-atom certificates, two-interval certificates, and global-dual attempts can go in separate folders.

## Check all finite-atom certificates

The local Mathlib workspace used for these checks is not vendored in this
repository. On this machine the default is:

```bash
/Users/aaron/Downloads/erdos数学问题
```

Run every current finite-atom Lean check with:

```bash
finite_atoms/check_all.sh
```

If Mathlib is in another local folder, run:

```bash
MATHLIB_WORKSPACE=/path/to/mathlib finite_atoms/check_all.sh
```
