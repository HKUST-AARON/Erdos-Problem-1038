# Erdős Problem 1038

Lean work for [Erdős Problem #1038](https://www.erdosproblems.com/1038).

## Problem

For a non-constant monic polynomial $f$ whose roots are all real and lie in $[-1,1]$, determine the infimum and supremum of

$$
\bigl\lvert \lbrace x\in\mathbb{R}:\ \lvert f(x)\rvert<1 \rbrace \bigr\rvert .
$$

Equivalently, for the logarithmic potential attached to the empirical root measure, one studies the length of the positive set $\lbrace U>0\rbrace$.

## Current formal blocks

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

Later stronger finite-atom certificates, two-interval certificates, and global-dual attempts will go in separate folders.
