# Erdős Problem 1038

This repository contains Lean certificate files for a finite-atom lower-bound route related to [Erdős Problem #1038](https://www.erdosproblems.com/1038).

## Problem

For a non-constant monic polynomial $f$ whose roots are all real and lie in $[-1,1]$, determine the infimum and supremum of

$$
\bigl|\{x\in\mathbb{R}: |f(x)|<1\}\bigr|.
$$

In the logarithmic-potential formulation, one studies the length of a positive set of the form

$$
\{x: U_\mu(x)>0\}.
$$

## Current lower-bound certificate

The current files record a finite-atom certificate route at

$$
M=1.806304.
$$

The route has two finite certificate blocks:

1. A two-parameter forcing branch that supplies the long interval part.
2. A five-atom tail block that supplies the remaining length.

The exact closing arithmetic is checked in Lean:

```text
1.708 + (1.806304 - 1.708) = 1.806304
1.806304 < 1.836
```

The finite certificates are meant to be read together with the standard minimizer reduction and the usual logarithmic-potential duality/sweep framework used in the discussion of the problem. Those outer theoretical reductions are not duplicated as full measure-theoretic formalizations in this repository.

## Repository layout

```text
finite_atoms/five_atom_1806304/
```

The five-atom tail certificate. This is the main folder for the five-atom construction at $M=1.806304$. It includes the one-variable logarithmic potential, the pole-free interval-box certificate, exact arithmetic checks, and route bookkeeping for the tail sweep.

```text
finite_atoms/forcing_1708/
```

The preceding two-parameter forcing branch. It contains the interval certificate data and Lean checks for the branch that supports the long interval contribution.

```text
finite_atoms/common/
```

Shared finite-atom selector lemmas. These are the finite algebraic implications used after the logarithmic-potential duality identity has reduced the argument to a positive weighted sum over finitely many atoms.

```text
finite_atoms/route_1806304/
```

The route-level closure file. It checks the arithmetic that combines the long forcing contribution and the five-atom tail contribution to reach $M=1.806304$.

The separation into these folders follows the proof structure: common finite-atom logic, forcing branch, five-atom tail, and final arithmetic closure.

## Five-atom certificate

The five-atom tail block is in:

```text
finite_atoms/five_atom_1806304/
```

The measure used in the tail block is

$$
\lambda_a=
\delta_a
+1.174168821\,\delta_{a+1.80650001}
+0.025921118\,\delta_{a+2.57053197}
+0.118647936\,\delta_{a+2.68367709}
+0.180553554\,\delta_{a+2.79017717},
$$

for

$$
a\in[-1.806304,-1.708].
$$

The main one-variable theorem in the Lean files is

```text
poleFreeOneVariableLogPositivity_from_boxes
```

in

```text
finite_atoms/five_atom_1806304/lean/FiveAtom1806304BoxCertificate.lean
```

It proves the pole-free positivity of the five-atom logarithmic potential by a rational interval-box cover of the five smooth components between the poles.

## Check all finite-atom certificates

The repository does not vendor Mathlib. On this machine, the local Mathlib workspace is expected at:

```bash
/Users/aaron/Downloads/erdos数学问题
```

Run all current finite-atom checks with:

```bash
finite_atoms/check_all.sh
```

If Mathlib is elsewhere, set:

```bash
MATHLIB_WORKSPACE=/path/to/mathlib finite_atoms/check_all.sh
```
