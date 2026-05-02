# Erdős Problem 1038 proof packages

This repository collects proof packages for [Erdős Problem #1038](https://www.erdosproblems.com/1038).

## Problem

Determine the infimum and supremum of

$$
\lvert \lbrace x\in\mathbb{R}:\ \lvert f(x)\rvert<1 \rbrace \rvert
$$

as $f\in\mathbb{R}[x]$ ranges over all non-constant monic polynomials, all of whose roots are real and lie in the interval $[-1,1]$.

## Current package

[finite_atoms/five_atom_1806304](finite_atoms/five_atom_1806304/) contains a Lean/Mathlib formalization of the five-atom tail-block certificate with

```text
M = 1.806304.
```

Future packages can be added separately, for example stronger finite-atom certificates, two-interval dual certificates, or global dual-measure approaches.
