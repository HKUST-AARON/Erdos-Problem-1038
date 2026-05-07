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

## Current Finite-Atom Packages

The repository currently records two finite-atom lower-bound packages:

$$
M=1.807100.
$$

and

$$
M=1.814600 \quad\text{(piecewise five-atom, 560 blocks, conditional domain check).}
$$

Each package has the same two-part structure:

1. A two-parameter forcing branch that supplies the long interval part.
2. A five-atom tail block that supplies the remaining length.

The exact closing arithmetic is checked in Lean:

```text
1.708 + (1.807100 - 1.708) = 1.807100
1.708 + (1.814600 - 1.708) = 1.814600
```

The finite certificates are meant to be read together with the standard minimizer reduction and the usual logarithmic-potential duality/sweep framework used in the discussion of the problem. The finite route and the standard-reduction route are kept separate: the former checks concrete certificates after normalization, while the latter is the variational argument that should produce the normalized endpoint form.

## Standard-reduction status

The full Tao/natso standard reduction is not yet closed in Lean.

What is already formalized:

- normalized endpoint data imply baseline positivity and the `sqrt 2` baseline
  volume lower bound;
- endpoint/remainder bookkeeping for the canonical endpoint remainder;
- support uniqueness, zero-neighborhood, component atomization, normalized
  atomization, and replacement-rigidity bridges into the endpoint package;
- boundary-average bridge work once the needed right-endpoint hypotheses are
  supplied.

What remains genuinely unproved:

- select the real maximal positive component from a secondary minimizer;
- derive baseline placement and right-endpoint boundary data from that component;
- construct the barycenter replacement and prove primary objective nonincrease;
- use secondary minimality to force atomization/support uniqueness;
- remove the external provider interfaces such as `hPackageFromVariation`,
  `hEndpointFromVariation`, `TaoVariationalReductionInput`, and
  `TaoEndpointReductionInput`.

The finite-atom certificates depend on this normalized endpoint interface for
an unconditional original-problem statement.  Passing finite certificate checks
is therefore not by itself a proof of the full Standard Reduction.

## Verification Status

The checked repository status is:

```text
1.807100:
  Lean/Mathlib finite-atom tail certificate, route arithmetic, and forcing package checks.

1.814600:
  Lean/Mathlib exact geometry, block coverage, required-domain mapping,
  non-negative finite-atom selector, route arithmetic, tail sweep lemma,
  and route-level volume bookkeeping under the stated endpoint/forcing inputs.
  Generated 560-block required-domain certificate with Python verification.
  Required-domain worst margin: 9.534343713646365e-06.
  Bad required-domain blocks: 0.
```

The 1.814600 branch is therefore a verified required-domain finite-atom branch under the standard normalized-support reduction. It is not a full $[-1,1]$ positivity certificate, and it does not by itself prove the standard minimizer reduction.

## Repository layout

```text
finite_atoms/five_atom_1807100/
```

The five-atom tail certificate. This is the main folder for the five-atom construction at $M=1.807100$. It includes the one-variable logarithmic potential, the pole-free interval-box certificate, exact arithmetic checks, and route bookkeeping for the tail sweep.

```text
finite_atoms/forcing_1708/
```

The preceding two-parameter forcing branch. It contains the interval certificate data and Lean checks for the branch that supports the long interval contribution.

```text
finite_atoms/common/
```

Shared finite-atom selector lemmas and the normalized-support baseline interval lemma. These are the finite algebraic and real-variable implications used after the logarithmic-potential reduction has put the problem into normalized form.

```text
finite_atoms/route_1807100/
```

The route-level closure file. It checks the arithmetic that combines the long forcing contribution and the five-atom tail contribution to reach $M=1.807100$.

```text
finite_atoms/piecewise_five_atom_181460_560/
```

The piecewise five-atom 560-block branch for $M=1.814600$. It includes the exact
geometry checks, block weights, and required-domain positivity checker and
certificate output.

```text
finite_atoms/route_181460_560/
```

The route arithmetic for the piecewise branch, matching the same forcing split as
the 1.807100 folder.

The separation into these folders follows the proof structure: common finite-atom logic, forcing branch, five-atom tail, and final arithmetic closure.

## Five-atom certificate

The five-atom tail block is in:

```text
finite_atoms/five_atom_1807100/
```

The measure used in the tail block is

$$
\lambda_a=
\delta_a
+1.18287976\,\delta_{a+1.80710376}
+0.03349753\,\delta_{a+2.57979789}
+0.11739956\,\delta_{a+2.69319012}
+0.17267833\,\delta_{a+2.79229832},
$$

for

$$
a\in[-1.807100,-1.708].
$$

The main one-variable theorem in the Lean files is

```text
poleFreeOneVariableLogPositivity_from_boxes
```

in

```text
finite_atoms/five_atom_1807100/lean/FiveAtom1807100BoxCertificate.lean
```

It proves the pole-free positivity of the five-atom logarithmic potential by a rational interval-box cover of the five smooth components between the poles.
The 1.814600 branch contributes a generated required-domain certificate in
`finite_atoms/piecewise_five_atom_181460_560/certificates`.

## Check All Finite-Atom Files

The repository does not vendor Mathlib. Use any local Lean/Mathlib workspace and pass it through `MATHLIB_WORKSPACE`:

```bash
MATHLIB_WORKSPACE=/path/to/mathlib finite_atoms/check_all.sh
```

This runs the Lean files and the generated 560-block required-domain checker.
