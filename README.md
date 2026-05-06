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

The current Lean files prove several downstream consequences of the Tao/natso standard reduction, but the full variational reduction is not yet closed.

What is already formalized:

- normalized endpoint-mass data imply the baseline positive interval, up to the logarithmic pole at the endpoint;
- the puncture at the endpoint has zero Lebesgue length;
- once the component argument supplies the right endpoint/support data, the support-shape and endpoint-mass algebra feeds into the normalized endpoint-potential interface;
- the finite-atom route can use this normalized endpoint-potential interface as its input.

What remains to be proved:

- the true lower-semicontinuity/minimizer-existence layer for the logarithmic-potential objective;
- the Tao positive-component/variation theorem that turns an arbitrary secondary minimizer into endpoint-normalized data;
- the selection of the actual maximal positive component and its open-left-cover/topological bookkeeping;
- the barycenter replacement and variance-minimization argument that atomizes each positive component.

In the Lean interfaces this remaining hard step is still represented by names such as

```text
TaoVariationalReductionInput
TaoVariationalReductionInputENNReal
EndpointRouteClosureENNReal.endpointFromVariation
```

These are not final theorems of the standard reduction. They mark the exact entry point where the remaining variational proof has to be supplied.

The 1.814600 branch uses a required-domain interpretation of positivity:

$$
U_{\lambda_a}(x)>0\ \text{on}\ \{-1\}\cup[0,1]
$$

for each block parameter $a\in[-A,-C]$, which corresponds to the $y$-domains
$[C-1,A-1]\cup[C,A+1]$ in the checker.

The middle interval $[A-1,C]$ corresponds to $x\in(-1,0)$ and is not part of the normalized support. Some blocks are negative there; this is recorded by the diagnostic output and is not used by the finite-atom argument.

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
