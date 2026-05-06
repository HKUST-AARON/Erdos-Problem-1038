# Common finite-atom framework

This folder contains Lean lemmas shared by the finite-atom certificate route.

```text
lean/FiniteAtomFramework.lean
```

The file proves the finite dual-forcing implication used by both the forcing
branch and the five-atom tail block:

if a positive weighted finite atom sum is positive, and the primal potential is
non-positive outside a set `E`, then at least one atom lies in `E`.

It also proves the duality-to-selector interface:

```text
finite_atom_selector_from_duality
three_atom_selector_from_duality
five_atom_selector_from_duality
```

These theorems say that once a positive dual quantity is identified, via the
duality identity, with the finite weighted atom sum, the selector conclusion
follows.  The analytic proof of the logarithmic-potential integral identity is
not in this file; this file formalizes the finite step that follows from that
identity.

```text
lean/StandardReduction.lean
```

Records the current formal interface for the standard-reduction route.
This file should be read as a separation between the consequences already
proved after endpoint normalization and the variational theorem that still has
to produce that endpoint-normalized data.

Once the reduced potential has the endpoint lower bound coming from at least
half of the mass at `-1`, the file proves that the punctured baseline interval

```text
(-sqrt 2, 0) \\ {-1}
```

lies in the positive set.  The point `-1` is removed only because this Lean file
uses real-valued `Real.log`; at an atom the logarithmic potential is infinite in
the underlying potential-theoretic formulation.

The file also proves that this puncture does not change the Lebesgue length:

```text
baselinePunctured_volume
```

The normalized-support consequence is packaged for route-level use as:

```text
NormalizedEndpointPotential
NormalizedEndpointPotential.baseline_subset_positive
NormalizedEndpointPotential.baseline_length_le_positiveSet
StandardMinimizerReduction
standard_minimizer_reduction_baseline_length
```

`StandardMinimizerReduction` records the remaining external variational input:
that a minimizer can be put into normalized endpoint-mass form.  The lemmas
above prove all downstream baseline-interval consequences once that input is
available.

The file also separates the part of Tao's Section 3 reduction that is
order/algebra from the heavier positive-component and variation part:

```text
TaoComponentReductionData.support_subset_normalized
TaoComponentReductionData.endpointMass_ge_half
TaoReducedPotentialData.toNormalizedEndpointPotential
TaoReducedPotentialData.baseline_length_le_positiveSet
```

In words, once the component argument has selected the positive component
containing `(-1,0)`, the Lean file proves that the support is contained in
`{-1} ∪ [0,1]`, that the endpoint mass is at least `1/2`, and that these data
feed into the normalized endpoint-potential interface used by the finite-atom
certificate route.

## Standard-reduction route review

The route currently has three layers.

Closed downstream layer:

- endpoint lower-bound data imply baseline positivity;
- endpoint punctures do not change Lebesgue length;
- component endpoint/support hypotheses imply normalized support shape;
- endpoint-mass algebra gives the `1/2` endpoint lower bound once the boundary-average input is available.

Live standard-reduction layer:

- prove the true positive component selected from the positive set has the open-left-cover property required by the existing endpoint package;
- prove barycenter replacement for a positive component, using Jensen outside the component and variance decrease inside the component;
- use the variance-minimizing minimizer to show component atomization;
- connect the atomized component to the endpoint-normalized support/mass data.

Infrastructure layer still to be closed:

- lower semicontinuity of the actual logarithmic-potential objective;
- minimizer existence and secondary variance-minimizing minimizer existence;
- reflection/translation normalization from the selected component;
- the final polynomial-to-measure bridge for the original polynomial statement.

The main unproved standard-reduction entry points are still visible in the
Lean interface:

```text
TaoVariationalReductionInput
TaoVariationalReductionInputENNReal
EndpointRouteClosureENNReal.endpointFromVariation
```

These names should be treated as TODO boundaries, not as completed reduction
theorems.

The most useful next proof step is the component-topology bridge:

```text
selected maximal positive component
  -> open-left-cover near the endpoint
  -> endpoint package input
```

After that bridge is closed, the next target is the barycenter replacement and
variance-decrease argument that removes the remaining atomization input.

Check command from the repository root:

```bash
MATHLIB_WORKSPACE=/path/to/mathlib finite_atoms/check_all.sh
```
