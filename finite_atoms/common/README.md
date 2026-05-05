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

Formalizes the normalized-support consequence used by the standard reduction.
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

The file also separates the part of Tao's Section 3 reduction that is purely
order/algebra from the heavier variational part:

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

## Standard-reduction status after the current mathematical audit

The pure mathematical reduction has been written as the following chain:

1. Lower semicontinuity of the relaxed objective gives a minimizer.
2. Among minimizers, choose one with minimal variance.
3. A positive component has positive mass.
4. Barycenter replacement outside that component does not increase the
   logarithmic potential on the complement, hence does not increase the
   positive-set length.
5. Variance rigidity forces the restriction of the minimizer to each positive
   component to be a Dirac mass at its barycenter.
6. The mean-sign lemma gives a component containing `(-1,0)` after reflection.
7. Translation of the selected component atom to `-1` gives normalized support
   in `{-1} ∪ [0,1]`.
8. The boundary-average argument gives endpoint mass at least `1/2`; the
   degenerate `x_+ = 0` case is handled separately by the two-point/reflection
   case.

The Lean file has internalized several downstream pieces of this chain:

```text
measure_barycenter_logKernel_replacement_le_of_strictOutside_Ioo
integral_realMeasure_eq_outside_add_componentBlock
integral_componentReplacementMeasure_eq
unitIntervalLogPotential_eq_outside_add_componentBlock_logKernel
componentReplacementPotential_eq_outside_add_barycenter_logKernel
componentReplacement_potential_le_of_decomposition_and_block_jensen
componentReplacement_objective_le_of_strictOutside_decomposition_jensen
componentReplacement_objective_le_of_strictOutside_logKernel_jensen
measure_barycenter_second_moment_eq_imp_eq_dirac_at_mean
endpoint_lower_bound_from_normalized_support_decomposition
endpoint_mass_ge_half_from_boundary_average
endpoint_mass_ge_half_from_boundary_average_nonneg_or_degenerate
TaoComponentReductionData.support_subset_normalized
TaoComponentReductionData.endpointMass_ge_half
TaoReducedPotentialData.toNormalizedEndpointPotential
```

The most recent additions in this layer are:

```text
endpoint_lower_bound_from_normalized_support_decomposition
endpoint_mass_ge_half_from_boundary_average_nonneg_or_degenerate
```

The first is the named support-decomposition-to-endpoint-lower-bound bridge.
The second matches the mathematical proof's split between `x_+ > 0` and the
degenerate two-point `x_+ = 0` case.

The component-replacement layer now also has an explicit assembly bridge:
Lean decomposes integration against the original measure into outside plus
component-block terms, decomposes integration against the replacement measure
into outside plus barycenter-atom terms, and then assembles these scalar
decompositions with the Jensen comparison into pointwise replacement-potential
inequality and objective non-increase theorems.

The newest bridge specializes this assembly to the actual logarithmic kernel
`t ↦ log (1 / |x - t|)`: given the needed log-kernel integrability assumptions
and the Jensen comparison for every strict outside point, Lean now derives the
component-replacement objective non-increase directly.

The following review findings remain real Lean gaps, not solved claims:

```text
1. The core variational provider is still external:
   TaoVariationalReductionInput.reducedData is an input, not yet a theorem.

2. The actual objective
   μ ↦ volume {x | 0 < unitIntervalLogPotential μ x}
   has not yet been proved lower semicontinuous end-to-end.

3. The component-replacement objective lemma still consumes the outside
   log-kernel integrability and Jensen-comparison data as assumptions.  The
   measure-level integral decompositions, log-kernel specialization, and scalar
   assembly are formalized, but deriving those analytic hypotheses
   automatically from an arbitrary minimizer component is not yet closed.

4. PositiveComponent is still supplied as structure; the extraction of the
   relevant component from a minimizer, with boundary and replacement legality,
   is not fully formalized.

5. Endpoint lower bound is still packaged as data in TaoReducedPotentialData.
   The normalized-remainder bridge exists, but the full support decomposition
   from an arbitrary minimizer is not yet internalized.
```

So the current honest status is:

```text
pure mathematical standard-reduction route: written and clarified;
Lean formalization: downstream bridges are growing, but the full variational
provider and true-objective l.s.c. are still open formalization tasks.
```

Check command from the repository root:

```bash
MATHLIB_WORKSPACE=/path/to/mathlib finite_atoms/check_all.sh
```
