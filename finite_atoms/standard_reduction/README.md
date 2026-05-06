# Standard reduction formalization

This directory contains the Lean-facing decomposition of the standard reduction
used by the finite-atom route.

The intent is to separate the analytic reduction into small, checkable layers
instead of hiding it behind a single external hypothesis.

## Current layers

`lean/LogPotentialTruncation.lean` packages the truncated logarithmic potential
objects already defined in `finite_atoms/common/lean/StandardReduction.lean`.
It proves:

- joint measurability of the truncated kernel on `R x [-1,1]`;
- measurability of the truncated unit-interval potential;
- measurability of truncated threshold and positive sets.

This is the first layer needed for the lower-semicontinuity and minimizer
existence part of the standard reduction.

`lean/TruncatedObjective.lean` packages the countable truncated-sup surrogate
objective.  It proves measurability of the truncated-sup positive set and,
from compact threshold cores, lower semicontinuity and minimizer existence for
the surrogate objective.

`lean/LowerSemicontinuity.lean` packages the true relaxed objective

```lean
unitIntervalPositiveSetObjective
```

and proves that the diagonal-safe one-sided compact-core input implies:

- lower semicontinuity of the true objective;
- existence of a relaxed objective minimizer.

The preferred remaining analytic input at this layer is named
`OneSidedCompactCore`.  This avoids the too-strong requirement that singular
tail mass be uniformly stable under arbitrary weak perturbations.  A legacy
wrapper `CompactTailMassStability` is still present because older internal
bridges consume it, but it is not the preferred proof target.

`lean/MinimizerExistence.lean` packages the minimizer consequence as a named
`RelaxedMinimizer` object.  Its preferred constructor is
`exists_relaxed_minimizer_of_oneSidedCompactCore`.

`lean/VariationEndpoint.lean` isolates the hard endpoint input as
`EndpointFromVariation`.  Given endpoint-normalized data for the potential
presented to the finite-atom route, it proves the normalized endpoint-potential
consequences for any `RelaxedMinimizer`.  Reflection/translation normalization
and its objective invariance remain upstream work.  The file also provides the
narrower `ComponentPackageFromVariation` interface: if Tao's concrete
component/remainder package is supplied for each relaxed minimizer, the
endpoint data and baseline consequences are produced by the existing formal
packagers rather than by a generic endpoint-data hypothesis.

`lean/ComponentAtomization.lean` packages the barycenter-replacement part of
the variation argument.  It exposes objective non-increase from countable or
finite support-hit certificates and the secondary-minimizer consequence that a
caller-supplied tested block must already be a Dirac mass.  It now also
specializes this rigidity statement to the canonical normalized component
block and proves the measure-level bridge

```lean
componentBlock C = componentMass C • Measure.dirac (componentBarycenter C)
```

from normalized-block Dirac rigidity.  It also proves the support-order bridge
which turns this atomization statement into the `unique_support_in_component`
field once the selected support is contained in the actual topological support
and the barycenter has been normalized to `-1`.  The remaining upstream input
in this layer is the actual Tao variation data selecting the positive component
and providing the replacement/secondary-objective hypotheses.

The same file now also provides the canonical endpoint-remainder construction:
the remainder is `realMeasure μ` restricted to the complement of `{-1}`.  This
automatically supplies the a.e. support-in-support field, endpoint exclusion,
mass identity, and mass nonnegativity once the selected support contains the
actual topological support and the endpoint mass is identified with the mass at
`-1`.  The remaining inputs for this remainder bridge are the genuine analytic
ones: log-kernel integrability and the endpoint-plus-remainder potential lower
bound.  For the unmodified potential `unitIntervalLogPotential μ`, the
endpoint-plus-remainder decomposition is now proved as an equality, so the
canonical-remainder data only needs support containment and log-kernel
integrability.

The canonical endpoint construction has also been lifted one level higher to
the variation package itself.  The structure

```lean
CanonicalEndpointVariationPackageData
```

fixes the endpoint mass to `(realMeasure μ) {-1}` and fixes the remainder to
`endpointRemainder μ`.  Its converters build:

```lean
TaoVariationComponentPackage
TaoEndpointNormalizationData
TaoReducedPotentialData
NormalizedEndpointPotential
```

without asking downstream arguments to re-supply the endpoint/remainder
bookkeeping.  For the unmodified potential there is a constructor

```lean
CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential
```

which only keeps the support-containment and endpoint-remainder kernel
integrability inputs, because the potential decomposition is already proved by
the canonical endpoint-remainder equality.

The reusable theorem

```lean
endpointRemainder_kernel_integrable_of_normalized_support
```

derives endpoint-remainder kernel integrability from the normalized support
shape.  After the endpoint atom `-1` is removed, the canonical remainder is
a.e. supported on `[0,1]`, while every point in `BaselinePunctured` lies
strictly to the left of `0`.  Hence the logarithmic kernel is continuous on the
compact support region and is integrable against the endpoint remainder.  This
theorem can be passed directly to the existing
`CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential` constructor,
without adding another public constructor.

The component-order data now also gives the canonical-remainder support-order
form

```lean
endpointRemainder_ae_mem_Icc_xPlus_one_of_support_order
```

The same section records the small open-set boundary lemma

```lean
not_mem_of_isOpen_no_right_points
not_mem_positiveSet_of_continuousAt_no_right_points
no_right_positive_of_component_right_cover
```

which is the topological core for the later maximal-component step: if the
positive set is open and the selected right endpoint has no positive points
strictly to its right, then the endpoint is not itself positive.  The local
continuous-at version is the preferred interface for the real-valued
logarithmic potential, because global openness at diagonal atom points is not
the right target; endpoint separation can instead supply continuity at the
selected boundary point.

This feeds the boundary-average bridge

```lean
boundary_average_of_endpointRemainder_boundary_distance
```

which reduces the algebraic `boundary_average` field to the analytic boundary
distance lower bound at the component right endpoint plus distance
integrability of the canonical endpoint remainder.

The boundary-distance lower bound itself is now connected to the boundary
potential sign through Jensen's logarithmic inequality:

```lean
endpointRemainder_boundary_distance_of_potential_nonpos
boundary_average_of_boundary_potential_nonpos
boundary_average_of_right_endpoint_not_positive
boundary_average_of_component_right_endpoint_not_positive
boundary_average_of_component_continuousAt_no_right_positive
boundary_average_of_component_right_cover
```

Thus the `boundary_average` field can be obtained from a nonpositive boundary
potential value at `xPlus`, standard distance/log integrability and separation
hypotheses, and the canonical endpoint-remainder support-order theorem above.
For a genuine maximal positive component, the latest bridge replaces the
nonpositive boundary-potential input by the more natural topological statement
that the right endpoint is not in the positive set.

The component-order versions derive the `boundary_average` field either from
right-endpoint non-positivity directly, or from the more primitive pair of
inputs expected from the maximal-component argument: local endpoint continuity
and absence of positive points strictly to the right.  The `right_cover`
variant replaces the latter with a maximal-component coverage statement:
every positive point to the right of `xMinus` lies in `(xMinus,xPlus)`.

The boundary Jensen step now also discharges the routine integrability
obligations from compact support and endpoint separation:

```lean
boundary_average_of_boundary_potential_nonpos_auto_integrable
boundary_average_of_component_right_cover_auto_integrable
CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential_right_cover
CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential_right_region
```

The constructor
`CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential_right_region`
is the direct maximal-component-facing entry point.  It consumes the
right-region identity

```lean
component = PositiveSet (unitIntervalLogPotential μ) ∩ Ioi xMinus
```

and derives both component positivity and right-cover from it.  The lower-level
constructor
`CanonicalEndpointVariationPackageData.of_unitIntervalLogPotential_right_cover`
remains available when a proof already has the cover statement directly.  These
constructors no longer ask callers to separately provide
integrability of `|xPlus - t|`, `Real.log |xPlus - t|`, the endpoint-remainder
distance integral, the boundary-average inequality, or the baseline kernel
integrability.  In the right-region constructor, no endpoint-continuity input is
needed: the identity above directly implies `xPlus` is not in the positive set.
The remaining analytic input at this point is the genuine separation statement
`∀ᵐ t ∂realMeasure μ, ε ≤ |xPlus - t|`, together with the right-region
component identity.

At the relaxed-minimizer interface, the same file defines

```lean
CanonicalComponentPackageFromVariation
```

and converts it to the existing
`VariationEndpoint.ComponentPackageFromVariation`.  This keeps the dependency
direction acyclic: `VariationEndpoint.lean` stays independent of component
atomization, while `ComponentAtomization.lean` provides the narrower canonical
provider and the baseline-length consequence built from it.  The diagonal-safe
path continues to use `OneSidedCompactCore`; it does not go through the older
compact tail-mass stability interface.

## Check command

From the repository root:

```bash
MATHLIB_WORKSPACE="/path/to/mathlib" bash finite_atoms/check_all.sh
```

The default check intentionally skips expensive certificate rebuilds that have
already been verified repeatedly:

- `CHECK_PIECEWISE_181460_CHUNKS=1` opts in to the `1.814600` 560-chunk rebuild;
- `CHECK_FORCING_1708_FULL=1` opts in to the older `1.708` forcing aggregate check;
- `CHECK_FORCING_1708_STRONG_FULL=1` opts in to the strong forcing box-arithmetic
  and Python verifier.
