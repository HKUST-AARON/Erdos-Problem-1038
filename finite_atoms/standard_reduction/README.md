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
and its objective invariance remain upstream work.

`lean/ComponentAtomization.lean` packages the barycenter-replacement part of
the variation argument.  It exposes objective non-increase from countable or
finite support-hit certificates and the secondary-minimizer consequence that a
caller-supplied tested block must already be a Dirac mass.  It now also
specializes this rigidity statement to the canonical normalized component
block and proves the measure-level bridge

```lean
componentBlock C = componentMass C • Measure.dirac (componentBarycenter C)
```

from normalized-block Dirac rigidity.  The remaining upstream input in this
layer is the actual Tao variation data selecting the positive component and
providing the replacement/secondary-objective hypotheses.

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
