# Standard reduction formalization

This directory contains the Lean-facing decomposition of the standard reduction
used by the finite-atom route.

The intent is to separate the analytic reduction into small, checkable layers
instead of hiding it behind a single external hypothesis.

## Current layer

`lean/LogPotentialTruncation.lean` packages the truncated logarithmic potential
objects already defined in `finite_atoms/common/lean/StandardReduction.lean`.
It proves:

- joint measurability of the truncated kernel on `R x [-1,1]`;
- measurability of the truncated unit-interval potential;
- measurability of truncated threshold and positive sets.

This is the first layer needed for the lower-semicontinuity and minimizer
existence part of the standard reduction.

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
