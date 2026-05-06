# Route closure for the 1.814600 finite-atom package

This folder contains the route-level Lean file for the piecewise five-atom tail
certificate at

```text
M = 1.814600.
```

The main file is:

```text
lean/Route181460Closure.lean
```

It connects three route-side inputs to the lower bound for the augmented
unit-interval positive set:

```text
Route181460EndpointData.normalizedSupport
Route181460EndpointData.forcing1708Strong
Route181460EndpointData.tailMassFinite
```

For callers that have the more global unit-interval off-diagonal tail-mass
condition, the route-specific tail-mass field is built automatically by:

```text
Route181460EndpointData.of_unitInterval_offDiagonal
augmented_positiveSet_volume_lower_bound_from_forcing1708Strong_or_unitIntervalOffDiagonal
```

The packaged theorem is:

```text
Route181460EndpointData.lower_bound
```

It is a thin wrapper around the existing route handoff theorem:

```text
augmented_positiveSet_volume_lower_bound_from_forcing1708Strong_or_tailMass
```

## Verification policy

The 1.814600 route imports the 560 piecewise box-list chunks. Those chunks have
already been verified repeatedly and are expensive to rebuild. The default
repository check therefore skips the 560-chunk rebuild.

To opt in to the expensive full rebuild, run:

```bash
CHECK_PIECEWISE_181460_CHUNKS=1 \
MATHLIB_WORKSPACE='/path/to/mathlib-workspace' \
bash finite_atoms/check_all.sh
```

For ordinary route-wrapper work, do not rerun the 560 chunks unless their source
files changed.
