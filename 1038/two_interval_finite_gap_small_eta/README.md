# Two-Interval Finite-Gap Small-Eta Branch

This folder contains a separated proof-engineering artifact for the small-eta
singular end of the Erdős 1038 two-interval finite-gap route.

Status: certificate-backed diagnostics and interval-winding bridge, not a full
solution of Problem 1038.

## Scope

The current objective is local branch existence for the two-interval ansatz as
\(\varepsilon\to0^+\).  The already certified finite branch covers
\([10^{-8}, 0.002]\).  This folder records the separate bridge work below
\(10^{-8}\).

Current bridge evidence:

```text
limiting-center interval bridge:  [3e-16, 3e-10] PASS
corrected-center interval bridge: [3e-10, 1e-8] PASS
existing finite certificate:      [1e-8, 0.002] PASS
```

The remaining gap is not another sampled slab.  It is the final asymptotic
theorem for \(0<\varepsilon<3\cdot10^{-16}\), plus replacement of floating
center constants by a clean Arb/rational certificate.

## Files

```text
solve_two_interval_finite_gap.py
verify_two_interval_epsilon_slabs.py
verify_two_interval_continuation_tube.py
verify_two_interval_small_eta_limit.py
verify_two_interval_small_eta_remainder.py
verify_corrected_center_tube.py
verify_asymptotic_obligation.py
diagnose_interval_remainder_components.py
diagnose_k1_eta_floor.py
```

The folder keeps the route-specific solver/verifiers together so the forum
artifact is self-contained inside this subdirectory.

## Commands

Corrected-center bridge below `1e-8`:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/verify_corrected_center_tube.py \
  --epsilons 3e-10,1e-9,3e-9,1e-8 \
  --max-correction 0.002 \
  --tube-radius-B 0.002 \
  --tube-radius-tau 0.002 \
  --max-corrected-residual 1e-5 \
  --interval-boundary-winding 8,8 \
  --interval-boundary-winding-adaptive-depth 3
```

Expected summary:

```text
TWO-INTERVAL CORRECTED-CENTER TUBE: PASS-DIAGNOSTIC rows=4
interval_winding_checked=3
interval_winding_min_origin=8.394290e-04
```

Limiting-center bridge:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/verify_corrected_center_tube.py \
  --center-mode limiting \
  --epsilons 3e-12,1e-11,3e-11,1e-10,3e-10 \
  --max-correction 0.001 \
  --tube-radius-B 0.02 \
  --tube-radius-tau 0.02 \
  --max-corrected-residual 1e-4 \
  --interval-boundary-winding 8,8 \
  --interval-boundary-winding-adaptive-depth 3
```

Expected summary:

```text
TWO-INTERVAL CORRECTED-CENTER TUBE: PASS-DIAGNOSTIC rows=5
interval_winding_checked=4
interval_winding_min_origin=8.329573e-03
```

Deep limiting stress test:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/verify_corrected_center_tube.py \
  --center-mode limiting \
  --epsilons 3e-16,1e-15,3e-15,1e-14,3e-14,1e-13,3e-13,1e-12,3e-12 \
  --max-correction 0.001 \
  --tube-radius-B 0.02 \
  --tube-radius-tau 0.02 \
  --max-corrected-residual 1e-4 \
  --interval-boundary-winding 8,8 \
  --interval-boundary-winding-adaptive-depth 3
```

Expected summary:

```text
TWO-INTERVAL CORRECTED-CENTER TUBE: PASS-DIAGNOSTIC rows=9
interval_winding_checked=8
interval_winding_min_origin=8.354314e-03
```

Asymptotic obligation gate:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/verify_asymptotic_obligation.py
```

Expected summary:

```text
TWO-INTERVAL ASYMPTOTIC OBLIGATION:
theorem_status=OPEN
sampled_gate=PASS
target_bound=7.000000e-03
```

Component blocker diagnostic:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/diagnose_interval_remainder_components.py
```

Expected summary:

```text
TWO-INTERVAL INTERVAL REMAINDER COMPONENTS:
FAIL-DIAGNOSTIC ... blocker=K1
```

K1 eta-floor diagnostic:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/diagnose_k1_eta_floor.py
```

Expected summary:

```text
TWO-INTERVAL K1 ETA FLOOR:
PASS-DIAGNOSTIC ... conclusion='K1 endpoint-safe first-divided kernel controls eta floor'
```

## Caveat

This folder does not claim a complete proof of the 1038 infimum.  It is a
local two-interval branch artifact.  A global finite-gap reduction and a
matching upper construction are separate requirements.
