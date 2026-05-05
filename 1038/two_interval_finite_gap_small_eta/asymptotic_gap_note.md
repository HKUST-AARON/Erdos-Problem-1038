# Small-Eta Asymptotic Gap Note

This note records the current state of the remaining singular endpoint
\(0<\varepsilon<3\cdot10^{-16}\) for the two-interval finite-gap branch.

## Current Coverage

The local branch evidence is now split into three pieces:

```text
limiting-center interval bridge:  [3e-16, 3e-10] PASS
corrected-center interval bridge: [3e-10, 1e-8] PASS
existing finite certificate:      [1e-8, 0.002] PASS
```

The remaining uncovered interval is therefore:

```text
0 < epsilon < 3e-16
```

Equivalently,

```text
0 < eta < sqrt(3e-16) = 1.7320508075688772e-8
```

## Limiting Winding Target

The eta-zero limiting normal form is checked by:

```bash
.venv/bin/python 1038/verify_two_interval_small_eta_limit.py
```

Observed constants:

```text
degree_abs=1
limiting_min_origin=7.063335e-03
j00=7.063335324645e-01
forcing=2.222126305977e-01
curvature=-2.000677710756e-01
tau0=1.053891261372e+00
bottom_k2=2.058479813419e-02
top_k2=-2.158513698957e-02
min_structural_margin=1.833536e-01
```

The limiting boundary has a large margin compared with the observed positive
eta remainder.

## Remainder Diagnostics

The diagnostic comparison between the regularized positive-eta kernel and the
limiting normal form is:

```bash
.venv/bin/python 1038/verify_two_interval_small_eta_remainder.py \
  --eta-min 1e-16 \
  --eta-max 1e-8 \
  --eta-samples 9 \
  --edge-samples 8 \
  --renormalize-limit-layer \
  --fail-ratio 0.5
```

Observed summary:

```text
TWO-INTERVAL SMALL-ETA REMAINDER: PASS-DIAGNOSTIC
samples=288
failures=0
eta_min=1.000000e-16
eta_max=1.000000e-08
max_remainder=6.409310e-05
limiting_min_origin=7.063335e-03
ratio=9.074056e-03
```

This is not yet a proof.  It is sampled and uses floating boundary points.  But
it strongly indicates that the required uniform remainder bound is generous:
the observed remainder is below one percent of the limiting winding margin.

## Needed Lemma

The singular endpoint will close once the following lemma is certified:

> For \(0<\eta\le 1.7320508075688772\cdot10^{-8}\), on the rectangle
> \(B\in[-0.01,0.01]\), \(\tau\in[\tau_0-0.05,\tau_0+0.05]\),
> the regularized residual satisfies
> \[
> \|K_\eta(B,\tau)-K_0(B,\tau)\|_2
> < 7.0\cdot10^{-3}.
> \]

The observed diagnostic is much stronger:

```text
max sampled remainder ~= 6.41e-5
```

so even a very conservative proof bound should be enough.

## Next Proof-Grade Step

The next implementation should replace the sampled remainder diagnostic with
an Arb interval version:

1. use the existing `regularize_joint_limit_layer=True` residue-log kernels;
2. evaluate \(K_\eta-K_0\) on boundary boxes, not sampled points;
3. use an eta interval `(0, 1.7320508075688772e-8]`, handled by a limiting
   analytic expression rather than raw division by eta;
4. prove the interval norm is below the limiting boundary margin;
5. then combine this with the already passing interval bridge
   `[3e-16, 3e-10]` to close the full \(0<\varepsilon<10^{-8}\) singular gap.

Until that uniform interval remainder lemma exists, this remains a
certificate-backed route, not a completed proof of the singular endpoint.

## Why Not Keep Slicing Smaller?

An attempted deeper finite stress test confirms that pushing finite eta slabs
below the current bridge is the wrong proof strategy:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/verify_corrected_center_tube.py \
  --center-mode limiting \
  --epsilons 3e-32,1e-30,3e-28,1e-26,3e-24,1e-22,3e-20,1e-18,3e-16 \
  --max-correction 0.001 \
  --tube-radius-B 0.02 \
  --tube-radius-tau 0.02 \
  --max-corrected-residual 1e-4 \
  --interval-boundary-winding 8,8 \
  --interval-boundary-winding-adaptive-depth 3
```

Observed failure mode:

```text
epsilon=3.000000e-32 ... corrected_inf=1.065876e-01 degree=0
epsilon=1.000000e-30 ... corrected_inf=6.825498e-02 degree=0
...
interval slab ... status=FAIL
source=residue-log-mv u derivative: expected finite Arb ball, got nan
```

This should be read as a numerical/representation failure, not as evidence
against the branch.  At these eta values the finite positive-eta kernel is
being asked to resolve cancellations far below the precision and algebraic
conditioning of the current value/derivative primitives.

The conclusion is important:

```text
Do not close 0 < epsilon < 3e-16 by more finite slabs.
Close it by an eta=0 analytic remainder theorem.
```

The finite bridge is already close enough to zero that the remaining endpoint
must be handled by the limiting normal form plus a uniform remainder bound.

## Precision Stress Check

Raising the point-value precision does not remove the lower-eta failure:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/verify_corrected_center_tube.py \
  --center-mode limiting \
  --epsilons 1e-30,3e-28,1e-26 \
  --precision 1024 \
  --max-correction 0.001 \
  --tube-radius-B 0.02 \
  --tube-radius-tau 0.02 \
  --max-corrected-residual 1e-4
```

Observed:

```text
epsilon=1.000000e-30 ... corrected_inf=6.825498e-02 degree=0
epsilon=3.000000e-28 ... corrected_inf=1.128316e-03 degree=-1
epsilon=1.000000e-26 ... corrected_inf=1.741874e-04 degree=-1
TWO-INTERVAL CORRECTED-CENTER TUBE: FAIL-DIAGNOSTIC
```

The same behavior at 512-bit and 1024-bit precision indicates that this is not
a simple precision knob issue.  The finite positive-eta residue-log expression
has the wrong conditioning for the endpoint.  The proof must use the eta-zero
normal form and certify the remainder analytically.

## Component-Level Blocker

Direct interval probing on the full endpoint eta range
\([10^{-16},10^{-8}]\) shows that the second residual component is already
reasonably controlled by the regularized joint limit-layer kernel, while the
first component is not:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/diagnose_interval_remainder_components.py
```

Observed representative output:

```text
top-mid:   K1=[+/- 5.26] K2=[-0.022 +/- 5.35e-4]
right-mid: K1=[+/- 5.07] K2=[+/- 1.07e-4]
TWO-INTERVAL INTERVAL REMAINDER COMPONENTS:
FAIL-DIAGNOSTIC ... blocker=K1
```

So the remaining analytic kernel is more specific than "prove both
components": the immediate blocker is a proof-grade eta-zero first-divided
kernel for

```text
K1 = U(alpha) / eta.
```

The K2 branch already benefits from the combined residual-level cancellation;
K1 needs the analogous endpoint-safe first-divided treatment.

## K1 Eta-Floor Diagnostic

The K1 interval blow-up is localized at the endpoint eta floor.  Holding
`eta_high=1e-8` fixed and raising `eta_low` quickly restores a useful K1
interval:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/diagnose_k1_eta_floor.py
```

Observed:

```text
eta=[1e-16,1e-08] K1_radius=5.250000e+00
eta=[1e-12,1e-08] K1_radius=4.240000e-04
eta=[1e-10,1e-08] K1_radius=6.510000e-06
eta=[1e-09,1e-08] K1_radius=2.510000e-06
eta=[5e-09,1e-08] K1_radius=1.230000e-06
TWO-INTERVAL K1 ETA FLOOR: FAIL-DIAGNOSTIC ... radius_ratio=4.268293e+06
```

This confirms that the K1 obstruction is not broad instability on the whole
small-eta interval.  It is the removable singular endpoint at eta zero.  The
next kernel should therefore target the endpoint atom/log-ratio term in
`U(alpha)/eta`, replacing the explicit positive-eta quotient by its eta-zero
first-divided analytic form.
