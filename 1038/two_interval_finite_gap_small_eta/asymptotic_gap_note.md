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

The original K1 interval blow-up was localized at the endpoint eta floor.
Holding `eta_high=1e-8` fixed and raising `eta_low` restored a useful K1
interval, pointing to the endpoint atom/log-ratio term in `U(alpha)/eta`.

The contact endpoint term has now been replaced by the analytic identity

```text
log((w-rho_minus)/(w-rho_plus))/eta
= 2 * log(1 + eta / sqrt(1-alpha)) / eta
= 2 * log1p(z) / (z * sqrt(1-alpha)).
```

This removes the removable eta-zero singularity for the contact K1 branch.

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/diagnose_k1_eta_floor.py
```

Current output:

```text
eta=[1e-16,1e-08] K1_radius=2.390000e-06
eta=[1e-12,1e-08] K1_radius=2.390000e-06
eta=[1e-10,1e-08] K1_radius=2.370000e-06
eta=[1e-09,1e-08] K1_radius=2.150000e-06
eta=[5e-09,1e-08] K1_radius=1.210000e-06
TWO-INTERVAL K1 ETA FLOOR: PASS-DIAGNOSTIC
```

The K1 endpoint floor is therefore no longer the dominant blocker.

The remaining interval-proof issue is different: the old boundary-winding
mean-value derivative inflation can still produce `nan` at extremely small eta,
and direct whole-edge interval boxes are too wide because of dependency in
\((B,\tau)\).  The next proof-grade step should subdivide boundary boxes and
bound \(K_\eta-K_0\) directly, using the endpoint-safe K1 and the already
regularized K2 kernel.

## Direct Remainder Box Attempt

I added a direct boundary-box checker:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/verify_interval_remainder_boxes.py \
  --edge-boxes 256
```

It uses the endpoint-safe K1 and the regularized K2 value kernel, then compares
against the limiting normal form on boundary boxes.

Current result:

```text
TWO-INTERVAL INTERVAL REMAINDER BOXES: FAIL
edge_boxes=256 boxes=1024
target_bound=7.000000e-03
worst_bound=6.540541e-01
worst_source=right: D1=[+/- 0.0248] D2=[+/- 0.654]
```

The trend under subdivision is real but too slow:

```text
edge_boxes=16   worst_bound ~= 9.80
edge_boxes=64   worst_bound ~= 2.49
edge_boxes=256  worst_bound ~= 0.654
```

Splitting eta does not materially change this bound:

```text
eta=[1e-16,1e-12], edge_boxes=256  worst_bound ~= 0.654
eta=[1e-12,1e-8],  edge_boxes=256  worst_bound ~= 0.654
eta=[1e-10,1e-8],  edge_boxes=256  worst_bound ~= 0.654
```

Thus the endpoint-safe K1 fix succeeded, but the next blocker is K2 dependency
on the right/left boundary boxes.  The next kernel should reduce K2 directly on
fixed \(B=\pm0.01\) edges, rather than relying on generic interval dependency
over \(\tau\).  The blocker is tau/right-edge dependency, not eta-width.

## K2 Edge-Lipschitz Diagnostic

I added a focused diagnostic for the right/left boundary issue:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/diagnose_k2_edge_lipschitz.py
```

It evaluates the true K2 remainder on the two fixed boundary edges
\(B=\pm0.01\), over the endpoint eta range represented by
\(\eta=10^{-16},10^{-12},10^{-8}\), and estimates the tau slope on the
\(\tau_0\pm0.05\) edge interval.

Observed output:

```text
B=+0.01 eta=1.0e-16 range=[5.350883e-05,6.409310e-05] max_abs=6.409310e-05 max_slope=1.107338e-04
B=+0.01 eta=1.0e-12 range=[5.350885e-05,6.409310e-05] max_abs=6.409310e-05 max_slope=1.107337e-04
B=+0.01 eta=1.0e-08 range=[5.349449e-05,6.407606e-05] max_abs=6.407606e-05 max_slope=1.107053e-04
B=-0.01 eta=1.0e-16 range=[5.330673e-05,6.387085e-05] max_abs=6.387085e-05 max_slope=1.105324e-04
B=-0.01 eta=1.0e-12 range=[5.330673e-05,6.387084e-05] max_abs=6.387084e-05 max_slope=1.105324e-04
B=-0.01 eta=1.0e-08 range=[5.329255e-05,6.385399e-05] max_abs=6.385399e-05 max_slope=1.105040e-04
TWO-INTERVAL K2 EDGE LIPSCHITZ: PASS-DIAGNOSTIC
worst_value=6.409310e-05
sampled_worst_slope=1.107338e-04
candidate_lipschitz=2.000000e-04
implied_edge_bound=7.409310e-05
target_bound=7.000000e-03
```

This explains why the generic interval-box checker fails: it loses almost four
orders of magnitude through dependency, while the actual edge remainder is
smooth and small.  The next proof-grade step is therefore not more eta slicing,
but a certified K2 edge lemma:

```text
|d/dtau (K2_eta(+/-0.01,tau)-K2_0(+/-0.01,tau))| <= 2e-4
```

on the endpoint eta range and the tau interval.  Together with one certified
edge value bound, this would give a K2 edge bound below `8e-5`, far inside the
`7e-3` winding margin target.

## Dense K2 Edge Stress Test

To check that the candidate edge lemma is not an artifact of a coarse grid, I
also ran a dense eta/tau stress test:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/diagnose_k2_edge_lipschitz.py \
  --grid 2001 \
  --eta-values 1e-16,3e-16,1e-15,3e-15,1e-14,3e-14,1e-13,3e-13,1e-12,3e-12,1e-11,3e-11,1e-10,3e-10,1e-9,3e-9,1e-8
```

Observed summary:

```text
TWO-INTERVAL K2 EDGE LIPSCHITZ: PASS-DIAGNOSTIC
worst_value=6.409310e-05
sampled_worst_slope=1.108567e-04
candidate_lipschitz=2.000000e-04
implied_edge_bound=7.409310e-05
target_bound=7.000000e-03
worst_source='B=+0.01,eta=1.0e-16'
```

The maximum sampled slope is stable across the whole tested eta ladder and
occurs at the lower eta edge.  This makes the remaining proof obligation
sharper:

```text
Replace this sampled stress test by an Arb/Taylor edge enclosure for
d/dtau K2_eta(B,tau)-d/dtau K2_0(B,tau), B = +/-0.01.
```

If that derivative enclosure proves the conservative bound `2e-4`, the K2
edge part of the small-eta singular gap closes with a margin of roughly two
orders of magnitude.

## Hybrid Edge Certificate Diagnostic

The direct interval box checker fails because it asks Arb to enclose the full
K2 expression over a two-variable box.  A sharper diagnostic separates the
roles:

```text
K2 edge remainder <= point value + Arb eta variation + tau-Lipschitz allowance.
```

The eta-variation part is already interval-enclosed by the existing
`eta_variation_mid` kernel.  Running

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/diagnose_k2_edge_lipschitz.py \
  --grid 401 \
  --eta-values 1e-16,1e-8 \
  --hybrid-certificate
```

gives:

```text
TWO-INTERVAL K2 HYBRID EDGE CERTIFICATE: PASS-DIAGNOSTIC
grid=401
eta_low=1.000000e-16
eta_high=1.000000e-08
candidate_lipschitz=2.000000e-04
worst_bound=6.414311e-05
target_bound=7.000000e-03
worst_source='B=+0.01,index=400,tau=1.103891261372e+00,center=6.408458e-05,eta_var=8.530000e-09,tau_allowance=5.000000e-08'
```

This is much closer to the proof shape needed for the endpoint:

1. certify the point values on the tau grid;
2. certify the eta-variation kernel on each point or narrow tau cell;
3. certify the tau-Lipschitz bound `2e-4`.

Only the third item is still a sampled assumption in this diagnostic.  Once it
is replaced by an interval/Taylor derivative bound, the K2 right/left edge
obligation is no longer the blocker.

## Tau-Derivative Stress Diagnostic

The remaining sampled assumption in the hybrid certificate is the conservative
tau-Lipschitz target

```text
|d/dtau (K2_eta(B,tau)-K2_0(B,tau))| <= 2e-4,
B = +/-0.01.
```

I added a finite-difference derivative stress script:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/diagnose_k2_tau_derivative.py \
  --grid 401 \
  --h 1e-5 \
  --eta-values 1e-16,1e-12,1e-8
```

Observed output:

```text
B=+0.01 eta=1.0e-16 max_abs_derivative=1.108587e-04 max_abs_curvature=1.015854e-04
B=+0.01 eta=1.0e-12 max_abs_derivative=1.108587e-04 max_abs_curvature=1.016028e-04
B=+0.01 eta=1.0e-08 max_abs_derivative=1.108302e-04 max_abs_curvature=1.015681e-04
B=-0.01 eta=1.0e-16 max_abs_derivative=1.106573e-04 max_abs_curvature=1.018803e-04
B=-0.01 eta=1.0e-12 max_abs_derivative=1.106573e-04 max_abs_curvature=1.018803e-04
B=-0.01 eta=1.0e-08 max_abs_derivative=1.106289e-04 max_abs_curvature=1.018283e-04
TWO-INTERVAL K2 TAU DERIVATIVE: PASS-DIAGNOSTIC
worst_derivative=1.108587e-04
candidate_lipschitz=2.000000e-04
worst_curvature=1.018803e-04
candidate_curvature=2.500000e-04
```

This does not yet replace the required interval/Taylor derivative proof, but
it shows that the target `2e-4` has nearly a factor-two numerical margin and no
visible endpoint spike on the tested eta ladder.  The exact next proof artifact
should be an interval version of this derivative check, ideally using the same
combined K2 residual-level algebra rather than differentiating the uncancelled
primitive.

## Eta-Uniform Secant Diagnostic

I also added a stronger grid diagnostic that is closer to an interval proof.
For each tau cell, it evaluates the two endpoint remainders at
\(\eta_{\mathrm{mid}}\), thickens each endpoint by the Arb eta-variation
enclosure over the full eta interval, and divides by the cell width.  This
gives an eta-uniform secant bound for each cell.

Command:

```bash
.venv/bin/python 1038/two_interval_finite_gap_small_eta/diagnose_k2_tau_derivative.py \
  --grid 401 \
  --h 1e-5 \
  --eta-values 1e-16,1e-8 \
  --secant-certificate
```

Observed summary:

```text
TWO-INTERVAL K2 ETA-UNIFORM SECANTS: PASS-DIAGNOSTIC
grid=401
eta_low=1.000000e-16
eta_high=1.000000e-08
worst_secant_bound=1.790724e-04
candidate_lipschitz=2.000000e-04
worst_source='B=+0.01,index=399,tau_left=1.103641261372e+00,tau_right=1.103891261372e+00,left_eta=8.530000e-09,right_eta=8.530000e-09'
```

This is not yet a theorem because secant control alone does not bound all
within-cell derivatives.  But it has two useful consequences:

1. eta-uniformity is no longer the numerical difficulty; the Arb eta-variation
   contribution is only about `8.53e-9` at the worst endpoint;
2. the remaining proof gap is exactly a within-cell derivative/curvature
   enclosure, not a global endpoint singularity.
