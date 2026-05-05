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
