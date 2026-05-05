# Strong forcing branch certificate

This folder records the stronger two-parameter forcing branch used by the
`M = 1.814600` finite-atom route.

The branch uses

$$
a\in[-1.708,-\sqrt2],\qquad b=s(1.836+a),\qquad s\in[0,1],
$$

and

$$
\nu_{a,b}=\delta_a+(1.395-b)\delta_b+C(a,b)\delta_{1.071-b},
$$

where \(C(a,b)\) is chosen by \(U_{\nu_{a,b}}(-1)=10^{-4}\).

The fixed certificate is:

```text
forcing_1836_interval_certificate.json
```

It contains 5955 boxes covering

```text
a ∈ [-1.708, -1.414213562373095]
s ∈ [0, 1]
x ∈ [0, 1]
```

with worst certified lower bound

```text
0.00000276921093908335076907373670075951405896314059839585990514842973110247469531
```

This is the forcing handoff needed for the 1.814600 route:

```text
if (-1.708,0) is not contained in the augmented positive set,
then the forcing branch gives volume at least 1.836.
```

## Check command

From the repository root:

```bash
python3 finite_atoms/forcing_1836/scripts/verify_forcing_1836_interval.py \
  --check-json finite_atoms/forcing_1836/forcing_1836_interval_certificate.json
```

Expected output ends with:

```text
status: PASS
```

## Lean rational arithmetic layer

The JSON certificate is also unpacked into Lean chunks:

```text
lean/box_arith_chunks/Forcing1836BoxArith000.lean
...
lean/box_arith_chunks/Forcing1836BoxArith119.lean
lean/Forcing1836BoxData.lean
```

These files check the rational recombination layer for all 5955 boxes:

```text
box shape
positive weights
positive C(a,b) lower bound
stored lower bound > 10^-6
stored lower bound <= recombined rational lower bound
```

To check this layer:

```bash
LEAN_JOBS=8 MATHLIB_WORKSPACE=/path/to/mathlib \
  finite_atoms/forcing_1836/scripts/check_box_arith.sh
```
