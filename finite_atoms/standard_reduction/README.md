# Standard Reduction ledger

Goal: prove the Tao/natso standard reduction in Lean, not merely package its
consequences.  The target is to remove the remaining external variation-provider
inputs and derive endpoint-normalized data from an actual secondary minimizer.

## Current truth

The downstream endpoint package is now substantially formalized.  In particular,
`finite_atoms/common/lean/StandardReduction.lean` proves the chain

```text
selected component data
+ boundary average
+ support uniqueness / zero-neighborhood / component atomization
  -> TaoVariationComponentPackage
  -> TaoEndpointNormalizationData
  -> NormalizedEndpointPotential
  -> volume baseline lower bound sqrt 2
```

The following pieces are already Lean-proved under their stated hypotheses:

- endpoint mass at `-1` plus normalized support gives positivity on
  `BaselinePunctured`;
- the puncture at `-1` has zero Lebesgue volume;
- endpoint-remainder mass bookkeeping for
  `(realMeasure μ).restrict ({-1}ᶜ)`;
- support uniqueness inside the selected component gives endpoint-remainder
  log-kernel integrability on `BaselinePunctured`;
- zero-neighborhood data imply support uniqueness;
- component-block atomization implies zero-neighborhood data;
- normalized component-block atomization implies component-block atomization;
- replacement/second-moment rigidity can convert secondary equality into
  normalized Dirac atomization;
- augmented span plus right-gap hypotheses can feed the boundary-average bridge.

These are real formal bridges, not `sorry` placeholders.  They are still
conditional bridges: their hypotheses must be produced by the actual variation
argument.

## What is not closed

Full Standard Reduction is not proved yet.  The remaining mathematical inputs
are exactly these.

1. **Real positive-component selection.**
   From a secondary minimizer `μ`, construct the correct maximal or augmented
   maximal `PositiveComponent μ` containing the baseline interval `Ioo (-1) 0`.

2. **Right endpoint / boundary-average source.**
   Prove the selected component has a right endpoint `xPlus > 0` and derive
   Tao's boundary-average inequality from maximality, boundary nonpositivity,
   support separation, and the already-formal distance/Jensen bridge.

3. **Barycenter replacement construction.**
   Construct the replacement probability measure for the selected component,
   prove it is admissible, and prove its primary objective does not increase.

4. **Secondary rigidity to atomization.**
   Use secondary minimality plus replacement nonincrease to prove component
   atomization or zero-neighborhood/support uniqueness inside the selected
   component.

5. **Provider removal.**
   Replace the remaining external provider interfaces, especially
   `hPackageFromVariation`, `hEndpointFromVariation`,
   `TaoVariationalReductionInput`, and `TaoEndpointReductionInput`, by the real
   component-selection/replacement/boundary proof.

Until these five items are proved, the standard reduction is a conditional
formal interface, not an unconditional theorem.

## Do not overstate

`0 sorry` / `0 axiom` is not the same as full closure.  Current Lean theorems
are valid under explicit hypotheses.  The unproved content is represented by
provider arguments and structure fields, not by `sorry`.

The finite-atom lower-bound route can use the normalized endpoint interface once
Standard Reduction supplies it.  The finite certificates do not by themselves
prove the full standard reduction.

## Next proof order

Do not add more endpoint-wrapper theorems unless they remove a genuinely new
mathematical input.  The useful order is:

1. Prove the positive-set component/topology lemma that produces the selected
   maximal component and baseline placement.
2. Prove the right-endpoint boundary statement and feed it into the existing
   boundary-average bridge.
3. Build the actual barycenter replacement measure for that component.
4. Prove primary nonincrease and secondary rigidity for the replacement.
5. Use the existing atomization/zero-neighborhood/support-uniqueness bridges to
   assemble `TaoVariationComponentPackage` without any external provider.
6. Only after that, remove or demote the old provider-style theorems.

## Current preferred Lean entry points

The most useful endpoint-facing theorems are now the narrow high-level bridges
in `StandardReduction.lean`:

```text
...from_support_unique_component_data
...from_zero_neighborhood_component_data
...from_component_atomization_component_data
```

They should be treated as temporary targets for the real variation proof.  They
are not the final Standard Reduction theorem.

## Verification scope

For Standard Reduction work, the cheap check is the single-file compile:

```bash
MATHLIB_WORKSPACE='/Users/aaron/Downloads/Frankl 并闭集猜想'
REPO='/Users/aaron/Downloads/erdos数学问题'
BUILD=/tmp/erdos1038_standard_reduction_olean
rm -rf "$BUILD"
mkdir -p "$BUILD/finite_atoms/common/lean"
cd "$MATHLIB_WORKSPACE"
lake env lean -R "$REPO" \
  -o "$BUILD/finite_atoms/common/lean/StandardReduction.olean" \
  "$REPO/finite_atoms/common/lean/StandardReduction.lean"
```

Do not run route, forcing, or 560-block checks for Standard Reduction-only doc
or interface changes unless explicitly requested.
