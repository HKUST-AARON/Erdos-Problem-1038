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

## Proof-grade Standard Reduction target

This is the Lean-facing proof text for the old Standard Reduction block.  It is
not a new assumption layer.  Each item below must eventually become a theorem in
`finite_atoms/common/lean/StandardReduction.lean`.  The final theorem must not
take `hPackageFromVariation`, `hEndpointFromVariation`,
`TaoVariationalReductionInput`, or `TaoEndpointReductionInput` as inputs.

### Final theorem shape

The intended endpoint is a theorem of this form.

```lean
theorem unitInterval_standardReduction_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective mu <=
          unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
            unitIntervalTruncatedPositiveSetObjective mu ->
        unitIntervalSecondMomentObjective mu <=
          unitIntervalSecondMomentObjective nu) :
    NormalizedEndpointPotential (unitIntervalLogPotential mu) := by
  -- construct the selected component, replacement, rigidity, boundary average,
  -- and endpoint package internally; do not import a provider theorem.
```

A stronger final form may directly conclude the baseline lower bound.

```lean
theorem unitInterval_standardReduction_baseline_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective mu <=
          unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
            unitIntervalTruncatedPositiveSetObjective mu ->
        unitIntervalSecondMomentObjective mu <=
          unitIntervalSecondMomentObjective nu) :
    ENNReal.ofReal (Real.sqrt 2) <=
      volume (PositiveSet (unitIntervalLogPotential mu)) := by
  exact normalizedEndpointPotential_baseline_volume_lower_bound
    (unitInterval_standardReduction_from_secondaryMinimizer hPrimary hSecondary)
```

The actual names can differ.  The logical shape cannot differ: the theorem must
start with a real secondary minimizer and produce endpoint-normalized data
without an external variation provider.

### Step 1: select the real positive component

Prove that the secondary minimizer has a positive component with the exact
baseline placement and interval data needed by the existing endpoint-package
bridges.

```lean
theorem selected_positiveComponent_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective mu <=
          unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
            unitIntervalTruncatedPositiveSetObjective mu ->
        unitIntervalSecondMomentObjective mu <=
          unitIntervalSecondMomentObjective nu) :
    exists C : PositiveComponent mu,
    exists xMinus xPlus : Real,
      C.interval = Set.Ioo xMinus xPlus /\
      Set.Ioo (-1 : Real) 0 <= C.interval /\
      0 < xPlus /\
      AugmentedIntervalMaximal mu C := by
  -- open positive set -> connected component -> interval representation
  -- baseline positivity supplies `Set.Ioo (-1) 0 <= C.interval`
  -- maximality supplies the augmented endpoint bookkeeping
```

This is the first hard mouth.  It is a topology theorem about the ordinary or
augmented positive set.  It must not use finite-atom route information.

### Step 2: prove the right-boundary average

From the selected maximal component, prove the Tao boundary inequality that
later gives endpoint mass at least `1 / 2`.

```lean
theorem boundary_average_from_selected_positiveComponent
    {mu : ProbabilityMeasure UnitInterval1038}
    {C : PositiveComponent mu}
    {xMinus xPlus endpointMass : Real}
    (hC_interval : C.interval = Set.Ioo xMinus xPlus)
    (hBaseline : Set.Ioo (-1 : Real) 0 <= C.interval)
    (hxPlus : 0 < xPlus)
    (hMax : AugmentedIntervalMaximal mu C)
    (hEndpointMass :
      realMeasure mu ({-1} : Set Real) = ENNReal.ofReal endpointMass) :
    1 <= (xPlus + 1) * endpointMass +
      (1 - xPlus) * (1 - endpointMass) := by
  -- maximal right endpoint gives a nonpositive boundary potential statement
  -- boundary-distance estimates convert it into the displayed average
```

This is the second hard mouth.  Existing downstream algebra can already turn
this inequality into `1 / 2 <= endpointMass`, but the source of the inequality
must be proved here.

### Step 3: construct the barycenter replacement

Construct the actual component replacement object from the selected component.
This step must build the replacement measure, not assume it.

```lean
theorem componentReplacement_from_selected_positiveComponent
    {mu : ProbabilityMeasure UnitInterval1038}
    {C : PositiveComponent mu}
    (hMassPos : 0 < componentMass mu C)
    (hMassFinite : componentMass mu C < top) :
    exists R : ComponentReplacement mu C,
      R.mass_pos = hMassPos /\
      R.mass_ne_top = hMassFinite := by
  -- define the component block, normalize it, take its barycenter, replace the
  -- block by a Dirac mass at the barycenter, and prove the result is again a
  -- probability measure on UnitInterval1038
```

The output should be strong enough to feed the existing replacement-probability
and potential-equality bridges.

### Step 4: prove primary objective nonincrease for the real replacement

Use Jensen outside the component plus the existing small-exception/tail machinery
to prove that the replacement does not increase the truncated positive-set
objective.

```lean
theorem componentReplacement_truncatedObjective_nonincrease_from_variation
    {mu : ProbabilityMeasure UnitInterval1038}
    {C : PositiveComponent mu}
    (R : ComponentReplacement mu C)
    (hJensen :
      forall x : Real,
        StrictOutsideComponent C x ->
        componentReplacementPotential C x <= unitIntervalLogPotential mu x) :
    unitIntervalTruncatedPositiveSetObjective
        (componentReplacementProbability mu C R) <=
      unitIntervalTruncatedPositiveSetObjective mu := by
  -- apply the already-proved small-exception comparison theorem
  -- instantiate the exceptional sets from threshold-tail bad-set machinery
  -- take eta -> 0 only through the existing exact bridge
```

No support-as-exception argument is allowed here.  Diagonal/pole exceptions must
be finite, null, or arbitrarily small with an explicit limiting theorem.

### Step 5: derive secondary rigidity and atomization

Use primary nonincrease, secondary minimality, and the concrete second-moment
objective to force equality, then convert equality into Dirac atomization of the
component block.

```lean
theorem component_atomization_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    {C : PositiveComponent mu}
    (R : ComponentReplacement mu C)
    (hPrimary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective mu <=
          unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
            unitIntervalTruncatedPositiveSetObjective mu ->
        unitIntervalSecondMomentObjective mu <=
          unitIntervalSecondMomentObjective nu)
    (hPrimaryReplacement :
      unitIntervalTruncatedPositiveSetObjective
          (componentReplacementProbability mu C R) <=
        unitIntervalTruncatedPositiveSetObjective mu) :
    componentBlock mu C = componentMass mu C • Measure.dirac (-1) := by
  -- primary minimality makes the replacement also primary-minimizing
  -- secondary minimality plus replacement second-moment nonincrease gives equality
  -- equality in the variance/barycenter replacement gives normalized Dirac
  -- boundary/component identification moves the barycenter to `-1`
```

If the proof naturally splits, the accepted intermediate endpoints are:

```lean
normalizedComponentBlock mu C = Measure.dirac (componentBarycenter mu C)
componentBarycenter mu C = -1
normalizedComponentBlock mu C = Measure.dirac (-1)
componentBlock mu C = componentMass mu C • Measure.dirac (-1)
```

### Step 6: assemble the endpoint package

Once Steps 1--5 are proved, use the existing downstream bridges.  This assembly
should be short and should not introduce a new provider structure.

```lean
theorem taoVariationComponentPackage_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective mu <=
          unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
            unitIntervalTruncatedPositiveSetObjective mu ->
        unitIntervalSecondMomentObjective mu <=
          unitIntervalSecondMomentObjective nu) :
    TaoVariationComponentPackage (unitIntervalLogPotential mu) := by
  rcases selected_positiveComponent_from_secondaryMinimizer hPrimary hSecondary
    with <C, xMinus, xPlus, hC_interval, hBaseline, hxPlus, hMax>
  have hBoundary := boundary_average_from_selected_positiveComponent
    hC_interval hBaseline hxPlus hMax ?hEndpointMass
  rcases componentReplacement_from_selected_positiveComponent ?hMassPos ?hMassFinite
    with <R, hR>
  have hPrimaryReplacement :=
    componentReplacement_truncatedObjective_nonincrease_from_variation R ?hJensen
  have hAtom := component_atomization_from_secondaryMinimizer
    R hPrimary hSecondary hPrimaryReplacement
  -- feed `hBoundary`, `hAtom`, and existing remainder/support bridges into the
  -- current strongest package constructor
```

Then the final endpoint theorem is just:

```lean
theorem unitInterval_standardReduction_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective mu <=
          unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary :
      forall nu : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
            unitIntervalTruncatedPositiveSetObjective mu ->
        unitIntervalSecondMomentObjective mu <=
          unitIntervalSecondMomentObjective nu) :
    NormalizedEndpointPotential (unitIntervalLogPotential mu) := by
  exact tao_endpoint_from_component_variation_package_ennreal
    (taoVariationComponentPackage_from_secondaryMinimizer hPrimary hSecondary)
```

### Lean acceptance rules

- Every theorem must state whether it uses `PositiveSet` or an augmented positive
  set.
- Every objective inequality must state whether it is for the ordinary objective
  or `unitIntervalTruncatedPositiveSetObjective`.
- Every exceptional set must be finite, null, or arbitrarily small with an
  explicit limiting theorem; the full support of `mu` cannot be used as an
  exception.
- Every boundary point used in a log kernel must carry either an off-diagonal
  proof or an integrability/tail-finiteness proof.
- Every use of support must specify whether it is topological support of
  `realMeasure mu`, almost-everywhere support, or the subtype support in
  `UnitInterval1038`.
- The old provider theorems may remain as compatibility wrappers, but the final
  Standard Reduction theorem must not depend on them.

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
