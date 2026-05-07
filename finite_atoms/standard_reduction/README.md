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

### Formula-level mathematical proof text

The intended mathematical proof is the following.  The purpose of the Lean work
is to turn each displayed implication into a theorem with the same hypotheses.

Let

$$
  U_\mu(x)=\int_{[-1,1]} \log {1\over |x-y|}\,d\mu(y),
  \qquad
  E_\mu=\{x\in \mathbb R:U_\mu(x)>0\},
$$

and let

$$
  F(\mu)=\lambda(E_\mu),
  \qquad
  Q(\mu)=\int_{[-1,1]} y^2\,d\mu(y).
$$

In Lean the actual objective is the truncated version
`unitIntervalTruncatedPositiveSetObjective`; the proof below must therefore be
implemented with the truncated objective first, and only then transferred to the
ordinary positive set through the existing tail-exception bridges.

Choose a probability measure `mu` which minimizes `F`, and among all such
minimizers minimizes `Q`.  In formula form the two minimizer facts are

$$
  F(\mu)\le F(\nu) \quad\hbox{for every probability }\nu,
$$

and

$$
  F(\nu)\le F(\mu) \Longrightarrow Q(\mu)\le Q(\nu).
$$

The Standard Reduction must prove from these two facts that, after the accepted
normalization,

$$
  \operatorname{supp}\mu\subseteq \{-1\}\cup[0,1]
  \quad\hbox{and}\quad
  \mu(\{-1\})\ge {1\over 2}.
$$

Then for every

$$
  x\in(-\sqrt2,0),\qquad x\ne -1,
$$

write

$$
  p=\mu(\{-1\}), \qquad \mu=p\delta_{-1}+(1-p)\rho,
  \qquad \operatorname{supp}\rho\subseteq[0,1].
$$

For `y in [0,1]` and `x in (-sqrt 2,0)` one has

$$
  |x-y|\le 1-x.
$$

Therefore

$$
\begin{aligned}
  U_\mu(x)
  &=p\log {1\over |x+1|}
    +(1-p)\int_{[0,1]}\log {1\over |x-y|}\,d\rho(y) \\
  &\ge p\log {1\over |x+1|}
    +(1-p)\log {1\over 1-x}.
\end{aligned}
$$

Since `p >= 1/2`, the right side is bounded below by

$$
  {1\over2}\log {1\over |x+1|(1-x)}.
$$

If `-1 < x < 0`, then

$$
  |x+1|(1-x)=(1+x)(1-x)=1-x^2<1.
$$

If `-sqrt 2 < x < -1`, then

$$
  |x+1|(1-x)=(-x-1)(1-x)=x^2-1<1.
$$

Thus

$$
  |x+1|(1-x)<1,
  \qquad
  U_\mu(x)>0.
$$

So

$$
  (-\sqrt2,0)\setminus\{-1\}\subseteq E_\mu.
$$

The point `{-1}` has Lebesgue measure zero, hence

$$
  \lambda(E_\mu)\ge \lambda((-\sqrt2,0))=\sqrt2.
$$

This last displayed argument is already the easy downstream part.  The hard
upstream part is proving the normalized support and endpoint mass inequality.
That proof must proceed as follows.

#### 1. Positive component selection

Let `C=(a,b)` be the positive component selected from `E_mu`.  The component
selection theorem must prove

$$
  (-1,0)\subseteq C,
  \qquad
  C=(a,b),
  \qquad
  b>0,
$$

and the required maximality condition: if the component can be enlarged to the
right without increasing the objective, then `C` was not selected correctly.
This is the theorem currently missing under the name "real positive-component
selection".

#### 2. Component replacement

Decompose the measure into the part inside and outside `C`:

$$
  \mu=\mu_C+\mu_{C^c},
  \qquad
  m=\mu_C(\mathbb R)>0.
$$

Let

$$
  c={1\over m}\int_C y\,d\mu_C(y)
$$

be the barycenter.  Define the replacement measure

$$
  \nu=\mu_{C^c}+m\delta_c.
$$

For every `x notin C`, the function

$$
  y\mapsto \log {1\over |x-y|}
$$

is convex on `C`.  Jensen gives

$$
  m\log {1\over |x-c|}
  \le
  \int_C \log {1\over |x-y|}\,d\mu_C(y).
$$

Therefore

$$
  U_\nu(x)\le U_\mu(x)
  \qquad (x\notin C),
$$

up to the explicitly controlled diagonal/tail exceptional sets.  Since
`C subset E_mu`, the inside of `C` is already counted by the original positive
set.  Consequently

$$
  F(\nu)\le F(\mu).
$$

In Lean this is exactly the route through
`componentReplacement_objective_le_of_forall_small_tailMass_exception`, followed
by the exact small-eta limiting bridge.

#### 3. Secondary rigidity

The second moment of the replacement is

$$
  Q(\nu)=Q(\mu)-\int_C y^2\,d\mu_C(y)+m c^2.
$$

Because

$$
  \int_C (y-c)^2\,d\mu_C(y)
  =\int_C y^2\,d\mu_C(y)-m c^2\ge 0,
$$

we get

$$
  Q(\nu)\le Q(\mu).
$$

The primary minimality of `mu` and `F(nu) <= F(mu)` imply that `nu` is also a
primary minimizer.  The secondary minimality of `mu` then gives

$$
  Q(\mu)\le Q(\nu).
$$

Hence

$$
  Q(\nu)=Q(\mu),
  \qquad
  \int_C (y-c)^2\,d\mu_C(y)=0.
$$

Thus

$$
  \mu_C=m\delta_c.
$$

After the selected normalization and endpoint-identification theorem, this must
become

$$
  c=-1,
  \qquad
  \mu_C=m\delta_{-1}.
$$

This is the missing bridge from real replacement rigidity to endpoint
atomization.

#### 4. Boundary average and endpoint mass

Let

$$
  p=\mu(\{-1\}),
  \qquad
  C=(a,b),
  \qquad
  b>0.
$$

The Tao boundary variation must prove

$$
  1\le (b+1)p+(1-b)(1-p).
$$

Algebra gives

$$
\begin{aligned}
  1
  &\le (b+1)p+(1-b)(1-p) \\
  &=1-b+2bp.
\end{aligned}
$$

Since `b > 0`, this implies

$$
  b\le 2bp,
  \qquad
  p\ge {1\over2}.
$$

This is the only source of the endpoint mass lower bound.  It cannot be replaced
by a provider hypothesis in the final theorem.

#### 5. Normalized support

The atomization theorem gives no mass from `mu` inside `C` except at `-1`.
The zero-neighborhood/support-uniqueness bridge must prove

$$
  \operatorname{supp}\mu\cap C\subseteq\{-1\}.
$$

The component selection and normalization must place all remaining support to
the right, giving

$$
  \operatorname{supp}\mu\subseteq\{-1\}\cup[0,1].
$$

Combining this support statement with `p >= 1/2` gives
`NormalizedEndpointPotential (unitIntervalLogPotential mu)`, and the first part
of this section gives the baseline lower bound.

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
