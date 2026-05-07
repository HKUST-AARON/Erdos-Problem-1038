# Standard Reduction proof ledger

This file records the provider-free Standard Reduction proof target.  It is not a
route/forcing ledger.  It only tracks what must be proved in
`finite_atoms/common/lean/StandardReduction.lean` to derive endpoint-normalized
data from an actual secondary minimizer.

## Final target

For a probability measure `mu : ProbabilityMeasure UnitInterval1038`, define

$$
  U_\mu(x)=\int_{[-1,1]} \log {1\over |x-y|}\,d\mu(y),
  \qquad
  E_\mu=\{x:U_\mu(x)>0\}.
$$

In Lean these are represented by `unitIntervalLogPotential mu` and
`PositiveSet (unitIntervalLogPotential mu)`.  The primary objective is handled
first through `unitIntervalTruncatedPositiveSetObjective`, and only then related
back to the ordinary positive set by the existing tail-exception machinery.

The final theorem should have this logical shape:

```lean
theorem unitInterval_standardReduction_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective mu <=
        unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective mu ->
      unitIntervalSecondMomentObjective mu <=
        unitIntervalSecondMomentObjective nu) :
    NormalizedEndpointPotential (unitIntervalLogPotential mu)
```

This theorem must not take any of the old provider inputs:

```lean
hPackageFromVariation
hEndpointFromVariation
TaoVariationalReductionInput
TaoEndpointReductionInput
```

## Downstream endpoint argument

The endpoint theorem to be produced is:

$$
  \operatorname{supp}\mu\subseteq\{-1\}\cup[0,1],
  \qquad
  \mu(\{-1\})\ge {1\over2}.
$$

Once this is known, the baseline lower bound follows as follows.  Put

$$
  p=\mu(\{-1\}),
  \qquad
  \mu=p\delta_{-1}+(1-p)\rho,
  \qquad
  \operatorname{supp}\rho\subseteq[0,1].
$$

For `x in (-sqrt 2,0)`, `x != -1`, and `y in [0,1]`,

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
    +(1-p)\log {1\over 1-x} \\
  &\ge {1\over2}\log {1\over |x+1|(1-x)}.
\end{aligned}
$$

For `x in (-sqrt 2,0)`, `x != -1`,

$$
  |x+1|(1-x)<1.
$$

Hence `U_mu x > 0`, so

$$
  (-\sqrt2,0)\setminus\{-1\}\subseteq E_\mu.
$$

Since `volume ({-1} : Set Real) = 0`,

$$
  \lambda(E_\mu)\ge\lambda((-\sqrt2,0))=\sqrt2.
$$

Lean status: this downstream part is mostly already represented by the existing
`NormalizedEndpointPotential` and baseline-volume lemmas.  The hard work is to
prove the endpoint theorem from `hPrimary` and `hSecondary`.

## Provider-free proof obligations

The proof must be closed by the following theorem chain.  Each item is a real
Lean theorem obligation; none should be replaced by a new broad provider
structure.

### 1. Positive component selection

Mathematical statement: from the actual secondary minimizer, select the positive
component `C = (a,b)` satisfying

$$
  (-1,0)\subseteq C,
  \qquad
  b>0,
$$

and the required maximality condition.

Lean target shape:

```lean
theorem selected_positiveComponent_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective mu <=
        unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective mu ->
      unitIntervalSecondMomentObjective mu <=
        unitIntervalSecondMomentObjective nu) :
    exists C : PositiveComponent mu,
    exists a b : Real,
      C.interval = Set.Ioo a b /\
      Set.Ioo (-1 : Real) 0 <= C.interval /\
      0 < b /\
      C.AugmentedIntervalMaximal
```

Lean acceptance requirements:

- State explicitly whether the component is from `PositiveSet` or
  `unitIntervalAugmentedPositiveSet`.
- Prove `C.interval = Set.Ioo C.left C.right` or provide `a b` with equality.
- Prove measurability/open-set facts needed by later replacement lemmas.
- Do not import finite-atom route/forcing facts.

### 2. Component mass and barycenter replacement

Mathematical construction:

$$
  \mu=\mu_C+\mu_{C^c},
  \qquad
  m=\mu_C(\mathbb R)>0,
  \qquad
  c={1\over m}\int_C y\,d\mu_C(y),
$$

and

$$
  \nu=\mu_{C^c}+m\delta_c.
$$

Lean target shape:

```lean
theorem componentReplacement_from_selected_positiveComponent
    {mu : ProbabilityMeasure UnitInterval1038}
    {C : PositiveComponent mu}
    (hmass : 0 < componentMass C) :
    exists R : ComponentReplacement mu C,
      componentBarycenter C in Set.Icc (-1 : Real) 1 /\
      -- the replacement measure/probability object is admissible
      True
```

The final conclusion should use the actual replacement API already present in
`StandardReduction.lean`, for example `ComponentReplacement.of_mass_pos`,
`componentReplacementProbability`, and `componentReplacementPotential`.

Lean acceptance requirements:

- Prove `componentMass C != 0` and `componentMass C != top` from `hmass` and
  finiteness of `realMeasure mu`.
- Prove the normalized component block is a probability measure.
- Prove `componentBarycenter C in Icc (-1) 1`.
- Prove the replacement stays inside `UnitInterval1038`.

### 3. Jensen and primary objective nonincrease

Mathematical inequality: for `x notin C`, Jensen gives

$$
  m\log {1\over |x-c|}
  \le
  \int_C \log {1\over |x-y|}\,d\mu_C(y),
$$

hence

$$
  U_\nu(x)\le U_\mu(x)
$$

outside the component, away from explicitly controlled singular exceptions.
Since the inside of `C` is already contained in the original positive set,

$$
  F(\nu)\le F(\mu).
$$

Lean target shape:

```lean
theorem componentReplacement_primary_nonincrease_from_selected_component
    {mu : ProbabilityMeasure UnitInterval1038}
    {C : PositiveComponent mu}
    (R : ComponentReplacement mu C)
    (hcomponent_pos : C.interval <= PositiveSet (unitIntervalLogPotential mu))
    (hJensen : forall x : Real,
      StrictOutsideComponent C x ->
      componentReplacementPotential C x <= unitIntervalLogPotential mu x) :
    unitIntervalTruncatedPositiveSetObjective
        (componentReplacementProbability mu C R) <=
      unitIntervalTruncatedPositiveSetObjective mu
```

Lean acceptance requirements:

- Use the existing small-exception theorem rather than a support-as-exception
  shortcut.
- Diagonal/pole sets must be finite, null, or arbitrarily small with an explicit
  limiting theorem.
- State every integrability hypothesis for the log kernel before Jensen.
- The objective must be the truncated objective unless an explicit transfer to
  the ordinary objective is part of the theorem.

### 4. Secondary rigidity to Dirac atomization

Mathematical computation:

$$
\begin{aligned}
  Q(\nu)
  &=Q(\mu)-\int_C y^2\,d\mu_C(y)+mc^2 \\
  &=Q(\mu)-\int_C (y-c)^2\,d\mu_C(y)
  \le Q(\mu).
\end{aligned}
$$

Primary minimality plus `F(nu) <= F(mu)` makes `nu` another primary minimizer.
Secondary minimality gives `Q(mu) <= Q(nu)`.  Therefore

$$
  \int_C (y-c)^2\,d\mu_C(y)=0,
  \qquad
  \mu_C=m\delta_c.
$$

Lean target shape:

```lean
theorem normalizedComponentBlock_eq_dirac_barycenter_from_secondary_rigidity
    {mu : ProbabilityMeasure UnitInterval1038}
    {C : PositiveComponent mu}
    (R : ComponentReplacement mu C)
    (hPrimary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective mu <=
        unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective mu ->
      unitIntervalSecondMomentObjective mu <=
        unitIntervalSecondMomentObjective nu)
    (hPrimaryReplacement :
      unitIntervalTruncatedPositiveSetObjective
          (componentReplacementProbability mu C R) <=
        unitIntervalTruncatedPositiveSetObjective mu) :
    normalizedComponentBlock C = Measure.dirac (componentBarycenter C)
```

Lean acceptance requirements:

- Prove second-moment nonincrease for the actual replacement probability.
- Use `hPrimary` to show the replacement is also primary-minimizing.
- Use `hSecondary` to force equality.
- Convert zero variance into `Measure.dirac` via the existing normalized block
  rigidity lemma.

### 5. Endpoint identification and support uniqueness

The previous step gives atomization at the barycenter.  The Standard Reduction
must identify that barycenter with the endpoint:

$$
  c=-1.
$$

Then

$$
  \mu_C=m\delta_{-1},
  \qquad
  \operatorname{supp}\mu\cap C\subseteq\{-1\}.
$$

Lean target shape:

```lean
theorem endpoint_atomization_from_secondary_rigidity
    {mu : ProbabilityMeasure UnitInterval1038}
    {C : PositiveComponent mu}
    (R : ComponentReplacement mu C)
    (hnormalized :
      normalizedComponentBlock C = Measure.dirac (componentBarycenter C))
    (hbarycenter : componentBarycenter C = -1) :
    componentBlock C = componentMass C • Measure.dirac (-1 : Real)
```

and then:

```lean
theorem support_unique_in_component_from_secondary_rigidity
    {mu : ProbabilityMeasure UnitInterval1038}
    {C : PositiveComponent mu}
    (R : ComponentReplacement mu C)
    (hnormalized :
      normalizedComponentBlock C = Measure.dirac (componentBarycenter C))
    (hbarycenter : componentBarycenter C = -1) :
    forall t : Real,
      t in (realMeasure mu).support -> t in C.interval -> t = -1
```

Lean status: the second theorem is now essentially proved by the current bridge
`support_unique_in_component_of_normalizedComponentBlock_eq_dirac_barycenter`.
The still-hard part is proving `componentBarycenter C = -1` from the real
variation/normalization argument.

### 6. Boundary average and endpoint mass

Let `C=(a,b)` with `b>0`, and let

$$
  p=\mu(\{-1\}).
$$

The boundary variation must prove

$$
  1\le (b+1)p+(1-b)(1-p).
$$

Since

$$
  (b+1)p+(1-b)(1-p)=1-b+2bp,
$$

and `b>0`, this implies

$$
  p\ge {1\over2}.
$$

Lean target shape:

```lean
theorem boundary_average_from_selected_component
    {mu : ProbabilityMeasure UnitInterval1038}
    {C : PositiveComponent mu}
    (hright : 0 < C.right)
    (hboundary_source : -- right-boundary nonpositivity / distance source
      True) :
    1 <= (C.right + 1) *
          (((mu : Measure UnitInterval1038)
            {t : UnitInterval1038 | (t : Real) = -1}).toReal) +
        (1 - C.right) *
          (1 - (((mu : Measure UnitInterval1038)
            {t : UnitInterval1038 | (t : Real) = -1}).toReal))
```

Lean acceptance requirements:

- The boundary point must have the required off-diagonal or integrability proof.
- The proof should feed the existing `tao_boundary_average_of_boundary_distance_upper`
  or its current narrowed bridge.
- The half-mass conclusion must come from the displayed inequality, not from a
  provider field.

### 7. Assemble provider-free Standard Reduction

After obligations 1--6 are proved, assemble:

```lean
theorem taoVariationComponentPackage_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective mu <=
        unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective mu ->
      unitIntervalSecondMomentObjective mu <=
        unitIntervalSecondMomentObjective nu) :
    TaoVariationComponentPackage (unitIntervalLogPotential mu)
```

Then prove the final target theorem by applying the existing endpoint package
bridge.  At that point the old provider theorem can remain only as a backwards
compatibility wrapper.

## Current Lean status

Already proved, under explicit hypotheses:

- compact-threshold-core and lower-semicontinuity infrastructure for the
  truncated objective;
- primary minimizer and second-moment secondary minimizer existence;
- endpoint mass plus normalized support implies positivity on
  `BaselinePunctured`;
- puncturing `{-1}` costs zero Lebesgue measure;
- endpoint-remainder mass/support bookkeeping;
- support uniqueness implies endpoint-remainder log-kernel integrability;
- zero-neighborhood implies support uniqueness;
- component-block atomization implies zero-neighborhood;
- normalized component-block atomization implies component-block atomization;
- normalized atomization plus `componentBarycenter C = -1` implies support
  uniqueness inside the component;
- replacement/second-moment equality can be converted into normalized Dirac
  atomization once its hypotheses are supplied;
- augmented span/right-gap data can feed the boundary-distance and
  boundary-average bridges.

These are valid Lean theorems.  They do not close Standard Reduction until the
provider-free variation proof supplies their hypotheses.

## Remaining hard points

1. Select the maximal positive component from the real secondary minimizer.
2. Build the actual barycenter replacement probability measure.
3. Prove Jensen and primary objective nonincrease for that replacement.
4. Prove secondary rigidity for the real replacement.
5. Identify the barycenter with `-1`.
6. Prove the boundary-average source.
7. Assemble the provider-free final theorem.

## Next proof order

Do not add endpoint consequence wrappers.  The next useful theorem is the first
one that removes a real provider input:

```lean
selected_positiveComponent_from_secondaryMinimizer
```

If that is too large, split it into the following strict subgoals:

1. prove the positive set is open on the nonsingular region needed by the
   selected component;
2. construct the connected component containing `Ioo (-1) 0`;
3. prove the component is an interval `Set.Ioo a b`;
4. prove `0 < b`;
5. prove the maximal or augmented-maximal property.

## Verification scope

For Standard Reduction-only Lean work, run only the single-file compile:

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

Do not run route, forcing, 560-block, or full-repo checks for this work unless
explicitly requested.
