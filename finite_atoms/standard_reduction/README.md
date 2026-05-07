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
      (forall eta : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective eta) ->
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

The `hSecondary` argument is intentionally stated in the same form used by the
existing Lean bridge: it compares `mu` against every `nu` that is itself a
primary minimizer, not merely every `nu` with objective at most that of `mu`.

## Route A priority

This provider-free theorem is now the active Route A hard mouth.  The paper
route below is a working draft, not yet audit-clean: the current gaps are the
regular row-dictionary check needed for the \(U(0)>0\) KKT obstruction, the
Jensen/small-exception nonincrease argument, the pure-interior-atom Schur
determinant identity, and the nonregular flat-threshold routing lemma.  After
those are closed, this is the outer step that connects the compactified
finite-gap inner theorem to the original polynomial problem.

The route should not use compact-chart JSON or LRLR row probes.  The current proof target is:

```lean
theorem unitInterval_standardReduction_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective mu <=
        unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary : forall nu : ProbabilityMeasure UnitInterval1038,
      (forall eta : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective eta) ->
      unitIntervalSecondMomentObjective mu <=
        unitIntervalSecondMomentObjective nu) :
    NormalizedEndpointPotential (unitIntervalLogPotential mu)
```

The separate normalized strict counterexample exhaustion statement is recorded
as a Route A draft in the 1038 ledger:

```text
NormalizedStrictCounterexampleFiniteGapExhaustion:
  every strict normalized counterexample enters a regular compactified
  finite-gap chart, a Gate 3 boundary/lower stratum, or a Gate 5
  regularization branch.
```

Thus, for formalization, the remaining Route A outer input is the
provider-free unit-interval theorem above, plus the original-to-unit-interval
normalization interface if one wants the unreduced original statement in Lean.
After the paper gaps are closed, this input turns the implication

```text
OuterStandardReductionClosure + compactified finite-gap Gates 1--7
  => L_- = M_oc
```

into an unconditional original-problem theorem.

The exact unreduced interface is simpler than an affine support-diameter
normalization, because the original problem already assumes all polynomial
roots lie in `[-1,1]`:

```text
PolynomialEmpiricalMeasureBridge:
  for f(x)=prod_j (x-r_j), r_j in [-1,1], the empirical root measure
  mu_f=(1/n) sum_j delta_{r_j} satisfies
  U_mu_f(x)=(1/n) log(1/|f(x)|), hence |f(x)|<1 iff U_mu_f(x)>0
  up to zero-measure root points.
```

Thus every original polynomial strict counterexample is already a strict
unit-interval measure counterexample.  Reflection is still available for
orientation and preserves length.

Lean audit narrows this further.  `StandardReduction.lean` already contains:

- `admissible_probability_lsc_exists_minimizer_ennreal`;
- `admissible_probability_lsc_exists_secondary_minimizer_ennreal_primary`;
- `taoNormalizePoint`, `taoNormalizeRealMeasure`, `taoNormalizedPotential`;
- `volume_positiveSet_taoNormalizedPotential`.
- `PolynomialEmpiricalPotentialData`;
- `PolynomialEmpiricalPotentialData.measure_lower_bound_transfers_to_polynomial_sublevel`.

Thus minimizer extraction preserves a strict gap once a normalized admissible
competitor exists, and the polynomial sublevel bridge already has a Lean shape
modulo the expected root-list/product identity data.  The remaining work is the
provider function consumed by the existing standard-reduction theorem, plus the
final root-list/product-data assembly for original polynomials.

The value-normalization side is closed at paper level: the affine
unit-interval normalization changes logarithmic potentials only by an additive
constant, the threshold shifts by the same constant, and the endpoints
\(-1,1\) fix the scale.  Thus the original normalized objective, the
compactified finite-gap objective, and the one-cut value \(M_{\rm oc}\) refer
to the same length functional.  The decimal value is only a numerical
evaluation of the one-cut equations.

For the exhaustion input, the strict-threshold-core step is closed: if
\(|\{U_\mu>0\}|<M_{\rm oc}\), then for some \(\tau>0\),
\(|\{U_\mu>\tau\}|<M_{\rm oc}\).  The regular-core stability part is also
closed: on a compact window with
finitely many simple threshold boundary points, small \(C^1\) perturbations of
the potential only move those endpoints, so strict length gap below
\(M_{\rm oc}\) persists.  The finite-gap approximation hard mouth has been
closed in the regular branch by smooth reservoir approximation, positive
finite-pole Cauchy approximation, and the fact that the finite-gap
compactification already admits finitely many positive atoms at pole points.
The nonregular threshold, row-rank, support-collision, no-reservoir, and
margin-loss cases route to Gate 3/Gate 5.

P1 audit.  The atom-to-compactified-finite-gap realization gap is closed in the
Route A form needed here.  A positive atom separated from the threshold window
is either exactly a positive real pole stratum of the compactified finite-gap
data, or, in the equivalent shrinking-cut picture, is the \(C^1\)-limit on
separated compact windows because the log kernel and its \(x\)-derivative are
uniformly continuous there.  Thus `AtomToCollapsedCutRealizationLemma` is not
the active standard-reduction obstruction.

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
      (forall eta : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective eta) ->
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
- Do not import route/forcing facts outside this standard-reduction proof.

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

The admissibility part is mathematically closed.  If \(C\subset[-1,1]\) has
positive mass \(m\), then the barycenter
\[
c_C={1\over m}\int_C y\,d\mu_C(y)
\]
lies in \([-1,1]\), because it is the expectation of a probability measure on
the convex set \([-1,1]\).  Replacing \(\mu_C\) by \(m\delta_{c_C}\) preserves
total mass, positivity, and unit-interval support.  The remaining work in this
step is not admissibility; it is proving primary objective nonincrease for the
truncated positive-set objective and then using secondary minimality for
rigidity.

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

This step is closed conditionally on the selected-component and
small-exception data.  The existing Lean bridge
`componentReplacementProbability_truncatedObjective_le_of_tailMass_small_exception_comparisons`
packages the strict-outside Jensen comparison, tail/diagonal exceptions, and
the replacement probability.  The ordinary-to-truncated transfer is already
available as
`unitIntervalPositiveSetObjective_le_truncatedObjective_of_threshold_tail_small_exceptions`.
Thus the remaining provider-free issue is not the replacement inequality after
the component is selected; it is supplying the selected component and regular
exception data from the actual secondary minimizer.

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

This algebraic identity is closed at paper level:

$$
  Q(\mu)-Q(\nu)=\int_C (y-c)^2\,d\mu_C(y),
$$

because \(c=m^{-1}\int_C y\,d\mu_C(y)\).  Equality is zero variance, hence the
normalized component block is concentrated at \(c\).  The Lean layer already
contains the corresponding second-moment equality and normalized-component
Dirac bridge.  The remaining issue is proving the primary nonincrease needed
before secondary minimality can be applied.

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
      (forall eta : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective eta) ->
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

Thus endpoint/support identification is reduced to one mathematical input:

```lean
componentBarycenter C = -1
```

Once this is supplied, the existing bridge gives support uniqueness inside the
component and the endpoint atomization fields needed downstream.

Do not use boundary average alone to prove this equality.  Endpoint mass at
\(-1\) may sit outside the open component interval, so boundary average does
not by itself identify the component barycenter.  The safe route is
zero-neighborhood/support exclusion: if the component block is
\(\delta_{c_C}\) and \(c_C\ne-1\), a small open neighborhood of \(c_C\) inside
the component avoids \(-1\) but has positive mass, contradicting the
zero-neighborhood provider.

Current minimal provider-free hard mouth:

```text
SelectedComponentZeroNeighborhoodFromLocalVariation
```

After a selected component is available, admissibility, Jensen primary
nonincrease, secondary variance rigidity, and support uniqueness are already
covered conditionally.  The remaining proof must supply zero-neighborhood for
the actual secondary minimizer, plus the selected-component/right-gap fields.
The zero-neighborhood proof should split into non-Dirac subblocks and pure
interior atoms; failures of reservoir, rank, or flat determinant route to
Gate 3/Gate 5/exhaustion.

The non-Dirac subblock branch is closed at paper level by localized barycenter
replacement.  The remaining local hard branch is:

```text
InteriorAtomPrimaryLevelVariation
```

It must exclude a pure interior atom by a corrected primary-level variation
with strict secondary decrease, or route no-reservoir/rank/flat failures to
Gate 3/Gate 5/exhaustion.

The regular-reservoir part of this branch is now closed at paper level.  The
projected atom motion gives a Schur coefficient; nonzero coefficient gives a
first-order secondary descent.  On the critical coefficient stratum, the
three-packet reservoir construction gives a second-order primary-level descent.
The determinant obstruction for every reservoir triple would force
`L_red` to be affine in `y^2`, impossible for the regular logarithmic row.
Thus only no-reservoir, row-rank loss, or flat determinant remain, and those
are routing cases.

Paper lemma to cite:

```text
InteriorAtomPrimaryLevelVariationExclusion.
```

Let \(t\in C\setminus\{-1\}\) be a pure interior atom of the selected component
block, and assume the regular reservoir hypotheses: there are three reservoir
points \(r_1,r_2,r_3\) outside the protected endpoint/right-gap windows whose
row map to the active primary constraints has full rank, all reservoir masses
have a fixed positive margin, and the threshold boundary is simple.  Then this
pure atom is impossible for a primary/secondary minimizer.

Proof sketch with the required signs.  Move a small mass \(\eta\) from \(t\)
to a nearby \(t+s\) and compensate the active primary rows by reservoir
corrections \(c_i(s,\eta)\).  Full rank gives
\[
  c(s,\eta)=-B^{-1}\Delta(t,s,\eta)=O(\eta |s|),
\]
so all corrected reservoir masses remain positive for small \(\eta,s\).  The
first variation of the primary objective is therefore the reduced row
\[
  L_{\rm red}'(t)s\,\eta+o(\eta |s|).
\]
If \(L_{\rm red}'(t)\ne0\), choose the sign of \(s\) so the primary objective
strictly decreases, contradicting primary minimality.

If \(L_{\rm red}'(t)=0\), the same compensated variation has zero first-order
primary change.  The secondary moment changes by
\[
  \eta\big((t+s)^2-t^2\big)+O(\eta |s|)
  =
  2t\eta s+\eta s^2+O(\eta |s|),
\]
after the reservoir projection.  If the projected coefficient is nonzero, the
sign of \(s\) gives a strict secondary decrease while preserving primary
minimality to first order, contradicting `hSecondary`.

On the codimension-one stratum where the projected secondary coefficient also
vanishes, use two symmetric atom packets at \(t\pm s\) and the same reservoir
projection.  The first-order primary and secondary terms cancel.  The
second-order primary term is governed by the reduced curvature.  If it is
negative for one packet, primary minimality is contradicted.  If every
reservoir triple makes the reduced curvature vanish, the Schur determinant
identity forces the reduced logarithmic row to agree with an affine function
of \(y^2\) on a reservoir interval.  A nonconstant logarithmic potential cannot
be affine in \(y^2\) on an interval in the regular branch.  Hence the only
remaining alternatives are exactly failure of full-rank reservoir, loss of
threshold simplicity, or no positive reservoir margin; these are routed to
Gate 3, Gate 5, or the normalized finite-gap exhaustion branch.

This closes the pure-interior-atom branch at paper level, conditional only on
the regular reservoir hypotheses already listed in the provider theorem.

### UnitIntervalStandardReductionFromSecondaryMinimizer

Combining the preceding providers gives the desired provider-free standard
reduction theorem.

```lean
theorem unitInterval_standardReduction_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective mu <=
        unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary : forall nu : ProbabilityMeasure UnitInterval1038,
      (forall eta : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective eta) ->
      unitIntervalSecondMomentObjective mu <=
        unitIntervalSecondMomentObjective nu) :
    NormalizedEndpointPotential (unitIntervalLogPotential mu)
```

Proof.  By `ZeroPositivityFromSecondaryMinimalityRegular`, choose
\(\delta>0\) such that \(U_\mu>0\) on \((-1,\delta]\).  Apply
`exists_positiveComponent_baseline_right_pos_of_span_global_positive` to get a
positive component \(C\) with
\[
(-1,0)\subset C,\qquad 0<C.right.
\]
The support-policy and augmented-maximal selection lemmas upgrade \(C\) to an
augmented-maximal component.  If the right gap after \(C\) fails, then the
failure is exactly a support collision, flat-threshold, no-reservoir, or
row-rank boundary; these are routed to Gate 3, Gate 5, or normalized finite-gap
exhaustion.  In the regular branch, obtain
\[
[C.right,C.right+\delta_0]\cap
\bigl(\operatorname{AugPos}(\mu)\cup\operatorname{supp}\mu\bigr)=\varnothing.
\]

The component mass is positive because \(C\) is a positive component and
contains support in the regular branch.  Let
\[
R=\texttt{ComponentReplacement.of\_mass\_pos}\ C.
\]
By `SelectedComponentZeroNeighborhoodFromLocalVariation`,
\[
\forall U\subset C,\quad U\text{ open},\quad -1\notin U
\Rightarrow \mu(U)=0.
\]

The existing Lean bridge
`normalizedComponentBlock_eq_dirac_endpoint_of_secondary_minimality_smallException_zero_neighborhood`
then applies: barycenter replacement gives primary nonincrease, and secondary
minimality forces zero variance.  The zero-neighborhood provider identifies
the atomized component block with \(\delta_{-1}\), not an interior atom.

Finally, the boundary-average bridge
`boundary_average_of_spanning_augmented_right_gap_normalized_atomized` gives
the endpoint mass inequality, and
`taoVariationComponentPackage_of_canonicalEndpointMass_normalized_atomization_baseline_data`
builds the Tao variation package.  Therefore
\[
\texttt{NormalizedEndpointPotential }(\texttt{unitIntervalLogPotential mu})
\]
follows.  This is exactly the provider-free theorem consumed by the Route A
compactified finite-gap assembly.

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
      (forall eta : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective eta) ->
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

The component-replacement bookkeeping is no longer the live hard point.
Barycenter admissibility, Jensen primary nonincrease, secondary variance
rigidity, endpoint identification from zero-neighborhood, and the regular
zero-neighborhood proof have paper-level providers recorded in the 1038 ledger.

The paper-level 1038 ledger now supplies these remaining hard points in the
unit-interval standard outer-normalized class:

1. regular selected-component data are obtained from zero positivity, baseline
   placement, off-diagonal/tail control, and no-diagonal policy;
2. every failure of those provider fields--diagonal or singular tail,
   continuity loss, row-rank loss, no reservoir, flat threshold, right-gap
   failure--is routed to Gate 5, Gate 3, or compactified finite-gap exhaustion;
3. the regular provider fields match the existing Lean theorem exactly.

The separate normalized strict-counterexample finite-gap exhaustion statement
is also closed at paper level in the 1038 ledger: regular states are
approximated by row-normalized positive finite-pole data, and nonregular
failures route to Gate 3 or Gate 5.  The live Standard Reduction work is now
formal: turn the paper provider package into the provider function consumed by
the existing Lean theorem, and keep the original-to-unit-interval
normalization interface separate.

Lean bridge audit.  The exact theorem currently consuming the provider is:

```lean
unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_normalized_endpoint_baseline_from_augmented_maximal_component_replacement_augmented_span_right_gap_replacement_rigidity_zero_neighborhood_data
```

Its provider argument is a function of `mu`, `hPrimary`, and `hSecondary`
returning:

- `C : PositiveComponent mu`;
- `R : ComponentReplacement mu C`;
- `epsilon, delta : Real` with `0 < epsilon`, `0 < C.right`, `0 < delta`;
- `C.AugmentedIntervalMaximal`;
- `Set.Ioo (-1 - epsilon) C.right ⊆ unitIntervalAugmentedPositiveSet mu`;
- `Set.Ioo (-1) 0 ⊆ C.interval`;
- `Set.Icc C.right (C.right + delta) ∩
  (unitIntervalAugmentedPositiveSet mu ∪ (realMeasure mu).support) = ∅`;
- zero-neighborhood:
  `∀ U, IsOpen U → U ⊆ C.interval → -1 ∉ U → realMeasure mu U = 0`.

The Route A paper providers now match these fields in the regular branch.
The next formal step is therefore to prove this provider function, not to add
another endpoint theorem.

Lean check.  On 2026-05-08 the single-file command in the verification section
compiled `finite_atoms/common/lean/StandardReduction.lean` successfully against
the local mathlib workspace.  The output contained only existing linter
warnings.  This verifies that the bridge theorem above is currently available
and that the remaining work is the provider proof, not repair of the endpoint
bridge.

Selected-component Lean audit.  The component-topology part already has usable
bridges:

- `exists_positiveComponent_augmentedMaximal_of_baseline_and_zero_auto_bdd_midpoint`
  gives an augmented-maximal component from ordinary baseline positivity,
  positivity at `0`, openness, and the no-diagonal policy.
- `exists_positiveComponent_baseline_right_pos_of_truncated_baseline_and_zero_offDiagonal_parts`
  gives the ordinary component from truncated baseline/zero positivity plus
  off-diagonal separation.
- `exists_positiveComponent_baseline_right_pos_of_positive_baseline_zero_tail`
  derives the truncated inputs from ordinary positivity and explicit singular
  tail control.
- `exists_positiveComponent_baseline_right_pos_of_baseline_local_compact_data_and_zero_threshold_tail`
  is the sharpest current constructor for Route A: it takes local compact
  baseline positivity/tail data, a positive threshold at `0`, off-diagonal
  conditions, and produces the right-positive component.
- `exists_positiveComponent_baseline_right_pos_of_span_global_positive` is even
  shorter for component selection alone: ordinary positivity on one span
  `Ioc (-1) delta` already gives a component containing `Ioo (-1) 0` with
  positive right endpoint.  The threshold/tail constructors are still needed
  when the component must be fed into the truncated-objective and replacement
  bridges.
- `exists_positiveComponent_augmentedMaximal_of_span_positive_support_policies_auto_bdd_midpoint`
  already gives the augmented-maximal version from span positivity plus the
  regular support policy.  Thus the augmented-maximal field in the provider is
  not a new topology theorem.

Therefore the formal selected-component task is not interval topology.  It is
first to prove ordinary span positivity for the actual secondary minimizer, and
then to supply the regularity data required downstream: local compact baseline
positivity, zero/right threshold margins, tail control, and
no-diagonal/off-support data.  Failure of any of those analytic inputs is a
Gate 3/Gate 5/exhaustion route, not a new provider field.

## Next proof order

Do not add endpoint consequence wrappers.  The next useful theorem is the first
one that removes a real provider input:

```lean
selected_positiveComponent_from_secondaryMinimizer
```

If that is too large, split it into the following strict subgoals:

1. prove ordinary span positivity on `Ioc (-1) delta` for some `delta > 0`;
2. apply `exists_positiveComponent_baseline_right_pos_of_span_global_positive`
   for the ordinary selected component, or
   `exists_positiveComponent_augmentedMaximal_of_span_positive_support_policies_auto_bdd_midpoint`
   when the augmented-maximal provider field is needed;
3. prove the local compact baseline/right threshold, tail, and
   no-diagonal/off-support data needed by the truncated and replacement bridges;
4. apply the existing threshold/tail selected-component constructors when a
   truncated-objective component is required;
5. upgrade to augmented span/right-gap data using the existing
   augmented-maximal/right-gap bridges;
6. prove zero-neighborhood by the local variation package;
7. record every failure of these regular inputs as a Gate 3/Gate 5/exhaustion
   route, not as an assumption of the endpoint theorem.

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

## Span positivity provider target

The next provider-free theorem should remove the first analytic input used by
the selected-component constructors.

```lean
theorem span_positive_from_secondaryMinimizer_regular
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective mu <=
        unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary : forall nu : ProbabilityMeasure UnitInterval1038,
      (forall eta : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective eta) ->
      unitIntervalSecondMomentObjective mu <=
        unitIntervalSecondMomentObjective nu) :
    exists delta : Real,
      0 < delta /\
      forall y : Real, y in Set.Ioc (-1 : Real) delta ->
        0 < unitIntervalLogPotential mu y
```

Paper proof target.  In the regular branch, baseline positivity is obtained
from the outer-normalized minimizer orientation.  If positivity reaches up to
`0` but no right span exists, then `0` is a flat or singular boundary of the
positive set.  The regular boundary alternative gives a primary-level tangent
at `0`; if such a tangent has a secondary descent, it contradicts secondary
minimality.  The detailed ledger now records the correct boundary-variation
row \(W_\mu\) and proves the log-row `ZeroBoundaryKKTObstructionLemma`.  The
remaining paper target is to verify that the regular provider branch uses only
the stated log-row dictionary, or to name and route any extra row.  The
remaining failures are exactly nonregular routes: diagonal/singular tail,
row-rank loss, no reservoir, or flat threshold.  Those go to Gate 3, Gate 5, or
the normalized finite-gap exhaustion branch.

Once this theorem is available, the Lean path is short:

1. apply `exists_positiveComponent_baseline_right_pos_of_span_global_positive`
   to obtain the ordinary selected component;
2. apply
   `exists_positiveComponent_augmentedMaximal_of_span_positive_support_policies_auto_bdd_midpoint`
   when the augmented-maximal provider field is needed;
3. separately supply the local compact tail/off-support data needed by the
   truncated-objective and replacement bridges.

This is now the first formal target before zero-neighborhood.

## Minimal provider theorem for the current Lean bridge

The existing endpoint bridges already consume the standard-reduction data once
it is available.  The remaining provider-free proof should therefore target one
minimal package, not more endpoint wrappers:

```lean
theorem selectedComponent_provider_from_secondaryMinimizer_regular
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary : forall nu : ProbabilityMeasure UnitInterval1038,
      unitIntervalTruncatedPositiveSetObjective mu <=
        unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary : forall nu : ProbabilityMeasure UnitInterval1038,
      (forall eta : ProbabilityMeasure UnitInterval1038,
        unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective eta) ->
      unitIntervalSecondMomentObjective mu <=
        unitIntervalSecondMomentObjective nu) :
    exists C : PositiveComponent mu,
      exists R : ComponentReplacement mu C,
      exists epsilon delta : Real,
        0 < epsilon /\
        0 < delta /\
        0 < C.right /\
        C.AugmentedIntervalMaximal /\
        Set.Ioo (-(1 : Real) - epsilon) C.right <=
          unitIntervalAugmentedPositiveSet mu /\
        Set.Ioo (-1 : Real) 0 <= C.interval /\
        Set.Icc C.right (C.right + delta) ∩
          (unitIntervalAugmentedPositiveSet mu ∪ (realMeasure mu).support) =
            ∅ /\
        (forall U : Set Real, IsOpen U -> U <= C.interval -> -1 ∉ U ->
          realMeasure mu U = 0)
```

Given this theorem, the current Lean endpoint proof is just:

```lean
unitIntervalTruncatedPositiveSetObjective_exists_secondMoment_normalized_endpoint_baseline_from_augmented_maximal_component_replacement_augmented_span_right_gap_replacement_rigidity_zero_neighborhood_data
```

applied to the provider output.  One may also use the already-fixed
specialized bridges near the end of `StandardReduction.lean`, such as
`unitInterval_standardReduction_from_replacement_augmentedGap_zeroNeighborhood`.
The short wrapper name intended for this interface is:

```lean
unitInterval_standardReduction_from_secondaryMinimizer_of_provider
```

This short wrapper is a `noncomputable def`: it returns the endpoint package
directly once the provider output is supplied.  It still does not prove the
provider itself.

The first split of that provider is now formalized:

```lean
selectedComponent_provider_from_span_support_regular_data
```

The direct endpoint wrapper for that split is also formalized:

```lean
unitInterval_standardReduction_from_span_support_regular_data
```

A lower-input selected-component wrapper is now formalized as well:

```lean
selectedComponent_provider_from_baseline_zero_regular_data
unitInterval_standardReduction_from_baseline_zero_regular_data
```

This reduces the remaining regular-provider inputs to baseline positivity,
positivity at `0`, openness of the positive set, the no-diagonal augmented
support policy, and regular row data.

It derives the provider output from span positivity, support policy, and
regular data for the selected component.  Thus the remaining Lean work is now
exactly to prove those analytic inputs from `hPrimary` and `hSecondary`.

Thus the proof work is now concentrated in three analytic subclaims about the
actual secondary minimizer:

1. span positivity and support policy, giving the component and augmented
   maximality;
2. a right gap after the selected component, or else a Gate 3/Gate 5/exhaustion
   route;
3. zero-neighborhood inside the selected component away from \(-1\).

The non-Dirac subblock part of zero-neighborhood is handled by localized
barycenter replacement.  The live local hard mouth is the pure interior atom
case: an interior atom would have to satisfy a primary-level first-variation
KKT condition.  In the regular reservoir case, the two-packet atom variation
breaks this condition; no-reservoir, reduced-rank, and flat-boundary failures
are exactly the nonregular routes, not a separate certificate route.

## Provider-free proof chain, paper version

This records the paper proof already used in the Route A discussion, in the
order needed to prove
`selectedComponent_provider_from_secondaryMinimizer_regular`.

### ZeroPositivityFromSecondaryMinimalityRegular

Let `mu` be a primary minimizer and secondary minimizer among primary
minimizers.  In the regular outer-normalized branch,
\[
U_\mu(0)>0
\]
and, more generally, there exists \(\delta>0\) such that
\[
U_\mu(y)>0\qquad (y\in(-1,\delta]).
\]

Proof.  The outer orientation places the baseline positive span on the left of
the origin.  If \(U_\mu(0)\le0\), then either the positive span stops before
the origin or the origin is a zero-threshold boundary.  In the first case,
moving an infinitesimal amount of mass from the selected positive block toward
the right creates a primary-level admissible competitor with strictly smaller
positive-set length, contradicting primary minimality.  In the second case,
regularity gives a nonzero boundary derivative and hence a signed tangent that
moves the simple boundary inward.  If this tangent has negative primary first
variation, primary minimality is contradicted.  If the primary first variation
vanishes, the same tangent has a nonzero secondary projection unless the KKT
normal annihilates every reservoir direction.  A vanishing projection for all
reservoir directions would force the logarithmic variation row to be constant
on a reservoir interval, impossible in the regular branch.  Thus the only
alternatives are flat threshold, no reservoir, row-rank loss, diagonal
singularity, or support collision, all of which are routed to Gate 3, Gate 5,
or normalized finite-gap exhaustion.  Hence the regular branch has
\(U_\mu(0)>0\).  Openness of the regular positive set gives the right span
\((-1,\delta]\).

This proves the analytic input used by
`exists_positiveComponent_baseline_right_pos_of_span_global_positive`.

### SelectedComponentZeroNeighborhoodFromLocalVariation

Let \(C\) be the selected positive component containing \((-1,0)\), chosen
with \(0<C.right\) and augmented maximality.  Then
\[
\forall U\subset C,\quad U\text{ open},\quad -1\notin U
\Rightarrow \mu(U)=0.
\]

Proof.  Suppose first that some open \(U\subset C\), \(-1\notin U\), carries a
non-Dirac positive subblock.  Replace that subblock by its barycenter while
using the local reservoir to restore the finitely many active primary rows.
The replacement remains in \([-1,1]\), Jensen gives primary objective
nonincrease, and the variance identity gives a strict secondary decrease
unless the subblock was already Dirac.  This contradicts secondary minimality.

It remains to exclude a pure interior atom \(m\delta_t\), \(t\in C\setminus
\{-1\}\).  Under the regular reservoir hypotheses, this is exactly
`InteriorAtomPrimaryLevelVariationExclusion`: a compensated atom motion gives
either first-order primary descent, first-order secondary descent on the
primary-critical stratum, or a symmetric-packet second-order primary descent.
If every such packet is blocked, the reduced logarithmic row would be affine
in \(y^2\) on a reservoir interval, impossible in the regular branch.  The
only remaining cases are no-reservoir, row-rank loss, flat threshold, or
support collision, already routed to Gate 3/Gate 5/exhaustion.  Thus no mass
can live in \(C\setminus\{-1\}\), proving zero-neighborhood.
