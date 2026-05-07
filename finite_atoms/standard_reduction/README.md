# Standard Reduction ledger

Goal: prove the Tao/natso standard reduction in Lean.  The final theorem must
start from an actual secondary minimizer and derive endpoint-normalized data.  It
must not take `hPackageFromVariation`, `hEndpointFromVariation`,
`TaoVariationalReductionInput`, or `TaoEndpointReductionInput` as external
providers.

## Target statement

For a probability measure `mu` on `[-1,1]`, write

$$
  U_\mu(x)=\int_{[-1,1]} \log {1\over |x-y|}\,d\mu(y),
  \qquad
  E_\mu=\{x:U_\mu(x)>0\}.
$$

Let the primary objective be

$$
  F(\mu)=\lambda(E_\mu),
$$

implemented in Lean first through the truncated objective
`unitIntervalTruncatedPositiveSetObjective`.  Let the secondary objective be the
second moment

$$
  Q(\mu)=\int_{[-1,1]} y^2\,d\mu(y).
$$

The intended theorem is:

```lean
theorem unitInterval_standardReduction_from_secondaryMinimizer
    {mu : ProbabilityMeasure UnitInterval1038}
    (hPrimary : forall nu,
      unitIntervalTruncatedPositiveSetObjective mu <=
        unitIntervalTruncatedPositiveSetObjective nu)
    (hSecondary : forall nu,
      unitIntervalTruncatedPositiveSetObjective nu <=
          unitIntervalTruncatedPositiveSetObjective mu ->
      unitIntervalSecondMomentObjective mu <=
        unitIntervalSecondMomentObjective nu) :
    NormalizedEndpointPotential (unitIntervalLogPotential mu)
```

A baseline-length corollary then gives

$$
  \lambda(E_\mu)\ge \sqrt2.
$$

## Mathematical proof spine

The proof must produce two normalized facts:

$$
  \operatorname{supp}\mu\subseteq\{-1\}\cup[0,1],
  \qquad
  \mu(\{-1\})\ge {1\over2}.
$$

Once these are known, the downstream argument is short.  For
`x in (-sqrt 2,0)`, `x != -1`, write

$$
  p=\mu(\{-1\}),
  \qquad
  \mu=p\delta_{-1}+(1-p)\rho,
  \qquad
  \operatorname{supp}\rho\subseteq[0,1].
$$

For `y in [0,1]`,

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

If `-1 < x < 0`, then

$$
  |x+1|(1-x)=1-x^2<1.
$$

If `-sqrt 2 < x < -1`, then

$$
  |x+1|(1-x)=x^2-1<1.
$$

Hence `U_mu(x) > 0`, so

$$
  (-\sqrt2,0)\setminus\{-1\}\subseteq E_\mu.
$$

Since `{-1}` has Lebesgue measure zero,

$$
  \lambda(E_\mu)\ge\lambda((-\sqrt2,0))=\sqrt2.
$$

The real work is proving the two normalized facts from secondary minimality.

## Variation proof obligations

### 1. Select the positive component

From the secondary minimizer, construct a genuine positive component
`C=(a,b)` such that

$$
  (-1,0)\subseteq C,
  \qquad
  b>0,
$$

and `C` is maximal or augmented maximal in the exact sense needed by the
boundary-distance lemmas.  This is a topology/positive-set theorem and cannot
use finite-atom route information.

### 2. Build the barycenter replacement

Decompose

$$
  \mu=\mu_C+\mu_{C^c},
  \qquad
  m=\mu_C(\mathbb R)>0,
$$

and define the barycenter

$$
  c={1\over m}\int_C y\,d\mu_C(y).
$$

The replacement measure is

$$
  \nu=\mu_{C^c}+m\delta_c.
$$

Lean must prove this is an admissible probability measure on `UnitInterval1038`
and that its potential is the existing `componentReplacementPotential`.

### 3. Prove primary objective nonincrease

For `x notin C`, Jensen gives

$$
  m\log {1\over |x-c|}
  \le
  \int_C \log {1\over |x-y|}\,d\mu_C(y),
$$

hence

$$
  U_\nu(x)\le U_\mu(x)
$$

outside the component, modulo diagonal/tail exceptions.  The exceptions must be
finite, null, or arbitrarily small; the full support of `mu` cannot be used as
an exception.  Using the existing small-exception machinery, this must yield

$$
  F(\nu)\le F(\mu).
$$

### 4. Use secondary rigidity

The replacement decreases second moment by the component variance:

$$
  Q(\nu)
  =Q(\mu)-\int_C y^2\,d\mu_C(y)+mc^2
  =Q(\mu)-\int_C (y-c)^2\,d\mu_C(y)
  \le Q(\mu).
$$

Since `mu` is primary-minimizing and `F(nu) <= F(mu)`, `nu` is also primary
minimizing.  Secondary minimality gives `Q(mu) <= Q(nu)`.  Therefore

$$
  \int_C (y-c)^2\,d\mu_C(y)=0,
  \qquad
  \mu_C=m\delta_c.
$$

The endpoint-identification part of the variation argument must then prove

$$
  c=-1,
  \qquad
  \mu_C=m\delta_{-1}.
$$

### 5. Derive support uniqueness and endpoint mass

Atomization gives support uniqueness inside the component:

$$
  \operatorname{supp}\mu\cap C\subseteq\{-1\}.
$$

Together with component placement, this must give the normalized support
condition

$$
  \operatorname{supp}\mu\subseteq\{-1\}\cup[0,1].
$$

The boundary variation must also prove, for `C=(a,b)` and
`p=mu({-1})`,

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

This boundary inequality is the only legitimate source of the half-mass bound.
It must not remain a provider hypothesis in the final theorem.

## Current Lean status

Already proved under explicit hypotheses:

- compact-threshold-core and lower-semicontinuity infrastructure for the
  truncated objective;
- existence of a primary minimizer and second-moment secondary minimizer;
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

These are real Lean theorems.  They are still conditional: the variation proof
must produce their hypotheses.

## Remaining hard mouths

1. **Component selection.**  Select the correct maximal positive component from
the actual secondary minimizer and prove `(-1,0) subset C`, `C=(a,b)`, `b>0`.

2. **Replacement construction.**  Build the actual barycenter replacement
probability measure and identify its potential.

3. **Primary nonincrease.**  Prove the replacement does not increase the
truncated positive-set objective, using Jensen plus the already-formal
small-exception machinery.

4. **Secondary rigidity to endpoint atomization.**  Turn primary nonincrease and
secondary minimality into `mu_C = m delta_{-1}`.

5. **Boundary average.**  Prove
`1 <= (b+1)p + (1-b)(1-p)` from the right-boundary variation argument.

6. **Provider removal.**  Assemble the above into `NormalizedEndpointPotential`
without `hPackageFromVariation`, `hEndpointFromVariation`,
`TaoVariationalReductionInput`, or `TaoEndpointReductionInput`.

## Next proof order

Do not add more endpoint consequence wrappers.  The useful order is:

1. prove the component-selection/topology theorem;
2. build the concrete barycenter replacement;
3. prove Jensen/primary nonincrease for that replacement;
4. prove secondary rigidity and endpoint atomization;
5. prove the boundary-average source;
6. assemble the final provider-free theorem.

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
