# Erdős Problem 1038: Tao-Facing Summary

This is the short shareable summary.  The detailed attempt ledger is
`1038_dual_two_interval_progress.md`.

## 1. Normalization

For a monic real-rooted polynomial

\[
f(x)=\prod_{j=1}^n(x-r_j),\qquad r_j\in[-1,1],
\]

set

\[
\mu_f=\frac1n\sum_j\delta_{r_j},\qquad
U_\mu(x)=\int\log\frac1{|x-t|}\,d\mu(t),\qquad
E_\mu=\{x:U_\mu(x)>0\}.
\]

Then

\[
\{x:|f(x)|<1\}=E_{\mu_f}.
\]

## 2. Supremum

\[
\boxed{L_+=2\sqrt2.}
\]

The lower example is \(f(x)=x^2-1\).  The upper bound is the standard
length-two support extremal bound, with equality at

\[
\frac12\delta_{-1}+\frac12\delta_1.
\]

## 3. Infimum: Current Bounds

The current one-cut candidate / provisional upper value is

\[
M_{\rm oc}=1.8344304757626617\ldots,
\]

with one-cut endpoints

\[
x_L=-1.8081073680988165,\qquad x_R=0.02632310766384517.
\]

The current finite-certificate lower-bound status in this repository is

\[
\boxed{L_-\ge1.814600}
\]

conditional on the standard Tao/natso minimizer reduction

\[
\mu(\{-1\})\ge\frac12,\qquad
\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1].
\]

The gate chain below gives a conditional exact-route skeleton:

\[
\boxed{
\text{if the remaining sign, compactness, and regularity lemmas are closed,
then }L_- = M_{\rm oc}.
}
\]

The unconditional equality is not yet proved.  The decimal is only the
numerical evaluation of the one-cut equations defining the current one-cut
candidate / provisional upper candidate \(M_{\rm oc}\).

## 4. The \(1.814600\) Finite-Certificate Package

The \(1.814600\) package is a piecewise five-atom tail certificate with
\(K=560\) blocks.

Relevant package:

```text
finite_atoms/piecewise_five_atom_181460_560/
finite_atoms/route_181460_560/
```

The route uses the same forcing split

\[
B=1.708,\qquad M=1.814600,
\]

so the tail contribution is

\[
M-B=0.106600.
\]

The route arithmetic is

\[
1.708+(1.814600-1.708)=1.814600.
\]

### Required-domain status

This is not a full \([-1,1]\) positivity certificate.

Under the normalized support condition

\[
\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1],
\]

each block only needs

\[
U_{\lambda_a}(x)>0\qquad x\in\{-1\}\cup[0,1].
\]

In \(y=x-a\), the required domains are

\[
[C-1,A-1]\cup[C,A+1].
\]

The middle gap \((A-1,C)\) corresponds to \(x\in(-1,0)\).  Some blocks are
negative there; this is an overcheck region and is not used by the conditional
finite-atom argument.

Certificate summary:

```text
M = 1.814600
K = 560
overall_worst_required.value = 9.534343713646365e-06
all_required_blocks_ok = true
num bad required blocks = 0
```

The generated Lean chunks record the block coverage and required-domain
logarithmic positivity.  The independent Python checker agrees with the
required-domain margin.

Public wording:

> Conditional on the standard normalized minimizer reduction, the repository
> contains a required-domain finite-atom certificate giving \(L_-\ge1.814600\).
> This is not a proof of the exact infimum.

## 5. Corrected Two-Interval Exact Route

The exact route remains the corrected endpoint-atom two-interval finite-gap
route.

For

\[
E_\varepsilon=(x_L+\varepsilon,x_R)\cup(1-\varepsilon,1),
\]

write

\[
\ell=x_L+\varepsilon,\qquad r=x_R,\qquad \beta=1-\varepsilon.
\]

The active Cauchy transform is

\[
F(z)=
\frac{z+A}{(z-\ell)(z-r)(z-1)}
\sqrt{(z-\alpha)(z-\beta)},\qquad
\sqrt{(z-\alpha)(z-\beta)}\sim z.
\]

The endpoint atom is forced:

\[
m_1=
\frac{(1+A)\sqrt{(1-\alpha)\varepsilon}}{(1-\ell)(1-r)}>0.
\]

Thus the old no-endpoint-atom ansatz is retired.

The fixed-epsilon skeleton supports this branch:

```text
epsilon = 0.002, 0.001, 0.0005, 0.0002, 0.0001, 0.00005
OVERALL TWO-INTERVAL SKELETON CHECK: PASS
(verifier integrity only, not a math proof)
```

Adjacent sampled slabs also support the branch, but sampled eta dependence is
not a continuum proof.

Four eta-uniform interval Krawczyk slabs have been closed:

```text
0.00005:0.0001   PASS
0.0001:0.0002    PASS
0.0002:0.0005    PASS
0.0005:0.001     PASS
0.001:0.002      open in this verifier
```

The open top slab should not be attacked by blindly increasing eta
subdivisions.  It likely needs a better continuation/center model or a
row-to-row split.

## 6. Main Remaining Mathematical Gap

Even if the two-interval local branch were completely certified, this would
not prove the exact infimum.

The real missing theorem is global finite-gap classification:

> Every regular counterexample with \(|E|<M_{\rm oc}\) either lies on the corrected
> one-cut/two-interval finite-gap branch, pinches or degenerates to a lower
> genus branch, or violates positivity/interlacing.

The first hard escape is a compact non-pinched \(g=2\) chamber.

Current compact \(g=2\) status is now sharper:

1. Regular free-period chambers are excluded by the period-transfer lineality
   density.  After adding the free filling variable, the period row contributes
   no independent \(\lambda\pi_0\) sign-shifter, and normal-to-lineality
   orthogonality contradicts any nonzero oriented sign-pattern normal.
2. Pinched and positivity-boundary limits are routed to corrected lower-genus
   branches, with nonnegative endpoint atoms allowed.  This is a routing
   target, not a substitute for the global lower-genus classification proof.
3. Rank-defect non-pinched interior chambers remain open.  The current hard
   target is no longer a bare rank or Schur-complement check.  The anchored
   Schiffer reduction adds the anchor row
   \[
   R_{\ell c}(G)=\delta W(c)
   =
   \int_J\log\frac1{|c-x|}G(x)\omega(x)\,dx,
   \]
   and reduces the problem to the raw augmented circuit sign on \(Z_0\).
   The quotient identity
   \[
   [Q^2]=
   \sum_\gamma
   \frac{Q(\gamma)}{P(\gamma)D_\gamma(\gamma)}[PQD_\gamma]
   \]
   shows that the period lift is already in the endpoint span modulo moving
   corrections.  Therefore quotient rank, Schur form, and endpoint
   interpolation alone cannot produce the strict lifted margin; the remaining
   theorem must use the actual \(P_\theta\)-contact/alternation structure on
   \(Z_0\), or switch to genuine second-variation data.

Current exact-route audit:

- The one-cut upper construction is now the most stable proof-grade component:
  Gate 6 defines \(M_{\rm oc}\) by exact equations and proves
  \(L_-\le M_{\rm oc}\).
- The lower bound is still open.  The first hard mouth is the compact
  non-pinched \(g=2\) rank-defect chamber, now reduced to
  `MovingSchifferMajorantSignTheorem` / raw augmented circuit signs.  The
  endpoint-period quotient no-go rules out any proof that uses only rank or
  Schur-complement bookkeeping.
- Boundary \(g=2\) routing still needs a compactness lemma.
- High genus still needs a proof that outside-row freezing gives a legitimate
  Schur complement with all global logarithmic-capacity tails accounted for.
- Lemma R still needs the regularization/row-restoration theorem from arbitrary
  minimizers to regular finite-gap approximants.

Useful corrections already recorded:

- the exact one-cut upper bound \(M_{\rm oc}\) is defined by analytical
  equations, not by a decimal;
- the no-endpoint-atom ansatz is wrong;
- brute-force small-eta subdivision is not a main route;
- whole-slab `Div2` intervalization creates artificial eta dependency;
- the naive three-kernel compact determinant is invalid;
- the determinant must use split kernels;
- the pure-\(q\) Schur scalar is insufficient;
- the rank-six Schur conclusion was dimensionally wrong;
- regular free-period compact \(g=2\) is excluded by the free-period
  lineality/sign contradiction;
- rank-defect compact \(g=2\) is reduced to the raw augmented circuit
  obstruction, not yet closed.
- the first-order endpoint-period quotient cannot close Gate 1, because the
  period lift \([Q^2]\) is already in the span of the endpoint classes
  \([PQD_\gamma]\) modulo the moving correction image.
- the Gate 1 fallback must be split: the \(\zeta=0\) no-atom branch is a
  finite collinearity test \(b_S=\Lambda\rho_S\) plus the lifted inequality
  \(b_\Pi-\Lambda\rho_\Pi<0\), while the \(\zeta\ne0\) branch is a
  \(Z_0\)-atomic cone-envelope problem.  The latter cannot be killed directly
  by finite \(Q_{\rm eff}\), because point-row Riesz loads have positive
  logarithmic blow-up.
- the active next theorem is therefore `MovingSchifferMajorantSignTheorem`:
  construct \(G_\theta=\theta\cdot V_S-V_\Pi\ge0\) on \(Z_0\), prove the
  strict affine and homogeneous residuals, equivalently prove the
  \(P_\theta=\kappa Q^2-\sum_\gamma\theta_\gamma H_\gamma^{\rm rep}\)
  alternation/sign table for the repaired moving Schiffer columns.
- viable Gate 1 attempts are now ordered as follows: first attack the
  \(Z_0\)-dual majorant / \(P_\theta\)-alternation theorem; in parallel compute
  the finite no-atom collinearity test \(b_S=\Lambda\rho_S\) and
  \(b_\Pi-\Lambda\rho_\Pi\); use a numerical margin oracle only with the
  repaired moving-chart columns \(H_\gamma^{\rm rep}\); attempt an explicit
  signed product formula only if it includes the moving correction columns and
  \(Z_0\)-contact rows; reserve \(Q_{\rm eff}\) for no-atom/off-cut finite
  subcases, since nonzero \(Z_0\)-atoms have positive point-row blow-up.
- the existing two-interval diagnostic scripts are not Gate 1 oracles: they do
  not output \(H_\gamma^{\rm rep}\), \(AX_\gamma=-r_\gamma\), \(V_S,\rho_S,b_S\).
  A proof-grade oracle must first extract this repaired moving-Schiffer data;
  then it may certify \(G_\theta\ge0\) on \(Z_0\) and the strict affine /
  homogeneous residual margins by interval sign tables for
  \(P_\theta/(Q^2R)\).  This certified oracle would prove
  `MovingSchifferMajorantSignTheorem`; failed denominator/contact/chart boxes
  route to Gate 3.
- `RepairedSchifferDataExtractorSoundness` now fixes the oracle input: solve
  \(AX_\gamma=-r_\gamma\) with
  \(B(\Delta P,\Delta Q)=QD\,\Delta P-PD\,\Delta Q\) and
  \(h_\gamma^{raw}=-\frac12PQD_\gamma\), then set
  \(H_\gamma^{rep}=h_\gamma^{raw}-BA^{-1}r_\gamma\),
  \(C_\gamma=H_\gamma^{rep}/(Q^2R)\),
  \(\rho_\gamma=-C_\gamma(c)\), and
  \(b_\gamma=aV_\gamma(u)+bV_\gamma(v)\).  The extractor proves the repaired
  columns satisfy the moving-chart rows; it still leaves the
  \(P_\theta\)-majorant sign theorem as the active hard mouth.
- `FiniteContactMajorantReduction` now reduces that hard mouth to finite
  contact patterns: at most four contacts for finite affine \(\Lambda\), at
  most five for the homogeneous/projective circuit, with equations
  \(G_\theta(x_i)=0\), interior stationarity \(P_\theta(x_i)=0\), a sign table
  for \(P_\theta/(Q^2R)\) between contacts, and the strict residual check.
  Contact collisions, endpoint/pole hits, or denominator sign loss route to
  Gate 3.
- `ContactPatternVerification` is now the concrete Gate 1 workload: enumerate
  contacts on \(Z_L\cup Z_R\) by endpoint/interior type, solve the finite
  \(G=0\), \(P=0\) contact systems, certify the interval sign table for
  \(P_\theta/(Q^2R)\), verify the KKT cone compatibility
  \(\sum_iw_iV_S(z_i)=-b_S+\Lambda\rho_S\) in the affine branch and
  \(\sum_iw_iV_S(z_i)=\lambda\rho_S\) in the homogeneous branch, and prove the
  affine or homogeneous residual is strict.  No solution is harmless;
  degeneration routes to Gate 3; a regular non-strict residual is a real Gate
  1 obstruction.
- The failure side has also been normalized: any regular Gate 1 failure now
  yields a finite weighted contact obstruction with contacts \(z_i\), positive
  weights \(w_i\), KKT cone equation, interior stationarity
  \(P_\theta(z_i)=0\), an interval sign table certifying \(G_\theta\ge0\), and
  a bad residual.  Thus the next proof task is to exclude these weighted
  systems pattern-by-pattern; otherwise a regular solution is a genuine
  rank-defect obstruction.
- Review audit: the affine four-contact residual has the exact Schur formula
  \[
  L_\Lambda(\theta_{\mathfrak p})
  =
  -\frac{\det\begin{pmatrix}
  E_{\mathfrak p}&v_{\Pi,\mathfrak p}\\
  b_S^T-\Lambda\rho_S^T&b_\Pi-\Lambda\rho_\Pi
  \end{pmatrix}}{\det E_{\mathfrak p}}.
  \]
  This verifies the determinant reduction for a fixed pattern.  It also shows
  why a fixed-pattern sign proof cannot cover all \(\Lambda\): the numerator
  is \(D_b-\Lambda D_\rho\).  The correct Gate 1 order is therefore to prove
  homogeneous margin witnesses \(G^{(c)}<0\) and \(G^{(c)}>0\), use them to
  compactify the affine \(\Lambda\)-axis, and then run contact-pattern
  verification on that compact range.  The still-missing theorem is the
  repaired-column envelope/ECT sign theorem, not a rank or quotient statement.
- Review audit: the homogeneous margins now have a sharper conditional target.
  Let
  \(\mathcal K_Z=\{\chi:\chi\cdot V_S(x)\ge0\ (x\in Z_0)\}\).  If
  \(\mathcal D_Z\ne\emptyset\) and \(\mathcal K_Z\) contains directions with
  positive and negative \(\rho_S\)-pairing, then adding large multiples of
  those directions to any majorant gives
  \(\sup_{\mathcal D_Z}G^{(c)}>0\) and \(\inf_{\mathcal D_Z}G^{(c)}<0\).  By
  separation this follows from
  \[
  \pm\rho_S\notin\operatorname{cone}\{V_S(x):x\in Z_0\},
  \]
  while \(\mathcal D_Z\ne\emptyset\) is exactly the no-positive-lift-recession
  condition
  \[
  \sum_iw_iV_S(x_i)=0,\quad w_i>0
  \Longrightarrow
  \sum_iw_iV_\Pi(x_i)\le0.
  \]
  Conic Carathéodory reduces the endpoint cone separation to at most four
  atoms; alternating cofactors with the off-row \(\rho_S\) would make the
  Cramer weights alternate and rule out positive representations.  This is a
  correct proof bridge, but it is conditional: the required off-row
  alternation and lifted circuit sign still require a row-by-row
  `RepairedCauchySignRegularity / ChartCompatibility` theorem for the actual
  repaired moving-Schiffer columns.  The proposed Cauchy/Andreief integration
  argument is only a sufficient route after the component order, integration
  basepoint, \(Q^2R\) signs, \(c,u,v\) row positions, and moving-Q/period rows
  have all been identified as one compatible ordered Cauchy/confluent system.
- Conditional proof bridge now recorded: if the repaired Cauchy columns
  \(C_j=H_j^{rep}/(Q^2R)\) are already one compatible sign-regular ordered
  Cauchy/confluent block, then the potential rows
  \(V_j(x)=\int_x^{x_*}C_j(t)\,dt\) inherit determinant signs by the
  total-positivity of the ordered step kernel and Cauchy-Binet/Andreief.  A
  mixed determinant with one evaluation row \(\rho_j=-C_j(c)\) gives the
  off-row alternating cofactors, hence endpoint cone separation.  If the same
  five-column orientation gives nonpositive \(V_\Pi\)-lift on positive
  circuits, then the homogeneous margins follow and the affine \(\Lambda\)
  parameter is compactified.  This still leaves the actual
  `RepairedCauchySignRegularity / ChartCompatibility` proof and compact
  affine boundary-row pencil verification; it is not a Gate 1 PASS.
- The positive-lift recession check is now finite and determinant-level: for
  five regular points \(x_i\), the circuit of the four endpoint rows is given
  by cofactors
  \(a_i=(-1)^i\det[V_S(x_1)\cdots\widehat{V_S(x_i)}\cdots V_S(x_5)]\), and its
  lift is, up to the fixed orientation sign,
  \[
  \sum_i a_iV_\Pi(x_i)
  =
  \pm\det\begin{pmatrix}
  V_S(x_1)&\cdots&V_S(x_5)\\
  V_\Pi(x_1)&\cdots&V_\Pi(x_5)
  \end{pmatrix}.
  \]
  Thus no-positive-lift recession is exactly a five-column orientation check:
  any circuit whose endpoint cofactors can be oriented positive must have
  nonpositive period lift, with vanishing cofactors routed to Gate 3.
- ECT-A homogeneous closure is now isolated.  If the actual repaired columns
  satisfy (i) endpoint/off-row cofactor alternation for \(\rho_S\), and
  (ii) the five-point lifted circuit orientation excluding positive
  \(V_\Pi\)-lift, then no-positive-lift recession holds,
  \(\mathcal D_Z\ne\emptyset\), \(\pm\rho_S\) are outside the endpoint cone,
  the two homogeneous margins hold, and the affine \(\Lambda\)-axis is compact.
  This is only the homogeneous closure; compact affine contact patterns and the
  boundary row pencil \(b-\Lambda\rho\) remain to be verified.
- After ECT-A, the compact affine target is now a finite pattern-minimum
  problem.  For each regular affine pattern \(\mathfrak p\), define
  \(\mathcal S_{\mathfrak p}\) by the contact equations, interior
  \(P_\theta=0\) equations, endpoint one-sided signs, interval sign table, and
  KKT equation
  \(\sum_iw_iV_S(z_i)=-b_S+\Lambda\rho_S\) with
  \(\Lambda\in[\Lambda_-,\Lambda_+]\).  The required check is
  \[
  m_{\mathfrak p}:=\inf_{\mathcal S_{\mathfrak p}}
  (G_\theta^{(b)}-\Lambda G_\theta^{(c)})>0.
  \]
  Empty patterns are harmless; boundary infima route to Gate 3; a regular
  nonpositive minimizer is exactly a Gate 1 weighted affine obstruction.
- Most likely next route: prove repaired-column ECT-A first, namely
  endpoint/off-row alternation plus five-point lifted circuit orientation for
  the actual \(H_\gamma^{rep}\) data.  This closes the homogeneous branch and
  compactifies \(\Lambda\).  Then verify the compact affine pattern minima
  \(m_{\mathfrak p}>0\) using a repaired-data contact oracle or an explicit
  determinant product.  Keep \(Q_{\rm eff}\) as a fallback for compact affine
  hard cases, not as the first attack on nonzero \(Z_0\)-atomic homogeneous
  loads.
- ECT-A is now reduced to full moving-block Schur minors.  Endpoint/off-row
  alternation requires signing the four-column full block with row blocks
  \(L_X\) and \(L_{X;i\to c}\); the lifted circuit orientation requires signing
  the five-column full block with the period column \(\kappa Q^2\).  Since
  \(\det A>0\), both signs are exactly signs of the corresponding full moving
  determinants.  The next concrete theorem is
  `ECTAFullMovingBlockSignLemma`: expand those four- and five-column full
  determinants as positive factors times ordered Cauchy/Vandermonde products,
  with zero determinants routed to Gate 3.
- The immediate checklist for that lemma is: fix an explicit ordered moving
  correction basis \(B_\nu=QD\Delta P_\nu-PD\Delta Q_\nu\); sign \(\det A\);
  sign the ordered \(L_X,L_{X;i\to c},L_Y\) row factors; sign the raw endpoint
  columns \(H_\gamma^{raw}=-\frac12PQD_\gamma\); sign the period lift
  \(\kappa Q^2\); and track the component signs of \(Q^2R\).  Any failure of
  these regular sign conventions routes to Gate 3 or becomes a real
  obstruction.
- The moving-correction basis can now be normalized.  Since
  \(QD\Delta P-PD\Delta Q=D\mathbb R[z]_{\le2d-3}\) in the regular monic
  \(Q\)-chart, ECTAFullMovingBlockSignLemma may use the canonical ordered
  columns \(B_m^{can}=Dz^m\), \(0\le m\le2d-3\).  The actual chart basis differs
  by an invertible change of basis whose determinant is absorbed into the
  \(\det A>0\) orientation convention.  The next determinant product is
  therefore the bordered interpolation determinant for
  \(Dz^m\), the raw endpoint columns \(-\frac12PQD_\gamma\), and the period
  column \(\kappa Q^2\) against the ordered \(A,L_X,L_{X;i\to c},L_Y\) rows.
- Correction: the five-column first-order full block is singular.  The period
  interpolation identity \(Q^2=DW_Q+\sum_\gamma
  Q(\gamma)/(P(\gamma)D_\gamma(\gamma))\,PQD_\gamma\) puts the period column in
  the span of the canonical correction columns and endpoint columns.  Hence
  the determinant corresponding to (G1ECTASchur5) cannot give strict lifted
  circuit orientation.  The full-block determinant route remains plausible
  only for the four-column endpoint/off-row alternation.  The lifted
  positive-circuit negativity must instead come from a direct majorant/envelope
  construction or a second-variation/effective Hessian input; it cannot come
  from the naive first-order five-column determinant.
- Computation has started with the required repaired-data object.  The new
  script `1038/gate1_repaired_data_extractor.py` implements the canonical
  extractor \(B_m=Dz^m\), \(A_{row,m}=row(B_m)\),
  \(r_\gamma=row(-\frac12PQD_\gamma)\), solves \(AX_\gamma=-r_\gamma\), and
  returns \(H_\gamma^{rep}\).  A synthetic regular \(g=2\) smoke test gives
  \(\det A=5.394710695371\cdot10^7\), \(\kappa(A)=6.851468981911\cdot10^2\),
  \(\max|AX+r|=6.821210263297\cdot10^{-13}\), and max repaired row residual
  \(7.691625114603\cdot10^{-13}\).  This verifies the extractor algebra only;
  it is not a Gate 1 certificate.  The next computation needs actual compact
  \(g=2\) chart input \((P,Q,D,\Gamma,\ell)\), because the existing
  `solve_two_interval_finite_gap.py` is still a local branch diagnostic and
  does not output the repaired Gate 1 data.
- The extractor now has `--audit-two-interval-json`.  Auditing
  `two_interval_branch_certificate_skeleton.json`,
  `two_interval_branch_certificate_top_split.json`,
  `two_interval_small_eta_certificate.json`, and
  `two_interval_tiny_eta_certificate.json` gives `gate1_ready = False` for
  all four.  They encode the old local ansatz
  \(F=(z+A)\sqrt{(z-\alpha)(z-\beta)}/((z-\ell)(z-r)(z-1))\), so they supply
  at most \(P=z+A\), \(Q=(z-\ell)(z-r)(z-1)\), and one moving cut
  \([\alpha,\beta]\).  They do not contain the required compact non-pinched
  \(g=2\) data \(\Gamma=\{\alpha_1,\beta_1,\alpha_2,\beta_2\}\),
  moving-chart rows \(\ell\), period orientation \(\kappa\), or
  \(Z_0,u,c,v\).  Therefore they cannot be wrapped into a Gate 1 repaired
  oracle input.
- The proof-grade computation entry point is now `--chart-json PATH`, with
  required fields `P,Q,gammas,rows` and optional fields
  `kappa,Z0,u,c,v,contact_points`.  Besides repaired extraction, it checks the
  period endpoint-quotient identity
  \(Q^2=DW_Q+\sum_\gamma
  Q(\gamma)(P(\gamma)D_\gamma(\gamma))^{-1}PQD_\gamma\).  A synthetic chart
  JSON smoke test gives \(\max|AX+r|=3.410605131648\cdot10^{-13}\), max repaired
  row residual \(3.845812557302\cdot10^{-13}\), and period-quotient remainder
  \(5.329070518201\cdot10^{-15}\).  Thus the remaining computational blocker
  is now specifically the absence of a real compact non-pinched \(g=2\) chart
  file, not extractor infrastructure.
- If the chart JSON includes an off-cut anchor `c`, the entry point now also
  computes \(\rho_\gamma=-H_\gamma^{rep}(c)/(Q(c)^2R(c))\) using the real
  branch \(R(z)\sim z^2\).  A synthetic anchor test at \(c=-0.4\) gives
  \(R(c)=-2.087103255711\) and \(\max_\gamma|\rho_\gamma|=2.992534365488\).
  It intentionally does not invent \(V_S,b_S\); those require the cut-density
  logarithmic potential normalization.
- The first potential layer is now implemented only on the right exterior
  component.  For \(s>\beta_2\), the extractor computes
  \(V_j(s)=\int_s^\infty C_j(y)\,dy\) by Gauss-Legendre quadrature after
  \(y=s+t/(1-t)\).  A synthetic chart with \(u=2.2,v=3.0\), two right-exterior
  contact points, \(a=0.4,b=0.6,\kappa=1\) computes four right-exterior rows,
  skips none, and gives \(\max_j|b_j|=7.071555885807\cdot10^2\).  Middle-gap
  and left-exterior potential rows are still intentionally uncomputed until
  their boundary-value convention is fixed.
- The right-exterior path now also computes the first off-row determinant
  smoke test.  With four synthetic right-exterior contacts
  \(2.02,2.2,2.5,3.0\), it forms \(E=(V_S(x_i)^T)\), replaces each row by
  \(\rho_S^T\), and reports \(\det E=-3.344745723982\cdot10^1\) with relative
  cofactor signs \((- ,+,-,+)\).  This confirms the executable can test the
  endpoint/off-row alternation hard mouth once real chart data are supplied;
  it is not a Gate 1 certificate.
- The right-exterior off-row checker now also supports grid scans.  On the
  synthetic chart, an \(N=8\) grid from \(2.02\) to \(4.0\) checks all \(70\)
  four-tuples and finds only \(15\) alternating tuples, with no singular
  \(\det E\).  The first nonalternating tuple is approximately
  \((2.02,2.302857142857143,2.585714285714286,2.8685714285714283)\), with
  relative signs \((- ,+,+,-)\).  This shows why single four-point smoke tests
  are not evidence for Gate 1; the real chart must pass a grid/envelope scan
  before any interval proof attempt.
- The same grid scan now records sign-pattern frequencies and determinant
  floors.  On the synthetic grid the patterns are \((-,-,+,-)\) with count
  \(40\), \((-,+,+,-)\) with count \(15\), and \((+,-,+,-)\) with count \(15\).
  The smallest \(|\det E|\) tuple is at
  \((3.1514285714285712,3.434285714285714,3.717142857142857,4.0)\) with
  \(\det E=3.872350669859211\cdot10^{-8}\), while the first nonalternating
  tuple has \(\det E=0.6096211894375172\).  Thus that synthetic failure is not
  just a near-singular determinant artifact.
- The extractor now has `--scan-jsons ROOT`, which verifies whether a
  proof-grade Gate 1 chart input is actually present.  Scanning `1038/` finds
  7 JSON files, with counts `{other_json: 3, old_two_interval_diagnostic: 4}`
  and `gate1 chart ready = 0`.  Scanning the full repository finds 130 JSON
  files, with counts `{other_json: 122, json_non_object: 2, unreadable_json: 2,
  old_two_interval_diagnostic: 4}` and again `gate1 chart ready = 0`.  Thus the
  current computational blocker is verified: the repository contains no compact
  non-pinched \(g=2\) chart JSON with `P,Q,gammas,rows`.  The next numerical
  step must derive or supply that chart; continuing to run the old branch JSONs
  would compute the wrong object.
- A follow-up chart-generation audit found no hidden concrete
  \(\alpha_1,\beta_1,\alpha_2,\beta_2\) or compact \(g=2\) \(P,Q\) candidate
  in the current 1038 materials.  The concrete numbers present are still the
  one-cut / old two-interval constants such as
  \(x_L=-1.8081073680988165\), \(x_R=0.02632310766384517\), and the old
  \(P=z+1.2627187696571671\), \(Q=(z-\ell)(z-r)(z-1)\) ansatz.  The compact
  neck equations specify local variables \(y=(q,a,b,c)\) in an external field
  \(W\), but do not yet generate the global chart data
  `P,Q,gammas,rows,kappa,Z0,u,c,v`.  The next executable target is therefore a
  compact \(g=2\) finite-gap chart-equation solver, not another pass over the
  old JSONs.
- The fixed-\(Q\) Hermite endpoint table should not be used as that solver
  target: the ledger already proves its collapse
  \(H_{\alpha_1}=H_{\beta_1}=H_{\alpha_2}=H_{\beta_2}
  =-\frac12\operatorname{lc}(P)Q^2\), so all endpoint columns are proportional
  to the period column.  The solver must instead define the full moving
  Schiffer chart.  The minimal missing definition is now named
  `CompactG2MovingChartEquations`: it must specify the unknown vector,
  equation vector, period/filling convention, and ordered row list `ell`, with
  output exactly `P,Q,gammas,rows,kappa,Z0,u,c,v`.
- A row-count audit found a sharper obstruction inside that target.  The
  proposed canonical correction image \(D\mathbb R[z]_{\le2d-3}\) has dimension
  \(2d-2\), but the simultaneously described pole-state rows
  \(H(p_k),H'(p_k)\) already give \(2d\) rows, or \(2d+1\) with zero mass.  For
  cubic \(Q\), this is 4 correction columns versus 6 or 7 rows.  Hence the
  square moving-chart matrix \(A_{\ell,X}\) is not yet defined.  The next proof
  step must decide which rows are equations, which are state outputs/quotient
  rows, or whether the correction image must be enlarged.
- The monic \(Q\)-chart rules out a harmless enlargement: the map
  \((\Delta P,\Delta Q)\mapsto Q\Delta P-P\Delta Q\) is already an isomorphism
  onto \(\mathbb R[z]_{\le2d-3}\), so the moving correction image really has
  dimension \(2d-2\).  The compatible repair is to prove a
  `SquareMovingChartGaugeLemma`: choose exactly \(2d-2\) independent rows for
  \(A\), and show every omitted pole/residue/period condition is a state
  output, quotient direction, or open regularity inequality routed to Gate 3.
- The square-gauge lemma must be sign-compatible, not merely algebraic.  The
  earlier normalization construction allows an arbitrary basis of
  \(\operatorname{im}\mathcal N\), but arbitrary row compression destroys the
  ordered Cauchy determinant signs.  The next target is therefore
  `TPSquareMovingChartGaugeLemma`: choose exactly \(2d-2\) rows that both span
  the normalization image and remain ordered Cauchy / confluent Cauchy /
  positive-average rows with fixed orientation.
- The extractor now has `--audit-pole-row-subsets` to enumerate square
  subgauges from the overcomplete pole eval/deriv row list.  On the synthetic
  cubic \(Q\) chart there are 6 pole rows, 4 correction columns, and all
  \(\binom64=15\) square subsets are full rank, with determinant magnitudes
  from \(7.019243915694513\cdot10^5\) to
  \(5.104535926940518\cdot10^8\).  This is only a rank/gauge diagnostic, but
  it gives the next computational handle for `TPSquareMovingChartGaugeLemma`.
- The same audit now records orientation signs.  In the synthetic cubic smoke
  chart, the 15 full-rank pole-row subgauges split as 11 positive determinants
  and 4 negative determinants; even the repeated row-kind pattern `E,D,E,D`
  has both signs.  This confirms the important methodological point: full rank
  is not a TP-compatible gauge criterion.  `TPSquareMovingChartGaugeLemma` must
  choose a canonical ordered row subset, or prove a sign normalization for the
  relevant Schur minors; arbitrary full-rank row selection is not proof-grade.
- A sharper toy clue is positive: among the square subgauges made of complete
  confluent pole pairs `H(p_i), H'(p_i)` while omitting one full pole pair,
  all 3 cubic candidates have the same determinant sign.  The most likely
  next gauge target is therefore a full-pair
  `TPSquareMovingChartGaugeLemma`: select \(d-1\) complete confluent pole
  pairs from the \(d\) real \(Q\)-poles, then prove one omitted-pair choice is
  regular and its full augmented Schur minors are ordered-Cauchy compatible.
- The \(A\)-matrix determinant for this full-pair gauge is now explicit.  For
  selected poles \(p_{i_1}<\cdots<p_{i_n}\), \(n=d-1\),
  \[
  \det A_{\rm pair}
  =
  \prod_r D(p_{i_r})^2
  \prod_{r<s}(p_{i_s}-p_{i_r})^4>0.
  \]
  This follows by subtracting \((D'(p)/D(p))\) times each evaluation row from
  its derivative row and reducing to the confluent Vandermonde determinant.
  The extractor checks this identity on the toy cubic chart to relative error
  \(3.12\cdot10^{-15}\).  The remaining Gate 1 gauge task is therefore not
  \(\det A\), but the augmented Schur-minor signs after endpoint/period/contact
  rows are appended.
- The full-pair gauge also gives an explicit repaired endpoint formula.  If
  \(M(z)\) is the selected pole factor, then
  \[
  H_\gamma^{\rm rep}(z)
  =
  -\frac12
  \frac{P(\gamma)Q(\gamma)}{M(\gamma)^2}
  M(z)^2D_\gamma(z).
  \]
  The proof is Hermite/interpolation: the repaired column has double zeros at
  the selected poles and agrees with the raw endpoint column modulo
  \(D\mathbb R[z]_{\le2d-3}\), so endpoint interpolation fixes it.  The toy
  audit verifies this formula to relative error \(1.09\cdot10^{-14}\).
  Consequently
  \[
  C_\gamma^{\rm rep}(z)
  =
  -\frac12
  \frac{P(\gamma)Q(\gamma)}{M(\gamma)^2}
  \frac{D_\gamma(z)}{N(z)^2R(z)},\quad Q=MN.
  \]
  This turns the repaired-column sign problem into an explicit omitted-pole
  Cauchy-kernel problem.
- In the toy cubic chart, the constants
  \(-\frac12P(\gamma)Q(\gamma)/M(\gamma)^2\) are positive for every endpoint
  and every omitted-pole choice.  The actual chart must prove the endpoint sign
  convention \(-P(\gamma)Q(\gamma)>0\).  Under that convention, the endpoint
  columns differ only by positive scalings from
  \(D_\gamma(z)/(N(z)^2R(z))\).  The next proof target is therefore the narrower
  `WeightedCubicAntiderivativeECTLemma` for potentials
  \[
  \int_s^\infty \frac{D_\gamma(t)}{N(t)^2R(t)}\,dt.
  \]
- The right-exterior part of this weighted-cubic ECT is already formal: for
  \(G_F(s)=\int_s^\infty F(t)/(N(t)^2R(t))\,dt\) with \(F\) cubic,
  \(G_F'\) has at most three zeros and \(G_F(\infty)=0\).  Four right-exterior
  zeros would force at least four derivative zeros, contradiction.  The
  remaining hard part is the split-set/global contact accounting and off-row
  determinant signs, not the right-exterior component alone.
- Important correction: this Rolle argument does not prove ECT on the actual
  split set \(Z_0=[\alpha_1,\beta_1]\cup[\alpha_2,\beta_2]\).  Four zeros can
  split \(2+2\) across the two components and force only two derivative zeros.
  A bare model \(G(x)=(x+2)(x+1)(x-1)(x-2)\) already has two zeros on each of
  two disjoint intervals while \(G'\) is cubic.  The remaining missing input is
  a cross-component constraint: period/normalization linkage, off-row
  determinant orientation, or a genuine two-interval total-positivity theorem
  for the kernel \(1/(N^2R)\).
- Therefore the next lemma should not be a bare two-interval cubic
  antiderivative ECT theorem; that statement is false without extra finite-gap
  connection data.  The sharper target is `SplitConnectionSignLemma`: prove
  that a \(2+2\) contact pattern across the two \(Z_0\) components contradicts
  the actual Gate 1 connection row, period/filling normalization, or off-row
  determinant orientation.  This is the only contact distribution not killed
  by the one-component Rolle count.
- The old diagnostic solver reinforces the same structure: its
  `potential_difference_by_F` row links contact values by atom logarithms plus
  an integral of the Cauchy-transform remainder, rather than allowing
  independent interval primitives.  For the full-pair Gate 1 kernel, the next
  concrete target is the signed connection integral
  \[
  \int_{x_2}^{x_3}\frac{F(t)}{N(t)^2R(t)}\,dt
  \]
  under the constraints that the within-component integrals over
  \([x_1,x_2]\) and \([x_3,x_4]\) vanish.  Proving this sign fixed and nonzero
  would close the \(2+2\) contact obstruction.
- Contact counting narrows this further.  Gate 1 contacts are contacts of a
  nonnegative majorant.  Every interior contact forces \(G'=0\), hence the
  cubic numerator \(F\) vanishes there.  Four interior contacts are therefore
  impossible.  The only split patterns not killed by the cubic degree are
  endpoint-heavy \(2+2\) patterns with one-sided derivative signs.  The next
  sign lemma should be stated for those endpoint-heavy contact patterns, not
  for arbitrary four interior contacts.
- The surviving \(2+2\) types are only
  \[
  (LR,LR),\quad (LR,LI),\quad (LR,IR),\quad (LI,LR),\quad (IR,LR),
  \]
  where \(L,R\) are component endpoints and \(I\) is an interior contact.  All
  other \(2+2\) patterns force at least four derivative zeros and are excluded
  by the cubic numerator except for Gate 3 degeneracy.  The next computation is
  the one-sided endpoint derivative plus connection-integral sign check for
  these five patterns.
- A bare quartic primitive check on model intervals \([-2,-1]\cup[1,2]\)
  shows these survivor contact sets are not automatically feasible: the
  interpolating quartics are negative somewhere on the components.  So the
  immediate finite check is even sharper: for each of the five survivor types,
  first test inward endpoint derivative signs and component nonnegativity; only
  patterns surviving that test need the split-connection integral.
- The extractor now has `--audit-endpoint-heavy-patterns` for this bare model.
  It reports that none of the five survivor types is sampled-nonnegative, and
  none satisfies all inward endpoint derivative signs.  This is diagnostic, not
  a Gate 1 proof.  The next proof target is the stronger
  `EndpointHeavyInwardSignLemma`: for the full-pair kernel \(1/(N^2R)\), no
  nonzero cubic numerator can realize those five endpoint-heavy contact
  patterns with the required one-sided inward signs.  Only if this fails should
  the split-connection integral be used.
- Root-budget refinement: \(LR\) on a component forces one numerator root;
  \(LI\) or \(IR\) forces two.  Thus \((LR,LR)\) forces two roots, while the
  four mixed survivor types force all three roots of the cubic.  The mixed
  types should next be attacked by root-order/inward-sign compatibility; only
  \((LR,LR)\) still has a free third root and likely needs the connection row.
- A symbolic sign automaton shows inward endpoint signs alone do not kill all
  survivor types.  For each possible component multiplier sign
  \(G'=\sigma_\nu F\), some endpoint-heavy cubic root orders remain feasible.
  Therefore the standalone `EndpointHeavyInwardSignLemma` is too strong.  The
  correct next target is `EndpointHeavyConnectionSignLemma`: combine the
  surviving inward-sign/root-order cases with the cross-component connection
  integral or off-row determinant orientation.
- The extractor now has `--audit-endpoint-heavy-connection`.  This is
  diagnostic only: it uses the normalized full-pair omitted-pole kernel
  \(F(x)/((x-p)^2R(x))\,dx\), solves the two within-component contact integral
  equations, and then reports the middle-gap connection sign.  On the
  symmetric model \(\Gamma=(-2,-1,1,2)\), \(p=0\), the four mixed survivors
  have stable signs in the sampled solves:
  \[
  (LR,LI),(LR,IR): -,\qquad (LI,LR),(IR,LR): +.
  \]
  But \((LR,LR)\) gives both signs.  Therefore a single fixed connection-sign
  lemma for all five survivor types is false even as a diagnostic statement.
  The next proof should split: prove the four mixed connection signs first,
  and handle \((LR,LR)\) with its extra free third root via a separate
  residual/off-row condition.
- The connection oracle now rejects omitted poles on the cuts and in the
  middle connection gap.  A pole on a cut makes the density singular; a pole in
  \((\beta_1,\alpha_2)\) lies on the connection path as a double pole, so the
  ordinary connection integral is not finite.  The new
  `--sweep-endpoint-heavy-connection` command sweeps six valid exterior
  omitted-pole models.  Aggregate solved signs:
  \[
  (LR,LI),(LR,IR):\ 29(-),\qquad
  (LI,LR),(IR,LR):\ 29(+),
  \]
  while \((LR,LR)\) remains mixed, \(15(-),15(+)\).  Thus the most plausible
  next theorem is the four-pattern mixed connection sign theorem, not a
  five-pattern theorem.
- The new `--continue-mixed-connection` command parameterizes each mixed
  pattern by its unique interior contact, solves the two component zero-
  integral equations for the remaining roots, and scans the whole continuation
  branch.  For \(\Gamma=(-2,-1,1,2),p=-3\), 40/40 samples solve in all four
  patterns with ranges
  \[
  (LR,LI):[-0.891,-0.483],\quad
  (LR,IR):[-1.350,-0.709],
  \]
  \[
  (LI,LR):[0.334,0.894],\quad
  (IR,LR):[0.185,0.521].
  \]
  A non-symmetric exterior-pole model \(\Gamma=(-3,-1.2,0.7,2.5),p=3.5\)
  gives the same signs.  The next proof target is therefore a
  `MixedConnectionMonotoneSignLemma`: along the one-parameter mixed branch,
  the connection integral cannot cross zero except through a Gate 3
  degeneration.
- The new `--audit-mixed-zero-connection` command attacks that crossing
  directly.  It solves the three equations
  \[
  I_L=0,\qquad I_R=0,\qquad I_{\rm gap}=0
  \]
  for the mixed contact/root parameters.  In both tested exterior-pole models
  it finds no regular zero-connection solution.  Best attempts retain the
  expected connection signs; some are driven to the ordering boundary.  The
  next paper lemma should be `MixedZeroConnectionNoInteriorLemma`: the
  three-integral zero system has no regular interior mixed solution, so any
  sign crossing routes to Gate 3.
- The new `--audit-mixed-kernel-roots` command linearizes the same obstruction.
  For fixed mixed interior contact \(y\), the three functionals
  \(I_L,I_R,I_{\rm gap}\) form a \(3\times4\) matrix on cubic coefficients.
  Its one-dimensional kernel cubic would have to have the mixed root order for
  a zero-connection crossing.  In both tested exterior-pole models, 40/40
  sampled \(y\)-values in all four mixed patterns fail this root-order test.
  The sharper paper target is `MixedKernelRootOrderLemma`: the kernel cubic
  of this \(3\times4\) matrix always has the wrong root order, except at Gate
  3 degeneracy.
- The kernel-root audit now also evaluates \(F_y(y)\).  In both tested
  exterior-pole models its sign is fixed:
  \[
  (LR,LI),(LI,LR):F_y(y)>0,\qquad
  (LR,IR),(IR,LR):F_y(y)<0.
  \]
  The sampled kernel roots always split as left-cut / middle-gap / right-cut.
  Thus the paper lemma can be sharpened: the zero-connection kernel cubic never
  has the prescribed interior-contact root \(y\).
- The same check is now determinant-form: append the evaluation row
  \(F\mapsto F(y)\) to the three rows \(I_L,I_R,I_{\rm gap}\), giving a
  \(4\times4\) matrix \(\mathcal A_y\) on \(1,x,x^2,x^3\).  The determinant
  has the same fixed signs as \(F_y(y)\) in both tested exterior-pole models.
  The next proof target is `MixedAugmentedDeterminantSignLemma`: prove the
  sign of \(\det\mathcal A_y\) for all regular mixed \(y\).
- `MixedAugmentedDeterminantSignLemma` is now proved for the full-pair
  exterior-pole kernel.  Andreief expansion writes \(\det\mathcal A_y\) as a
  product-domain integral of \(w_Cw_Cw_G\) times a Vandermonde determinant.
  The cut weights are positive, the middle-gap weight is negative, and the
  row order is fixed in each mixed pattern.  This gives
  \[
  (LR,LI),(LI,LR):\det\mathcal A_y>0,\qquad
  (LR,IR),(IR,LR):\det\mathcal A_y<0.
  \]
  Hence \(F_y(y)\ne0\), so a regular mixed zero-connection crossing is
  impossible; the four mixed endpoint-heavy survivor patterns are excluded
  modulo Gate 3 routing.
- The remaining endpoint-heavy pattern is \((LR,LR)\).  The new
  `--audit-lrlr-kernel` command forms the two component-integral rows on
  cubics and samples their two-dimensional kernel.  In both tested
  exterior-pole models, connection signs are split even among samples with
  valid LRLR root order.  Therefore LRLR cannot be excluded by component
  zero-integrals plus root order alone.  It needs an additional actual Gate 1
  row: residual, off-row, or KKT compatibility.  The next proof target is
  `LRLRResidualOffRowLemma`.
- The LRLR audit now also records the free third root and projective products
  \(I_{\rm gap}(F)L(F)\), because \(F\) and \(-F\) represent the same zero
  pattern.  With
  `--audit-lrlr-kernel --connection-samples 128 --connection-nodes 80`, the
  LRLR-order samples still split \(57(+),57(-)\), and the middle-gap free-root
  subbranch itself splits \(34(+),34(-)\).  Thus the remaining row cannot be a
  generic root-location or point-probe argument; it must use the actual
  homogeneous \(\rho\)-row or affine \(b-\Lambda\rho\) residual/KKT row from the
  moving-Schiffer chart.
- A current scan with `gate1_repaired_data_extractor.py --scan-jsons 1038`
  still reports `gate1 chart ready = 0`; the repository contains old
  two-interval diagnostic JSONs but no chart-ready input with
  \(P,Q,\Gamma\), moving-chart rows, and anchor/boundary data.  Therefore the
  next computation must first produce or import that chart-ready JSON before
  any LRLR residual-margin claim can be proof-grade.
- The extractor already supports that input through `--chart-json`.  The
  required minimal schema is \(P,Q,\Gamma\), the moving-chart rows
  \(\ell_r\), plus \(c\) for \(\rho_S\), and \(u,v,a,b,\kappa\) for the affine
  \(b-\Lambda\rho\) row.  Once such a file exists, the next run should compute
  \(H_\gamma^{rep}\), \(AX_\gamma+r_\gamma\), \(\rho_S,b_S,\rho_\Pi,b_\Pi\),
  and then test `LRLRResidualOffRowLemma` directly.
- The chart interface now also accepts
  `{"row_gauge":{"kind":"full_pair_pole_gauge","omit_q_pole_index":i}}`,
  which expands to all complete confluent \(Q\)-pole pairs except the omitted
  pair.  It rejects files that provide both `rows` and `row_gauge`.
- New command:
  `--chart-json PATH --audit-lrlr-residual-offrow`.  For a full-pair chart
  with anchor \(c\), it computes the LRLR projective sign
  \(I_{\rm gap}(F)F(c)/(N(c)^2R(c))\).  A synthetic chart smoke test runs
  end-to-end and gives split signs \(52(+),6(-)\) among \(58\) LRLR-order
  samples, so the command is diagnostic rather than result-forcing.  A real
  compact \(g=2\) chart is still needed before the LRLR row claim is
  proof-grade.
- The same LRLR audit now sweeps the affine row
  \(I_{\rm gap}(F)(L_b(F)-\Lambda L_\rho(F))\) when \(u,v,a,b\) are present
  and \(u,v\) lie in the right exterior.  The synthetic chart smoke sweep over
  \(\Lambda\in[-5,5]\) found no fixed nonzero sign, which is only a pipeline
  check.  The proof-grade next step is still to produce the compact \(g=2\)
  chart JSON and run the same rho/affine LRLR audit on that chart.
- A fresh old-solver JSON at \(\epsilon=0.01\) was audited again and is still
  not promotable: it has a one-cut ansatz \(P,Q,[\alpha,\beta]\), but lacks
  compact non-pinched \(\Gamma\), moving chart rows, \(\kappa\), and
  \(Z_0,u,c,v\).  Therefore the next route is not conversion of old
  diagnostics; it is `CompactG2MovingChartEquations` plus a true chart-ready
  JSON.

## 7. Update Discipline and Pure Mathematical Next Steps

Every future update should first update the detailed ledger
`1038_dual_two_interval_progress.md`, then continue the proof.  The update
should say which priority was attacked, which formula changed, what worked,
what failed, and why.

The exact-value target is the lower bound

\[
L_-\ge M_{\rm oc}.
\]

Equivalently, under the normalized minimizer reduction, there should be no
admissible probability measure \(\mu\) with

\[
\mu(\{-1\})\ge\frac12,\qquad
\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1],
\qquad
|E_\mu|<M_{\rm oc}.
\]

The theorem targets are frozen as:

\[
\textbf{Theorem U:}\quad L_-\le M_{\rm oc}
\]

from the one-cut upper construction, and

\[
\textbf{Theorem L:}\quad
\text{no normalized minimizer has }|E_\mu|<M_{\rm oc}.
\]

Only these two statements together imply

\[
L_- = M_{\rm oc}.
\]

The proof must not stop at the two-interval branch.  The two-interval branch is
only the local dangerous family.  The full lower bound needs the following
pure mathematical steps.

The current route decision is to stop treating small-eta/top-slab Krawczyk
tuning as the main line.  Those records remain useful diagnostics, but the
exact proof needs global finite-gap classification.

### Priority 1: one-cut upper construction status

This gives the matching upper bound

\[
L_-\le M_{\rm oc}.
\]

The candidate has support

\[
\{-1\}\cup[a,1],
\]

with density of the form

\[
d\mu_a(x)
=m_a\delta_{-1}
+\frac{x+1-c_a}{\pi(x+1)\sqrt{(1-x)(x-a)}}\,1_{[a,1]}(x)\,dx.
\]

This work is now carried out in Gate 6 below: the coefficient is fixed by the
potential level equation, the density and mass identities are verified, and the
exterior zero structure is proved by the derivative sign table.  The resulting
statement is:

\[
\boxed{\text{Gate 6: }L_-\le M_{\rm oc}\text{ is proof-grade.}}
\]

The formula is recorded here for reference.  In the one-cut notation

\[
s=\sqrt{2(1+a)},\qquad c_a=A(a)s,
\]

the mass identity makes the total mass automatic, and the scalar level equation
is

\[
U_{\mu_a}(1)=0.
\]

Equivalently one may define

\[
0=
\log\frac4{1-a}
-A(a)\left(\log2+sJ(a)\right),
\]

where

\[
J(a)=\frac1\pi\int_a^1
\frac{\log(1/(1-t))}
{(t+1)\sqrt{(1-t)(t-a)}}\,dt.
\]

The decimal values \(x_L,x_R\) are numerical evaluations of the exact
zero equations and are not definitions.  This upper construction is not the
difficult global lower-bound classification, but it fixes the exact value that
the lower bound must match.

### Priority 2: keep the corrected two-interval branch as local model

For

\[
E_\varepsilon=(\ell,r)\cup(\beta,1),
\qquad
\ell=x_L+\varepsilon,\qquad
\beta=1-\varepsilon,
\]

the corrected Cauchy transform is

\[
F(z)=
c\,\frac{z+A}{(z-\ell)(z-r)(z-1)}
\sqrt{(z-\alpha)(z-\beta)}.
\]

Here \(c>0\) is a normalization constant.  With the standard branch convention,
the local sign chamber is

\[
\boxed{-r<A<-\ell}
\]

under

\[
\ell<-1<r<\alpha<\beta<1.
\]

The old no-endpoint-atom model is retired because

\[
m_1=\operatorname{Res}_{z=1}F(z)
=
c\,\frac{(1+A)\sqrt{(1-\alpha)\varepsilon}}
{(1-\ell)(1-r)}
>0.
\]

The local branch proof must show, for the relevant parameter regime,

\[
m_\ell\ge0,\qquad m_r\ge0,\qquad m_1\ge0,
\]

\[
\rho(x)=\frac1\pi
\left|
\frac{x+A}{(x-\ell)(x-r)(x-1)}
\right|
\sqrt{(x-\alpha)(\beta-x)}
\ge0
\quad (x\in[\alpha,\beta]),
\]

and

\[
U_\lambda(x)=0\quad(x\in[\alpha,\beta]),
\qquad
U_\lambda(x)\ge0\quad(x\in[-1,1]).
\]

This branch supports the candidate \(M_{\rm oc}\), but by itself it is still a local
certificate, not a full exact proof.

### Priority 3: prove the pinching and degeneration theorem

Let a finite-gap dual transform have the general form

\[
F_n(z)=
\frac{P_n(z)}{Q_n(z)}
\sqrt{\prod_{j=1}^g(z-\alpha_{j,n})(z-\beta_{j,n})}.
\]

If a minimizing sequence leaves every compact nondegenerate chamber, some gap
must pinch:

\[
\beta_{j,n}-\alpha_{j,n}\to0
\quad\text{or}\quad
\alpha_{j,n},\beta_{j,n}\to \text{endpoint/pole}.
\]

The theorem needed is:

\[
F_n\longrightarrow F_\infty
\]

where \(F_\infty\) is either a lower-genus transform already covered by the
one-cut or corrected two-interval branch, or it has a negative density/residue
and is inadmissible.

This is the bridge from local finite-gap formulas to global exclusion.

### Priority 4: exclude compact non-pinched \(g=2\) chambers

This is the current hardest mathematical gap.

For two zero intervals, write

\[
F(z)=\frac{P(z)}{Q(z)}
\sqrt{(z-\alpha_1)(z-\beta_1)(z-\alpha_2)(z-\beta_2)}.
\]

If there is an extra positive component

\[
I=(u,v),\qquad c\in(u,v),
\]

the local atom/neck variables are

\[
q,\qquad a=c-u,\qquad b=v-c,\qquad c.
\]

The KKT equations should be written as

\[
K(q,a,b,c,\xi)=0,
\]

where \(\xi\) denotes the finite-gap background jets.  The correct
linearization is

\[
dK=A\,dy+B\,d\xi.
\]

The old rank-six Schur claim was wrong.  The correct obstruction is the
cokernel matrix

\[
B_{\mathrm{cok}}=\ker(A^T)\,B.
\]

The goal is to prove that no nonnegative finite-gap chamber has the required
cokernel sign pattern.  The split-kernel determinant that should replace the
invalid three-kernel determinant is

\[
\Delta_6(x_1,\ldots,x_6)
=
\det\left[
1,\frac1{x-u},\frac1{x-c},\frac1{x-v},
\log\frac1{|x-u|},\log\frac1{|x-v|}
\right]_{x=x_i}.
\]

The required sign theorem is that, after the correct orientation factor,

\[
\prod_i\sigma(x_i)\Delta_6(x_1,\ldots,x_6)
\]

has one fixed nonzero sign on the interlacing chamber.

The second independent obstruction should come from the reduced Hessian

\[
M=P^TGP,
\]

where \(G\) is the Schur complement of the finite-gap energy Hessian.  The
target identities are

\[
e_\zeta^TMe_\zeta=\lambda Q_c,
\]

\[
e_u^TMe_\zeta
=-\frac{\lambda}{2}\Gamma(c-u),
\qquad
e_v^TMe_\zeta
=\frac{\lambda}{2}\Gamma(v-c),
\]

and the curvature clamp

\[
\Gamma\le \frac{2\sqrt{aQ_c}}{c-u},
\qquad
-\Gamma\le \frac{2\sqrt{bQ_c}}{v-c}.
\]

The compact \(g=2\) chamber is closed only if these formulas force either

\[
Q_c<0,
\]

or a violation of the residue/density/interlacing signs.

The current refined hard mouth is one step earlier than the raw Schur
complement:

\[
\boxed{
\text{repair the }F(c)\text{-row and then write the branch-parametrized
second variation.}
}
\]

The previous fully augmented template with independent
\(\lambda_SS\) and \(\lambda_FF(c)\) rows is bookkeeping only.  The
proof-grade convention is now:

\[
\boxed{
S=0\text{ is derived from endpoint stationarity, while }F(c)=0
\text{ is a finite-gap branch equation, not a free }y\text{-stationarity row.}
}
\]

Use the branch-parametrized functional

\[
\begin{aligned}
\Phi_{\rm br}(q,a,b,c,\xi;\lambda)
={}&
(a+b)+\ell_{\rm ext}(\xi)
+\lambda_M(q+m_{\rm ext}(\xi)-1)
+\lambda_{\rm per}\Pi(\xi)\\
+\lambda_-E_-(y,\xi)
+\lambda_+E_+(y,\xi),
\end{aligned}
\]

where

\[
E_-=q\log\frac1a+W_\xi(c-a),
\qquad
E_+=q\log\frac1b+W_\xi(c+b),
\]

\[
S=aW_\xi'(c-a)+bW_\xi'(c+b).
\]

The branch equations are imposed separately:

\[
F_\xi(c)=0,\qquad F_\xi'(c)<0.
\]

At first order they restrict the tangent space by

\[
\delta F_\xi(c)=F_\xi'(c)\delta c+\delta_\xi F_\xi(c)=0.
\]

The reason is concrete.  If one keeps a free term
\(\lambda_FF_\xi(c)\), then in the fixed chart

\[
F_y=(0,0,0,F_\xi'(c)),
\]

and the projected \(c\)-Euler equation becomes

\[
0=\gamma S+\lambda_FF_\xi'(c),
\]

not \(S=0\).  Since the fixed period row has \(\Pi_y=0\), this is an
\(F\)-row obstruction, not a period obstruction.

The next lemma to write is:

\[
\boxed{\textbf{Lemma Branch-Parametrized Phi-Euler-Hessian}}
\]

At every regular compact \(g=2\) extremal, after solving
\(F_\xi(c)=0\) as a branch equation, the chosen \(\Phi_{\rm br}\) must satisfy

\[
d_y\Phi_{\rm br}=0
\Longleftrightarrow
E_-=E_+=S=0
\]

together with mass and period rows, while \(F(c)=0\) enters through the branch
tangent.

The density coordinate convention should also be fixed now.  The working
choice is:

\[
d\eta(x)=G(x)\omega(x)\,dx
\]

is the real perturbation, and the six local jet coordinates are only the row
values

\[
\xi_i=R_i(G).
\]

Thus \(H_{\xi y}\) initially means a mixed second-variation pairing
\((G,\delta y)\), not an ordinary derivative in six free coordinates.  The
period row remains a separate global constraint unless proved otherwise.

In particular,

\[
\delta W_\xi(s)=\int_J\log\frac1{|s-x|}\,d\xi(x),
\qquad
\delta F_\xi(z)=\int_J\frac{d\xi(x)}{z-x}.
\]

The six local rows record only selected functionals of \(G\).  For example,

\[
\delta_\xi S=aR_u(G)+bR_v(G),
\qquad
\delta_\xi F(c)=-R_c(G).
\]

The endpoint rows \(R_-,R_+\) record endpoint differences, not absolute
endpoint values.  Therefore the Schur complement must first be defined on
actual density perturbations and only later pushed down to the finite row
image.

The fixed-chart Euler part is now clean.  With

\[
p=\log(1/a),\quad r=\log(1/b),\quad A=W'(u),\quad B=W'(v),
\]

\[
X=q/a+A,\qquad Y=B-q/b,
\]

one has

\[
d_y\Phi_{\rm br}
=(0,1,1,0)+\lambda_M(1,0,0,0)
+\lambda_-(p,-X,0,A)+\lambda_+(r,0,Y,B).
\]

Thus \(d_y\Phi_{\rm br}=0\) gives

\[
\lambda_-=\frac1X,\qquad \lambda_+=-\frac1Y,
\]

and the \(c\)-row gives

\[
\frac{A}{X}-\frac{B}{Y}=0.
\]

Since

\[
\frac{A}{X}-\frac{B}{Y}
=-\frac{q(aA+bB)}{abXY},
\]

this is exactly \(S=0\) under \(q,a,b,X,Y\ne0\).  The \(q\)-row only fixes
\(\lambda_M\); it is not an extra scalar equation.

The next correction is that period cannot be used as a \(y\)-state row in the
fixed chart.  Since \(\Pi_y=0\), the matrix

\[
(E_-,E_+,M,\Pi)_y
\]

is singular.  Period is only an admissibility condition

\[
\delta\Pi(\xi)=0.
\]

The state lift should instead use

\[
\boxed{A_{\rm st}=(E_-,E_+,M,F_\xi(c)).}
\]

Its \(y\)-Jacobian is

\[
(A_{\rm st})_y=
\begin{pmatrix}
p&-X&0&A\\
r&0&Y&B\\
1&0&0&0\\
0&0&0&F_\xi'(c)
\end{pmatrix},
\]

with

\[
\det (A_{\rm st})_y=-XYF_\xi'(c).
\]

Thus the state lift is regular if

\[
X\ne0,\qquad Y\ne0,\qquad F_\xi'(c)\ne0.
\]

For perturbation rows \(\delta E_-,\delta E_+,\delta M,\delta F\), it gives

\[
\delta q=-\delta M,\qquad
\delta c=-\frac{\delta F}{F_\xi'(c)},
\]

\[
\delta a=
\frac{\delta E_- -p\,\delta M-\frac{A}{F_\xi'(c)}\delta F}{X},
\]

\[
\delta b=
\frac{r\,\delta M-\delta E_+
+\frac{B}{F_\xi'(c)}\delta F}{Y}.
\]

The bordered Schur complement should be

\[
\boxed{
G_0
=H_{\xi\xi}
-
\begin{pmatrix}H_{\xi y}&A_\xi^T\end{pmatrix}
\begin{pmatrix}
H_{yy}&A_y^T\\
A_y&0
\end{pmatrix}^{-1}
\begin{pmatrix}
H_{y\xi}\\
A_\xi
\end{pmatrix}.
}
\]

Equivalently, with the state lift

\[
T\xi=-A_y^{-1}A_\xi\xi,
\]

the density-level reduced Hessian is the symmetric bilinear form

\[
\boxed{
G_{\rm br}(\xi,\zeta)=
D^2\Phi_{\rm br}\big((T\xi,\xi),(T\zeta,\zeta)\big),
\qquad
\delta\Pi(\xi)=\delta\Pi(\zeta)=0.
}
\]

The bordered formula agrees with this expression under
\[
X\ne0,\qquad Y\ne0,\qquad F_\xi'(c)\ne0.
\]

The second-variation theorem must prove

\[
\boxed{
\xi^TG_0\xi\ge0
\quad\text{for actual admissible }\xi\text{ satisfying }\delta\Pi(\xi)=0.
}
\]

The next hard mouth is not yet the curvature clamp.  Since \(G_{\rm br}\) is
defined on actual density perturbations, a naive finite-row quotient would
need

\[
\boxed{
\ker(\rho|_{\mathcal X_\Pi})\subset\operatorname{Rad}(G_{\rm br}),
}
\]

where

\[
\rho(\xi)=(R_0,R_u,R_c,R_v,R_-,R_+,\Pi)(\xi),
\qquad
\mathcal X_\Pi=\{\xi:\Pi(\xi)=0\}.
\]

Equivalently, \(G_{\rm br}\) must descend to

\[
V=\rho(\mathcal X_\Pi)\subset\mathbb R^7.
\]

But this radical quotient is probably false as stated, because \(G_{\rm br}\)
contains the full log-energy

\[
\mathcal E_{\log}(\xi,\xi)
=\iint-\log|x-y|\,d\xi(x)d\xi(y),
\]

which is positive on nonzero zero-mass perturbations in the finite row kernel.
The replacement is a Feshbach / energy-minimal lift:

\[
W^\sharp=\ker(\rho^\sharp|_{\mathcal X_\Pi}),\qquad
\xi=Sr+w,
\]

\[
\rho^\sharp(Sr)=r,\qquad
\mathcal E_{\log}(Sr,w)=0\quad(w\in W^\sharp).
\]

Here the row map must be enlarged by the absolute log-potential anchor

\[
R_{\log c}(\xi)=\delta W_\xi(c)
=\int_J\log\frac1{|c-x|}\,d\xi(x),
\]

because \(R_-,R_+\) are only differences:

\[
R_-=\delta W(c)-\delta W(u),\qquad
R_+=\delta W(v)-\delta W(c).
\]

Thus

\[
\rho^\sharp=(R_0,R_u,R_c,R_v,R_-,R_+,R_{\log c},\Pi).
\]

The energy-minimal lift exists uniquely in the \(\mathcal E_{\log}\)-Hilbert
completion under continuity and feasibility of \(\rho^\sharp\); it should not
be claimed to be a smooth density without a separate regularity theorem.

The Hilbert-space statement must be made on zero-mass directions.  The
logarithmic energy is positive definite only after the mass/constant mode is
removed.  Thus either work on

\[
H_{0,\Pi}=\{h\in H_\Pi:R_0(h)=0\},
\]

so feasible row data have \(R_0=0\), or split \(R_0\) off as a separate
finite-dimensional coordinate before applying the minimal-lift theorem.
Without this convention, the phrase "every \(r\in V^\sharp\) has a minimal
log-energy lift" is too strong.

The row-continuity assumption is a separated fixed-chart statement.  With

\[
J\Subset\mathbb R\setminus\{u,c,v\},
\]

zero-mass log-energy is equivalent to an \(H^{-1/2}(J)\) norm, so rows are
continuous if their kernels lie in \(H^{1/2}(J)\).  The Cauchy rows, split
kernels \(L_\pm\), and \(R_{\log c}\) are continuous under this separation.
The period kernel \(\pi_0\) is continuous only if its jump lies in a gap away
from the support; an interior step jump is not \(H^{1/2}\).

The finite effective object, if the non-log part factors through
\(\rho^\sharp\), is

\[
Q_{\rm eff}(r)=\mathcal E_{\log}(Sr,Sr)+b(r,r),
\qquad r\in V^\sharp=\rho^\sharp(\mathcal X_\Pi).
\]

Separately, one should prove a row-realization lemma.  For the eight kernels

\[
1,(x-u)^{-1},(x-c)^{-1},(x-v)^{-1},L_-,L_+,
\log\frac1{|c-x|},\pi_0
\]

let \(\operatorname{Rel}\) be their linear relations on the regular support.
Smooth compactly supported density bumps realize exactly
\(\operatorname{Rel}^{\perp}\).  Full period-zero row realization requires the
extra determinant condition that these eight kernels are independent on
regular support.
This supports Chebyshev tests, but it does not by itself make the Hessian
finite-dimensional.

Until the minimal-lift or actual-density formulation is closed, the six local
rows cannot be treated as arbitrary free Hessian coordinates.  Any cokernel
vector is meaningful only through its action on the actual row image \(V\).

After that, the next theorem is not the curvature clamp directly.  The
log-minimal lift contributes a nonlocal term

\[
K_{\log}(r,s)=\mathcal E_{\log}(Sr,Ss),
\]

so one must first prove the effective endpoint Hessian identities for

\[
P^TQ_{\rm eff}P.
\]

Only if this effective block has the expected entries does the curvature clamp
need exactly five reduced-Hessian identities:

\[
e_u^TMe_u=\lambda a,\qquad
e_v^TMe_v=\lambda b,\qquad
e_\zeta^TMe_\zeta=\lambda Q_c,
\]

\[
e_u^TMe_\zeta=-\frac{\lambda}{2}\Gamma(c-u),
\qquad
e_v^TMe_\zeta=\frac{\lambda}{2}\Gamma(v-c).
\]

No \(e_u^TMe_v\) identity is needed for the clamp itself.

The immediate theorem queue is therefore:

1.  Prove the separated-chart Feshbach minimal-lift theorem.  This legitimizes
    \(Q_{\rm eff}\) as the finite effective Hessian on feasible row data; it
    does not compute the endpoint entries.

    Abstract content: for a real Hilbert space \(H\), a continuous finite-rank
    row map \(\rho^\sharp:H\to\mathbb R^m\), and
    \(W=\ker\rho^\sharp\), one has

    \[
    H=W\oplus W^{\perp_{\mathcal E}}.
    \]

    Each feasible \(r\in V=\rho^\sharp(H)\) has a unique lift

    \[
    Sr\in W^{\perp_{\mathcal E}}\cap(\rho^\sharp)^{-1}(r),
    \]

    and any \(\xi\in H\) decomposes as

    \[
    \xi=S\rho^\sharp(\xi)+w,\qquad w\in W.
    \]

    If

    \[
    G_{\rm br}=\mathcal E_{\log}+b\circ(\rho^\sharp,\rho^\sharp),
    \]

    then

    \[
    G_{\rm br}(Sr+w,Ss+w')
    =
    Q_{\rm eff}(r,s)+\mathcal E_{\log}(w,w').
    \]

    Therefore \(G_{\rm br}\ge0\) on a closed feasible tangent space implies
    \(Q_{\rm eff}\ge0\) only on the corresponding feasible row image.  If the
    tangent object is merely a cone, the later endpoint directions must be
    checked to lie in its lineality or in two-sided feasible directions.

2.  Prove endpoint-transfer realization.  The three columns of

    \[
    P:\operatorname{span}\{e_u,e_v,e_\zeta\}\to V^\sharp
    \]

    must lie in the actual row image.  Full row surjectivity is optional; these
    three columns are the necessary target.

    The theorem should be stated narrowly:

    \[
    \textbf{EndpointTransferRealization3:}\qquad
    P e_j\in \rho^\sharp(\mathcal X_{\Pi,\mathrm{lin}})
    \quad(j=u,v,\zeta).
    \]

    Equivalently, construct actual perturbations

    \[
    \xi_u,\xi_v,\xi_\zeta
    \]

    in the fixed-period, zero-mass or external-mass chart such that

    \[
    \rho^\sharp(\xi_j)=P e_j.
    \]

    The columns must satisfy \(r_{0j}=0\) in the zero-mass version, the period
    row \(r_{\Pi j}=0\), all row-relation constraints
    \(\lambda\cdot P e_j=0\) for \(\lambda\in\operatorname{Rel}\), and the
    relevant critical-cone lineality condition.  A formal endpoint row in the
    ambient coordinate space is not enough.

3.  Prove or replace the effective endpoint identities for
    \(M=P^TQ_{\rm eff}P\).  The log-minimal term
    \(K_{\log}=\mathcal E_{\log}(S\cdot,S\cdot)\) can alter the old local
    entries, so identities for the finite Schur term \(b\) alone are not
    enough.

4.  If the old five entries survive, derive the curvature clamp.  If they do
    not, use the actual effective entries

    \[
    m_{uu},m_{vv},m_{\zeta\zeta},m_{u\zeta},m_{v\zeta}
    \]

    and prove the corrected effective-entry clamp.

5.  Prove that the resulting clamp forces the Wronskian/sign pattern
    contradiction for the two-dimensional KKT cokernel.  The six-kernel
    Chebyshev determinant is only a variation-diminishing tool; it does not
    close compact \(g=2\) by itself.

Stop/go rule:

\[
\boxed{\text{GO, but only on the }Q_{\rm eff}\text{ theorem queue.}}
\]

If the actual effective entries do not imply the Wronskian contradiction, stop
the compact \(g=2\) Hessian-clamp route.  Do not return to the retired
free-\(F(c)\) multiplier, the naive finite-row radical quotient, or a
standalone Chebyshev determinant proof.


### Priority 5: global closure statement

The final theorem should read:

> Every normalized minimizer with \(|E_\mu|<M_{\rm oc}\) either belongs to a covered
> one-cut or corrected two-interval branch, degenerates to one of those
> branches, or lies in a compact \(g=2\) chamber that is impossible by the
> KKT-cokernel and reduced-Hessian obstruction.

Only after this theorem and the one-cut upper construction are both written
does the exact statement follow:

\[
\boxed{L_- = M_{\rm oc}=1.8344304757626617\ldots}.
\]

The \(Q_{\rm eff}\) work closes only one component of this global statement:
the compact non-pinched \(g=2\) chamber.  It does not close by itself the
one-cut upper construction, corrected \(g=1\) branch, pinching/degeneration,
high-genus local-neck reduction, regularity removal, or standard normalized
minimizer reduction.

After the minimal-lift theorem, the next proof target is a three-column
endpoint-transfer realization theorem, not full row surjectivity:

\[
P e_u,\ P e_v,\ P e_\zeta\in V^\sharp.
\]

Equivalently, construct actual admissible perturbations
\(\xi_u,\xi_v,\xi_\zeta\) with

\[
\rho^\sharp(\xi_j)=P e_j,\qquad j\in\{u,v,\zeta\},
\]

in the regular separated compact \(g=2\) chart.  Only after those three
directions are available does \(P^TQ_{\rm eff}P\) become a proof-grade object.

If the three-column realization fails, the finite Hessian-clamp route must be
downgraded immediately.  The two available fallbacks are:

1.  an actual-density formulation, keeping \(G_{\rm br}\) on real density
    perturbations and deriving the endpoint tests directly; or
2.  a cone formulation, proving that the combinations

    \[
    Be_u+Ae_\zeta,\qquad Be_\zeta+Ae_v
    \]

    are two-sided feasible directions.  If only one-sided feasibility is
    available, the ordinary PSD matrix clamp is not justified.

Once three-column realization is proved, the next theorem becomes the true
effective endpoint Hessian identity.  With

\[
p_j=P e_j,\qquad m_{ij}=Q_{\rm eff}(p_i,p_j),
\]

the target is

\[
m_{uu}=\lambda a,\quad m_{vv}=\lambda b,\quad
m_{\zeta\zeta}=\lambda Q_c,
\]

\[
m_{u\zeta}=-\frac{\lambda}{2}\Gamma(c-u),\qquad
m_{v\zeta}=\frac{\lambda}{2}\Gamma(v-c),\qquad \lambda>0.
\]

If the log-minimal term changes these entries, replace the old clamp by the
actual-entry clamp rather than forcing the old identities.

Current audit of the three columns:

The existing branch-state equations do not yet determine \(P e_u\),
\(P e_v\), or \(P e_\zeta\).  They give only compatibility constraints after a
specific endpoint convention has been chosen.  Thus the next missing object is
the explicit endpoint-transfer map \(P\).

Natural formal candidates are available:

\[
p_u=(0,r_{uu},0,r_{vu},r_{\log u}+X,-r_{\log u},r_{\log u},0)
\]

if \(e_u\) means \(\delta u=1\) with \(c,v,q\) fixed;

\[
p_v^0=(0,0,0,1,0,-Y,0,0)
\]

if \(e_v\) means \(\delta v=1\) with \(c,u,q\) fixed, with
\(\partial_vL_+=k_v\) and \(R_{\log c}=0\);

and

\[
p_\zeta^0=\left(0,0,F_c,0,-\frac qa,-\frac qb,0,0\right)
\]

if \(e_\zeta\) means moving \(c\) with \(u,v,q\) fixed, so
\((\delta q,\delta a,\delta b,\delta c)=(0,1,-1,1)\).

These are not yet proof-grade columns.  Each must still be checked against
\(\operatorname{Rel}^{\perp}\), period-zero, the zero-mass/external-mass
convention, and actual two-sided density realization.  Until that is done,
\(P^TQ_{\rm eff}P\) remains a formal target.

Adopt the formal convention \(P^0\) using endpoint-length orientation:

\[
e_u^0=\partial_a=-\partial_u,\qquad
e_v^0=\partial_b=\partial_v,\qquad
e_\zeta^0=\partial_c\text{ with }u,v,q\text{ fixed}.
\]

Then

\[
p_u^0=(0,1,0,0,-X,0,0,0),\qquad
p_v^0=(0,0,0,1,0,-Y,0,0),
\]

\[
p_\zeta^0=\left(0,0,F_c,0,-\frac qa,-\frac qb,0,0\right).
\]

This is only a formal branch-compatible convention.  Since \(\operatorname{Rel}\)
is not yet known to vanish, the row-level checks are

\[
\lambda_u-X\lambda_-=0,\qquad
\lambda_v-Y\lambda_+=0,
\]

\[
F_c\lambda_c-\frac qa\,\lambda_- -\frac qb\,\lambda_+=0
\qquad(\lambda\in\operatorname{Rel}).
\]

If these hold, an explicit bump construction in the regular support realizes
the rows as signed smooth density perturbations.  That still does not prove
two-sided critical-cone feasibility; positivity and lineality remain separate
conditions before using \(P^{0T}Q_{\rm eff}P^0\).

Rel audit:

The seven kernels

\[
1,(x-u)^{-1},(x-c)^{-1},(x-v)^{-1},L_-,L_+,\log\frac1{|c-x|}
\]

are independent on any nonempty regular interval separated from \(u,c,v\).
The period kernel is the obstruction.  If \(\pi_0\) is constant on the chosen
regular support, then \(k_\Pi\) is proportional to \(k_0\) and
\(\operatorname{Rel}\ne0\).  If the chosen support sees two different period
values, then \(\operatorname{Rel}=0\) and the \(P^0\) row checks are automatic.

Direct singularity comparison does not naturally prove the three nontrivial
annihilation identities unless it proves the stronger \(\operatorname{Rel}=0\)
statement.  In a nonzero-\(\operatorname{Rel}\) case, those identities would
be extra branch-parameter constraints, not consequences of the row relation.

Stop/go: do one bounded \(P^0\) audit.  Either choose support with two period
values and prove \(\operatorname{Rel}=0\), or verify the three displayed
annihilation identities directly.  If neither closes, stop the finite-row
\(P^{0T}Q_{\rm eff}P^0\) route and switch to the actual-density/cone endpoint
test formulation.

2026-05-06 refined decision:

The row-identity fallback should not be treated as the main route.  The three
identities

\[
\lambda_u=X\lambda_-,\qquad
\lambda_v=Y\lambda_+,\qquad
F_c\lambda_c=\frac qa\,\lambda_-+\frac qb\,\lambda_+
\]

contain branch-state constants and are not automatic singularity consequences
of \(\lambda\in\operatorname{Rel}\).  The best next attempt is therefore:

1. choose regular realization support crossing two period values;
2. prove \(\operatorname{Rel}=0\) from seven-kernel independence plus
   nonconstant period row;
3. realize \(p_u^0,p_v^0,p_\zeta^0\) by actual period-zero, zero-mass signed
   smooth perturbations;
4. check that these are two-sided critical directions, not merely one-sided
   cone directions.

Only after these four items can \(P^{0T}Q_{\rm eff}P^0\) be used in a PSD
curvature-clamp argument.  If item 1 or item 4 fails, the finite-row clamp
route must be replaced by an actual-density or second-order cone formulation.

The \(\operatorname{Rel}=0\) step is now reduced to a short analytic lemma.
If a relation holds on \(J_1\cup J_2\) and

\[
\pi_0|_{J_1}=1,\qquad \pi_0|_{J_2}=-\theta_{\rm per},\qquad
\theta_{\rm per}>0,
\]

with \(J_1,J_2\) genuine open regular pieces separated from \(u,c,v\) and with
fixed real log branches, then the non-period part \(H\) is constant on both
intervals.  Thus \(H'\) is
a rational function vanishing on open sets, hence identically zero.  Its
singular parts at \(u,c,v\) kill all non-period coefficients, and the two
remaining equations

\[
\lambda_0+\lambda_\Pi=0,\qquad
\lambda_0-\theta_{\rm per}\lambda_\Pi=0
\]

force \(\lambda_0=\lambda_\Pi=0\).  Therefore the row-level obstruction is
closed whenever such a two-period support is admissible.  The remaining hard
point is no longer \(\operatorname{Rel}\); it is actual two-sided critical
direction realization.

Next lineality criterion:

In a compact non-pinched regular chamber, row-level realization upgrades to a
two-sided critical direction if the bump support stays away from endpoints and
active boundaries, the background density has a positive lower bound there,
inactive inequalities have strict slack, and the active equality map has
regular linearization.  Then the implicit-function theorem corrects both
\(+t\) and \(-t\) perturbations by \(O(t^2)\), so the realized row vector lies
in the lineality of the critical cone.

Thus the next proof-grade task is to verify these regular-chamber assumptions
for \(p_u^0,p_v^0,p_\zeta^0\).  If strict slack or regular equality rank fails,
the finite-row PSD clamp cannot be used and the route must switch to a
one-sided cone KKT formulation.

2026-05-06 lineality decision:

Do not switch to cone KKT yet.  In a compact non-pinched chamber, if the
two-period support lies in positive-density regular interiors, signed compact
bumps are two-sided and the strict inequalities

\[
a>0,\qquad b>0,\qquad q>0,\qquad F_c<0
\]

plus strict interlacing survive small \(\pm t\) perturbations.  With the active
equalities corrected by the implicit-function theorem, the expected lemma is

\[
\operatorname{Rel}=0
+\text{ positive regular two-period support}
\Longrightarrow
p_u^0,p_v^0,p_\zeta^0
\in \rho^\sharp(\operatorname{Lin} C_{\rm crit}).
\]

If this lineality lemma is accepted, the next blocker becomes the effective
endpoint Hessian identity for \(M=P^{0T}Q_{\rm eff}P^0\), including the
nonlocal \(K_{\log}\) term.

Effective-entry audit:

Let

\[
m_{ij}=Q_{\rm eff}(p_i^0,p_j^0),\qquad i,j\in\{u,v,\zeta\}.
\]

PSD only gives the actual inequalities

\[
m_{uu}B^2+2m_{u\zeta}AB+m_{\zeta\zeta}A^2\ge0
\quad (x\in(u,c)),
\]

and

\[
m_{\zeta\zeta}B^2+2m_{v\zeta}AB+m_{vv}A^2\ge0
\quad (x\in(c,v)).
\]

To recover the old curvature clamp, one must prove the stronger
common-coefficient identities

\[
m_{uu}=\lambda a,\quad m_{vv}=\lambda b,\quad
m_{\zeta\zeta}=\lambda Q_c,
\]

\[
-\frac{2m_{u\zeta}}{c-u}
=\frac{2m_{v\zeta}}{v-c}
=\lambda\Gamma.
\]

If \(K_{\log}\) breaks this common coefficient and no replacement Wronskian
argument works with unequal coefficients, the compact \(g=2\)
Hessian-clamp route must stop.

Conservative review: the old five entries should not be assumed to survive
unchanged.  The term

\[
K_{\log}(p_i^0,p_j^0)
=\mathcal E_{\log}(Sp_i^0,Sp_j^0)
\]

is a genuine nonlocal Gram contribution.  The next derivation is to compute or
characterize

\[
m_{ij}
=b(p_i^0,p_j^0)+\mathcal E_{\log}(Sp_i^0,Sp_j^0)
\]

through the Riesz/minimal-lift system on the zero-mass, fixed-period Hilbert
space.  Continue only if this Gram contribution preserves the old common
\(\lambda,\Gamma\) structure or if the resulting actual-entry clamp still
forces the Wronskian sign contradiction.

Concrete Feshbach form:

Let \(g_i\) be the Riesz representer of the row \(\ell_i\):

\[
\mathcal E_{\log}(g_i,h)=\ell_i(h).
\]

Set

\[
C_{ij}=\ell_i(g_j)=\mathcal E_{\log}(g_i,g_j).
\]

When \(\operatorname{Rel}=0\) on the feasible row support, \(C\) is invertible
on the row image and the minimal lift satisfies \(Sr=\sum_i\alpha_i g_i\) with
\(C\alpha=r\).  Therefore

\[
K_{\log}(r,s)=r^TC^{-1}s,
\]

and the actual compact \(g=2\) matrix is

\[
M=P^{0T}(B+C^{-1})P^0.
\]

The next calculation is to test whether \(P^{0T}C^{-1}P^0\) preserves the
old five-entry pattern or destroys the common \(\lambda,\Gamma\) structure.
Equivalently, with

\[
N=P^{0T}C^{-1}P^0,
\]

the old clamp survives only if the five relevant entries of \(N\) lie in the
same one-dimensional template:

\[
N_{uu}=\delta a,\quad N_{vv}=\delta b,\quad
N_{\zeta\zeta}=\delta Q_c,
\]

\[
-\frac{2N_{u\zeta}}{c-u}
=\frac{2N_{v\zeta}}{v-c}
=\delta\Gamma.
\]

If \(\Gamma=0\), read the off-diagonal condition as
\(N_{u\zeta}=N_{v\zeta}=0\), and require the new scale
\(\lambda_B+\delta>0\).  This is a codimension-four condition on the five
relevant entries and is not automatic for a generic positive definite Gram
correction.  It requires an extra symmetry, orthogonality, or finite-gap Euler
identity.  If it fails, the route must use the actual-entry clamp with unequal
cross coefficients and prove a replacement Wronskian contradiction.

2026-05-06 review update:

The local neck algebra gives

\[
P_c=0,\qquad \Gamma>0,\qquad Q_c<0
\]

under the compact regular signs

\[
A=W'(u)<0<B=W'(v),\qquad X=U'(u)>0,\qquad F_c<0.
\]

This is a local sign lemma, not yet an effective Hessian theorem.  It becomes
a compact \(g=2\) contradiction only after proving

\[
m_{\zeta\zeta}
=Q_{\rm eff}(p_\zeta^0,p_\zeta^0)<0,
\]

or after proving the stronger identity

\[
m_{\zeta\zeta}=\lambda Q_c,\qquad \lambda>0.
\]

The sign \(Q_c<0\) also shows why the old common-template route is not the
right main target.  Since \(N=P^{0T}C^{-1}P^0\succeq0\), a nontrivial positive
Gram correction cannot satisfy

\[
N_{uu}=\delta a,\qquad
N_{vv}=\delta b,\qquad
N_{\zeta\zeta}=\delta Q_c
\]

with \(a,b>0\) and \(Q_c<0\), except in the trivial zero-correction case.
Thus the compact \(g=2\) priority is now the sharper lemma

\[
\boxed{\textbf{EffectiveNeckNegativity:}\quad
b(p_\zeta^0,p_\zeta^0)
+(p_\zeta^0)^TC^{-1}p_\zeta^0<0.}
\]

If this fails, the diagonal shortcut is dead and the route must move to the
actual-entry Wronskian or direct density/cone KKT formulation.

Historical conditional capacity reduction:

Under the separated regular compact \(g=2\) assumptions, plus the corrected
branch Euler/state-lift, Feshbach minimal lift, and two-sided realization of
\(p_\zeta^0\), compact \(g=2\) is excluded by the single scalar inequality

\[
Q_{\rm eff}(p_\zeta^0,p_\zeta^0)<0.
\]

This paragraph is a historical conditional route, not the current Gate 1
closure.  The active rank-defect hard mouth is the raw augmented circuit
obstruction and the MovingSchifferMajorantSignTheorem described below.

Equivalently, with

\[
p_\zeta^0=\left(0,0,F_c,0,-\frac qa,-\frac qb,0,0\right),
\]

define

\[
K_\zeta=(p_\zeta^0)^TC^{-1}p_\zeta^0
=
\inf\left\{\mathcal E_{\log}(\eta,\eta):
\eta\in H_{0,\Pi},\ \rho^\sharp(\eta)=p_\zeta^0\right\}.
\]

The remaining hard estimate is

\[
\boxed{
K_\zeta<-b(p_\zeta^0,p_\zeta^0).
}
\]

If \(b(p_\zeta^0,p_\zeta^0)=\lambda_BQ_c\) with \(\lambda_B>0\), this is the
capacity bound

\[
\boxed{
K_\zeta<-\lambda_BQ_c.
}
\]

This cannot be inferred from \(Q_c<0\) and \(C^{-1}\succeq0\) alone; the
Riesz/minimal-lift problem for this specific two-cut row must be solved or
estimated.  In Euler-Lagrange form, the minimizer satisfies a finite
Hilbert-transform/Cauchy-transform equation on \(J_1\cup J_2\).  This is the
exact route's current compact \(g=2\) hard mouth.

Equivalent Schur-positive form:

Let

\[
r=p_\zeta^0,\qquad T=-b(r,r).
\]

If \(b(r,r)=\lambda_BQ_c\) with \(\lambda_B>0\), then

\[
T=-\lambda_BQ_c>0.
\]

Since \(C\succ0\), the capacity estimate

\[
r^TC^{-1}r<T
\]

is equivalent to

\[
\boxed{
\mathcal S_\zeta=
\begin{pmatrix}
C&r\\
r^T&T
\end{pmatrix}
\succ0.
}
\]

Equivalently,

\[
(\alpha^Tr)^2<T\,\alpha^TC\alpha
\qquad(\alpha\ne0).
\]

The next named target should therefore be

\[
\boxed{\textbf{EffectiveNeckSchurPositive:}\quad
\mathcal S_\zeta\succ0.}
\]

To attack it, construct the two-cut Riesz representers \(g_i\) of the row
kernels, compute

\[
C_{ij}=\ell_i(g_j),
\]

and prove the augmented Gram matrix is positive definite.  The standard
finite Hilbert-transform inversion gives the candidate \(g_i\), but branch,
sign, mass, and period normalizations must be fixed before it is a proof.
This use of \(\operatorname{Rel}=0\) must be in the Hilbert-functional sense,
not only pointwise on smooth bumps; the bridge is row continuity plus density
of smooth compactly supported perturbations in the separated-chart energy
space.

First-order cokernel audit:

There is also a first-order KKT route, but it is only a reduction at this
point.  Eliminating the four local variables from the six augmented rows gives
a two-dimensional adjoint cokernel, not six independent moment constraints.
Under the compact-neck stationarity \(aA+bB=0\), the explicit cokernel kernels
can be written as

\[
K_1=
-r-\frac abp-\frac abL_-+L_+,
\]

\[
K_2=
p\Gamma+\frac a{x-u}+\frac{Q_c}{x-c}
+\frac b{x-v}+\Gamma L_-,
\]

with the local sign lemma

\[
\Gamma>0,\qquad Q_c<0.
\]

This proves the conditional first-order reduction:

\[
\operatorname{span}\{K_1,K_2\}\text{ has no admissible oriented compact sign
pattern}
\Longrightarrow
\text{no compact non-pinched }g=2.
\]

It does not close the chamber by itself.  The Wronskian

\[
W=K_1K_2'-K_1'K_2=C_0+C_-L_-+C_+L_+
\]

has coefficients whose signs are not forced by \(Q_c<0\) and \(\Gamma>0\)
alone.  With \(y=x-c\),

\[
C_+(y)=
-\frac a{(y+a)^2}
-\frac{Q_c}{y^2}
-\frac b{(y-b)^2}
-\frac{\Gamma a}{y(y+a)},
\]

\[
C_-(y)=
\frac ab\left(
\frac a{(y+a)^2}
+\frac{Q_c}{y^2}
+\frac b{(y-b)^2}
\right)
+\frac{\Gamma b}{y(y-b)}.
\]

The signs of these expressions depend on more than the local inequalities.
Thus the naked Chebyshev/Wronskian route needs an additional global oval
inequality before it can exclude compact \(g=2\).  Until such a theorem is
proved, the main hard mouth remains EffectiveNeckSchurPositive, or else an
actual-entry Wronskian / cone-KKT replacement.

Green/Gram-extension audit:

One can formally reproduce the neck row by the distribution

\[
D_\zeta=
F_c\partial_c\delta_c
-\frac qa(\delta_c-\delta_u)
-\frac qb(\delta_v-\delta_c),
\]

because

\[
\mathcal E_{\log}(D_\zeta,\eta)=p_\zeta^0(\eta)
\]

on smooth external perturbations.  This does not make
\(\mathcal S_\zeta\) a proved Gram matrix.  \(D_\zeta\) contains point masses
and a dipole, so it is not in \(H_{0,\Pi}\), and its self-energy requires a
Hadamard finite-part convention.  Such a finite part is not automatically a
positive Hilbert inner product and is not automatically the negative of the
finite non-log block \(b(p_\zeta^0,p_\zeta^0)\).  Therefore
RenormalizedNeckEnergyIdentity should be recorded only as heuristic
bookkeeping unless a genuine positive extension Hilbert space and matching
finite-part identity are proved.

The reliable remaining target is the single-RHS finite-Hilbert estimate:

\[
K_\zeta=
\inf\left\{
\mathcal E_{\log}(\eta,\eta):
\eta\in H_{0,\Pi},\ \rho^\sharp(\eta)=p_\zeta^0
\right\}
<T,
\qquad T=-b(p_\zeta^0,p_\zeta^0).
\]

Equivalently, solve \(C\alpha=p_\zeta^0\) and prove

\[
\alpha^Tp_\zeta^0<T.
\]

In Rayleigh form, this is the trace inequality

\[
\left(
F_c\alpha_c-\frac qa\alpha_- -\frac qb\alpha_+
\right)^2
<
T\,\alpha^TC\alpha
\qquad(\alpha\ne0).
\]

This is now the compact \(g=2\) hard mouth.  Chebyshev sign control and local
\(Q_c<0,\Gamma>0\) do not provide this energy estimate by themselves.

Constrained balayage / residue queue:

The safe interpretation of the formal neck distribution \(D_\zeta\) is as a
continuous functional on \(H_{0,\Pi}\), not as a finite-energy vector.  Its
Riesz representer is the constrained balayage \(\mathsf B_\Pi D_\zeta\), and

\[
\|\mathsf B_\Pi D_\zeta\|_{\mathcal E}^2
=K_\zeta=(p_\zeta^0)^TC^{-1}p_\zeta^0.
\]

Thus the remaining target can be named

\[
\boxed{\textbf{BalayageGapPositive:}\quad T-K_\zeta>0.}
\]

For computation, write the single-RHS minimizer by its Cauchy transform.  With

\[
R(z)=\sqrt{(z-\alpha_1)(z-\beta_1)(z-\alpha_2)(z-\beta_2)},\qquad
R(z)\sim z^2,
\]

and

\[
f_\alpha(z)=-\sum_i\alpha_i k_i'(z),
\]

the solution has the finite-gap form

\[
\boxed{
G_\alpha(z)=f_\alpha(z)+\frac{A_\alpha(z)}{R(z)}.
}
\]

The numerator \(A_\alpha\) cancels the polar parts at \(u,c,v\), while its
affine freedom is fixed by zero mass and fixed period.  The row constraints
are

\[
\int_J\frac{d\eta(x)}{x-s}=-G_\alpha(s)
\qquad(s=u,c,v),
\]

and

\[
\int_JL_\pm(x)\,d\eta(x)
=-\int_{\text{corresponding gap}}G_\alpha(s)\,ds.
\]

Thus, for \(p_\zeta^0\),

\[
G_\alpha(u)=0,\qquad
G_\alpha(c)=-F_c,\qquad
G_\alpha(v)=0,
\]

\[
\int_u^cG_\alpha(s)\,ds=\frac qa,\qquad
\int_c^vG_\alpha(s)\,ds=\frac qb,
\]

plus the two normalizations.  Once this system gives \(C\alpha=p_\zeta^0\),

\[
K_\zeta=\alpha^Tp_\zeta^0
=F_c\alpha_c-\frac qa\alpha_- -\frac qb\alpha_+.
\]

The next theorem to prove is not a generic Schur slogan but the concrete
identity

\[
\boxed{\textbf{LocalSchurTraceIdentity}_\zeta.}
\]

It must identify the branch-Hessian finite trace

\[
T=-b(p_\zeta^0,p_\zeta^0)
\]

with the polar residue trace of

\[
\Omega_\alpha(z)=\frac{A_\alpha(z)^2}{R(z)}\,dz
\]

at \(u,c,v,\infty\), using the same branch state-lift and period
normalization.  Then residue/period positivity should give

\[
T-\alpha^Tp_\zeta^0
=
\int_J\frac{|A_{\alpha,+}(x)|^2}{|R_+(x)|}\,dx
+\mathcal P_{\rm per}(A_\alpha)>0,
\]

unless the row is zero, which \(p_\zeta^0\) is not.  Without
LocalSchurTraceIdentity, this square-residue expression is not yet tied to the
actual finite block \(b\), so compact \(g=2\) is still not excluded.

Diagonal shortcut audit:

Computing the currently defined corrected branch Hessian in the
\(p_\zeta^0\) direction gives a stop signal for the diagonal shortcut.  The
state lift is

\[
\delta y_\zeta=(\delta q,\delta a,\delta b,\delta c)=(0,1,-1,1),
\]

so \(u\) and \(v\) are fixed while \(c\) moves.  Since the proof-grade
\(\Phi_{\rm br}\) has no independent \(\lambda_SS\) Hessian term and no free
\(\lambda_FF(c)\) Hessian term,

\[
v_\zeta^T\nabla_y^2E_-v_\zeta=\frac q{a^2},
\qquad
v_\zeta^T\nabla_y^2E_+v_\zeta=\frac q{b^2}.
\]

With

\[
\lambda_-=\frac1X,\qquad \lambda_+=-\frac1Y,\qquad
Y=-\frac abX,
\]

the endpoint finite contribution is

\[
\boxed{
H_{\rm ep}(p_\zeta^0,p_\zeta^0)
=\frac{q(a+b)}{a^2bX}>0.
}
\]

The endpoint mixed \(y\)-density terms vanish because

\[
\delta c-\delta a=0,\qquad \delta c+\delta b=0.
\]

Thus, under the current corrected fixed-chart branch functional and without an
additional explicitly defined finite non-log term,

\[
b_{\rm br}(p_\zeta^0,p_\zeta^0)>0.
\]

This is incompatible with the hoped-for identification

\[
b(p_\zeta^0,p_\zeta^0)=\lambda_BQ_c,\qquad \lambda_B>0,\quad Q_c<0.
\]

Therefore \(p_\zeta^0\) is not a negative diagonal Hessian direction in the
current convention:

\[
Q_{\rm eff}(p_\zeta^0,p_\zeta^0)
=b_{\rm br}(p_\zeta^0,p_\zeta^0)+K_\zeta>0.
\]

Record this as

\[
\boxed{\textbf{DiagonalShortcutFails}_\zeta.}
\]

The route should now switch to first-order KKT separation / cone KKT unless a
new, explicit MixedSchurTraceIdentity is defined and proved.  The first-order
replacement target is the convex-hull form of the sign obstruction:

\[
\boxed{
0\in\operatorname{int}\operatorname{conv}
\{(\sigma K_1(x),\sigma K_2(x)):x\in J_1\cup J_2\}.
}
\]

This OvalConvexityLemma would rule out any nonzero cokernel combination with
the admissible oriented sign pattern.

Period quotient / free-period audit:

The positive-quadrature route must not be read as a fixed-period tangent
argument without an additional quotient lemma.  If

\[
G_\Pi=\sigma h_\Pi,\qquad h_\Pi>0,
\]

then, with

\[
\pi_0|_{J_1}=1,\qquad
\pi_0|_{J_2}=-\theta_{\rm per},\qquad
\sigma|_{J_1}=-1,\quad \sigma|_{J_2}=1,
\]

one has

\[
\pi_0\sigma<0
\]

on both ovals, hence

\[
\Pi(G_\Pi)<0.
\]

So \(G_\Pi\) is not a fixed-period tangent density.  The first-order route
therefore needs a

\[
\boxed{\textbf{PeriodQuotientLemma}}
\]

showing that \(K_1,K_2\) already represent the full fixed-period quotient
cokernel, or else proving the stronger exclusion with an added period
multiplier

\[
\theta_1K_1+\theta_2K_2+\lambda\pi_0.
\]

The positive period density can still be used in a free-period lift by adding a
period/filling variable \(\tau\) and compensating

\[
\dot\tau+\Pi(G_\Pi)=0.
\]

In that free-period chart the quotient part is a direct linear-algebra check.
The extended local/period system is

\[
\begin{pmatrix}A&0\\0&1\end{pmatrix}
\begin{pmatrix}\dot y\\\dot\tau\end{pmatrix}
+
\begin{pmatrix}B\\\Pi\end{pmatrix}G=0.
\]

An extended left-cokernel \((\kappa,\kappa_\Pi)\) satisfies

\[
\kappa^TA=0,\qquad \kappa_\Pi=0.
\]

Thus the period row is absorbed by \(\tau\), and no extra pointwise sign
multiplier \(\lambda\pi_0\) remains.  The free-period normal space is still
\(\operatorname{span}\{K_1,K_2\}\).

The strong sufficient condition for positive quadrature is the six local rows:

\[
A\dot y_\Pi+B G_\Pi=0.
\]

Equivalently, for the two cokernel kernels,

\[
\int_JK_i(x)G_\Pi(x)\omega(x)\,dx=0,\qquad i=1,2.
\]

Writing

\[
C_\Pi(s)=\int_J\frac{G_\Pi(x)\omega(x)}{x-s}\,dx,\qquad
M_\Pi=\int_JG_\Pi(x)\omega(x)\,dx,
\]

this becomes

\[
\left(-r-\frac abp\right)M_\Pi
-\frac ab\int_u^cC_\Pi(s)\,ds
+\int_c^vC_\Pi(s)\,ds=0,
\tag{P1}
\]

\[
p\Gamma M_\Pi
+aC_\Pi(u)
+Q_cC_\Pi(c)
+bC_\Pi(v)
+\Gamma\int_u^cC_\Pi(s)\,ds=0.
\tag{P2}
\]

The next concrete target is therefore

\[
\boxed{\textbf{FreePeriodResidueAnnihilation}.}
\]

It must write the normalized real period-transfer differential, prove its
boundary density is \(G_\Pi=\sigma h_\Pi\) with \(h_\Pi>0\), and verify the
needed residue/period calculation.  This was an earlier proof target; Gates
1--2 below supersede the unnecessary \((P1),(P2)\) route by the free-period
quotient and the actual-normal lineality argument.

This target is stronger than required in the regular free-period case.  If the
actual KKT normal is

\[
K_\theta=\theta_1K_1+\theta_2K_2
\]

and it has the admissible oriented sign pattern \(\sigma K_\theta\ge0\), then
regular free-period lineality \(G_\Pi=\sigma h_\Pi\), \(h_\Pi>0\), gives

\[
0=\int_JK_\theta G_\Pi\omega
=\int_J\sigma K_\theta h_\Pi\omega.
\]

The right side is strictly positive unless \(K_\theta\equiv0\), which is ruled
out by strict Chebyshev independence of the six-kernel span.  Hence regular
free-period compact non-pinched \(g=2\) is excluded without proving (P1),(P2)
for \(K_1,K_2\) separately.

The former compact \(g=2\) hard case was rank-defect.  Let

\[
r_\Pi=\left(\int_JK_1G_\Pi\omega,\int_JK_2G_\Pi\omega\right).
\]

For any oriented sign-pattern normal,

\[
\theta\cdot r_\Pi
=\int_JK_\theta G_\Pi\omega
=\int_J\sigma K_\theta h_\Pi\omega>0.
\]

The later anchored Schiffer reduction replaces the old ConeOrientationTable
target by the raw augmented circuit sign theorem.  Current audit: Gate 1 has
not yet proved the required Schur-block orientation sign; it has reduced the
rank-defect compact \(g=2\) interior case to
`SchurBlockTotalPositivityLemma`.  Gate 2 then connects that reduced LP to
Proposition 4.1 once the sign theorem is supplied.

Current compact \(g=2\) status:

1. regular free-period non-pinched chambers are excluded by the lineality/sign
   contradiction above;
2. pinching or positivity-boundary limits should be sent to the boundary
   reduction, where the genus-two radical loses a pair of branch points and
   any pole/zero collision creates only a nonnegative endpoint atom in the
   corrected lower-genus branch;
3. the remaining unclosed case is a rank-defect non-pinched interior point,
   pending the Schiffer/cone-descent orientation table.

So the honest statement is: regular free-period compact \(g=2\) is killed,
boundary cases are routed to lower genus, and rank-defect compact \(g=2\)
remains open until the cone orientation table is proved.

Anchored rank-defect update:

The six local rows \(R_0,R_u,R_c,R_v,R_-,R_+\) are not enough to apply the
first-variation length formula, because \(R_-\) and \(R_+\) encode endpoint
potential differences rather than absolute endpoint values.  The rank-defect
Schiffer table must add

\[
R_{\ell c}(G)=\delta W(c)
=\int_J\log\frac1{|c-x|}G(x)\omega(x)\,dx.
\]

Then

\[
\delta W(u)=R_{\ell c}-R_-,
\qquad
\delta W(v)=R_{\ell c}+R_+.
\]

For the neck interval \((u,v)\), with \(U'(u)=X>0\),
\(U'(v)=Y<0\), and \(Y=-aX/b\), the checked boundary derivative is

\[
\boxed{
aX\,\delta L_{uv}
=(a+b)R_{\ell c}-aR_-+bR_+.
}
\tag{ND}
\]

Thus the next rank-defect target is the anchored semi-infinite feasibility
problem

\[
\boxed{
R_0=0,\qquad
R_c=0,\qquad
(a+b)R_{\ell c}-aR_-+bR_+<0,\qquad
V|_{Z_0}<0.
}
\tag{LP}
\]

The perturbation must have the regularized form

\[
V_{\rm Sch}^{(\rho)}
=U_{\nu_\Pi}
+\sum_m s_mV_{{\rm Schiffer},m}^{(\rho)}
+\sum_\ell t_\ell V_{{\rm local},\ell},
\]

and the proof must verify Proposition 4.1 regularity, interior-zero protection,
negative total boundary derivative, and positive pairing with every oriented
sign-pattern normal after quotienting by equality-row corrections.  If this LP
fails, the Farkas dual produces an additional boundary/\(Z_0\) multiplier that
must be routed back to the excluded regular KKT normal or to pinching/lower
genus.

State-lift audit:

The LP above is the regularity-safe slice because it imposes \(R_0=R_c=0\)
before applying the boundary length formula.  If one instead applies the
branch state-lift first, then under the current convention
\(\delta M=R_0\), \(\delta F=-R_c\), \(Y=-aX/b\), and the stationarity relation
\(aA+bB=0\), the neck derivative becomes

\[
\boxed{
aX\,\delta L_{uv}^{\rm lift}
=(a+b)R_{\ell c}-aR_-+bR_+-(ap+br)R_0.
}
\tag{SL-ND}
\]

Thus the documented LP is a sufficient condition, while the weaker
state-lifted inequality

\[
(a+b)R_{\ell c}-aR_-+bR_+-(ap+br)R_0<0
\]

is only available after a separate atom-state regularity check.  The formal
\(\delta q,\delta c\) corrections can create singular atom-weight or
atom-motion terms near \(c\), so they cannot be fed into Proposition 4.1
without proving admissibility of the finite-\(\varepsilon\) perturbation.

Farkas fallback is the next target, but it also needs a clean formulation:
LP failure may first be an equality-row reachability failure rather than a
boundary/\(Z_0\) obstruction, and the separation argument must specify the
topological vector space in which endpoint values, \(R_{\ell c}\), and
restriction to \(Z_0\) are continuous.  After those safeguards, the fallback
dual is governed by the local-correction table, the regularized Schiffer
endpoint table, and the \(Z_0\)-pairing table.

Reduced LP update:

The equality rows can be eliminated without atom-state variations.  Pick two
smooth density bumps \(\psi_1,\psi_2\) in positive-density regular interiors,
away from \(u,c,v\), branch endpoints, and the \(Z_0\)-boundary, such that

\[
M=
\begin{pmatrix}
R_0(\psi_1)&R_0(\psi_2)\\
R_c(\psi_1)&R_c(\psi_2)
\end{pmatrix}
\]

is invertible.  This is achieved by shrinking the bumps to two distinct points
\(x_1,x_2\ne c\), since the determinant tends to

\[
\frac1{x_2-c}-\frac1{x_1-c}\ne0.
\]

For a density seed \(G\), set

\[
E(G)=\binom{R_0(G)}{R_c(G)},\qquad
\widehat G=G-\sum_{j=1}^2(M^{-1}E(G))_j\psi_j.
\]

Then \(R_0(\widehat G)=R_c(\widehat G)=0\).  With

\[
\beta=
\binom{B_{\rm safe}(\psi_1)}
      {B_{\rm safe}(\psi_2)},
\]

the reduced boundary functional is

\[
\boxed{
B_{\rm red}(G)
=B_{\rm safe}(G)-\beta^TM^{-1}E(G).
}
\tag{Bred}
\]

Thus the safe rank-defect target becomes

\[
\boxed{
B_{\rm red}(G)<0,\qquad
\widehat V<0\quad\text{on }Z_0.
}
\tag{RLP}
\]

If this reduced LP is feasible for a regularized Schiffer-period seed, the
rank-defect chamber is ruled out.  If it is infeasible, Farkas gives a reduced
dual

\[
\eta B_{\rm red}(G)+\int_{Z_0}\widehat V\,d\zeta\ge0,
\qquad \eta\ge0,\quad \zeta\ge0.
\]

For the actual finite seed class

\[
\mathcal I=\{\Pi,\alpha_1,\beta_1,\alpha_2,\beta_2\},
\]

this dual must remain finite-dimensional.  Define

\[
b_j=B_{\rm red}(G_j),\qquad
f_j=\widehat V_{G_j}|_{Z_0}.
\]

With the period seed fixed and the four endpoint Schiffer coefficients varied,
the affine reduced LP is

\[
b_\Pi+\sum_\gamma s_\gamma b_\gamma<0,
\qquad
f_\Pi+\sum_\gamma s_\gamma f_\gamma<0\quad\text{on }Z_0.
\]

If this affine system is infeasible, finite-dimensional Farkas gives
\(\eta\ge0\) and \(\zeta\ge0\) on \(Z_0\) such that

\[
\eta b_\gamma+\int_{Z_0}f_\gamma\,d\zeta=0
\quad(\gamma=\alpha_1,\beta_1,\alpha_2,\beta_2),
\]

\[
\eta b_\Pi+\int_{Z_0}f_\Pi\,d\zeta\ge0.
\]

By conic Carathéodory in \(\mathbb R^5\), \(\zeta\) may be replaced by an
atomic measure with at most five atoms:

\[
\zeta_*=\sum_{k=1}^{N}w_k\delta_{x_k},
\qquad
1\le N\le5,\quad w_k>0,\quad x_k\in Z_0.
\]

Thus the next obstruction is finite:

\[
\eta b_\gamma+\sum_{k=1}^{N}w_k f_\gamma(x_k)=0,
\qquad
\eta b_\Pi+\sum_{k=1}^{N}w_k f_\Pi(x_k)\ge0.
\]

The required next theorem is `AtomicFallbackExclusion`: show this finite atomic
certificate is impossible unless the candidate is already on a pinching,
positivity-boundary, or lower-genus degeneration.

Boundary-neutral corrector simplification:

The equality-correction bumps may be chosen so that they do not change the
boundary functional.  Since

\[
B_{\rm safe}(G)=aV_G(u)+bV_G(v),
\]

unit bumps at regular interior points have limiting rows

\[
\left(
1,\frac1{x-c},
a\log\frac1{|u-x|}+b\log\frac1{|v-x|}
\right).
\]

The logarithmic row is not affine in \((x-c)^{-1}\) on a regular interval, so
three interior bumps can be chosen with independent
\((R_0,R_c,B_{\rm safe})\)-rows.  Taking two signed combinations in the
kernel of \(B_{\rm safe}\) gives smooth correctors \(\psi_1,\psi_2\) with

\[
B_{\rm safe}(\psi_1)=B_{\rm safe}(\psi_2)=0,
\]

while the \(2\times2\) matrix of \((R_0,R_c)\)-rows remains invertible.  These
are signed smooth correctors supported in positive-density interiors, so they
remain regularity-safe for small amplitudes.

With this choice,

\[
\boxed{
B_{\rm red}(G)=B_{\rm safe}(G)=aV_G(u)+bV_G(v).
}
\]

Only the \(Z_0\)-functions still need equality correction:

\[
f_j(x)=V_{G_j}(x)
-(U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}E(G_j).
\]

Thus the reduced Schiffer table simplifies to

\[
b_j=aV_{G_j}(u)+bV_{G_j}(v),
\qquad
f_j=\widehat V_{G_j}|_{Z_0}.
\]

The finite fallback can now be checked by positive circuits.  With

\[
F(x)=
\begin{pmatrix}
f_{\alpha_1}(x)\\
f_{\beta_1}(x)\\
f_{\alpha_2}(x)\\
f_{\beta_2}(x)
\end{pmatrix},
\quad
b=
\begin{pmatrix}
b_{\alpha_1}\\
b_{\beta_1}\\
b_{\alpha_2}\\
b_{\beta_2}
\end{pmatrix},
\quad
\tau=f_\Pi,\quad \tau_*=b_\Pi,
\]

`AtomicFallbackExclusion` is the assertion that every positive relation

\[
\eta b+\sum_k w_kF(x_k)=0
\]

has negative lifted value

\[
\eta\tau_*+\sum_k w_k\tau(x_k)<0.
\]

Equivalently, prove the determinant signs:

\[
\tau_*-\tau_X^TF_X^{-1}b<0
\]

for every four-point circuit with \(w=-F_X^{-1}b>0\), and

\[
\sum_{i=1}^5w_i\tau(x_i)<0
\]

for every five-point positive circuit with \(\eta=0\).  Degenerate
determinants must reduce to smaller circuits or to boundary routing.  This
criterion is now the immediate finite-dimensional rank-defect test.

Converting this fallback into a finite-Hilbert equation is conditional: the
allowed seed class must be dense enough, after equality correction, to test all
smooth compactly supported density perturbations on \(J\).  Under that
additional density/closure hypothesis, the fallback kernel satisfies

\[
\operatorname{p.v.}\int_J\frac{d\zeta(s)}{x-s}
+\eta\left(\frac a{x-u}+\frac b{x-v}\right)
=\frac{\Lambda_c}{(x-c)^2}.
\tag{PV}
\]

The PV route is therefore only an optional conditional fallback.  The immediate
task is to compute the reduced Schiffer table

\[
b_j=aV_{G_j}(u)+bV_{G_j}(v),
\qquad
f_j=V_{G_j}-(U_{\psi_1},U_{\psi_2})M^{-1}E(G_j),
\]

and then prove `AtomicFallbackExclusion`.

There is one required normalization step before that table is meaningful.  The
current ledger has not yet defined the endpoint Schiffer seeds

\[
G_\gamma^{(\rho)},\quad V_\gamma^{(\rho)}
\qquad
(\gamma=\alpha_1,\beta_1,\alpha_2,\beta_2).
\]

For

\[
F(z)=\frac{P(z)}{Q(z)}R(z),\qquad
R(z)^2=\prod_\delta(z-\delta),
\]

the raw coordinate derivative is

\[
\partial_\gamma R(z)=-\frac{R(z)}{2(z-\gamma)},
\qquad
\delta_\gamma F_{\rm raw}(z)
=-\frac{P(z)R(z)}{2Q(z)(z-\gamma)}
\]

if \(P,Q\) are frozen.  But this raw variation generally changes the infinity
normalization, residues, period/filling row, pole data, and the branch row
\(F(c)\).  Therefore the admissible seed must first be normalized by a finite
linear correction

\[
\delta_\gamma F(z)
=
\frac{\Delta_\gamma P(z)}{Q(z)}R(z)
-\frac{P(z)R(z)}{2Q(z)(z-\gamma)}
-\frac{P(z)R(z)}{Q(z)^2}\Delta_\gamma Q(z),
\]

with the chart specifying which corrections are allowed and which rows are
held fixed.  Only after this normalization is fixed can one compute
\(V_\gamma(u),V_\gamma(v),E(G_\gamma)\), and \(V_\gamma|_{Z_0}\).  The
convention below fixes this seed definition; determinant signs still cannot be
checked before the resulting table is actually computed.

We now fix the convention.  Write

\[
D_\gamma(z)=\frac{D(z)}{z-\gamma}.
\]

The raw endpoint motion has fixed-cut numerator

\[
H_\gamma^{\rm raw}(z)=-\frac12P(z)Q(z)D_\gamma(z),
\qquad
\delta_\gamma F_{\rm raw}(z)
=\frac{H_\gamma^{\rm raw}(z)}{Q(z)^2R(z)}.
\]

Let \(\mathcal N\) be the finite list of normalization rows required in the
chosen Schiffer chart: unwanted off-cut principal parts, forbidden Laurent
terms at infinity, and the selected period/filling convention.  Do not include
\(R_0\) or \(R_c\), because those rows are corrected later by the
boundary-neutral bumps.  Choose a finite correction numerator space
\(\mathcal H_{\rm norm}\) such that

\[
\mathcal N:\mathcal H_{\rm norm}\to\operatorname{im}\mathcal N
\]

is an isomorphism.  Define \(H_\gamma^{\rm corr}\in\mathcal H_{\rm norm}\) by

\[
\mathcal N(H_\gamma^{\rm corr})=\mathcal N(H_\gamma^{\rm raw}),
\]

and set

\[
\boxed{
H_\gamma=H_\gamma^{\rm raw}-H_\gamma^{\rm corr},
\qquad
\delta_\gamma F(z)=\frac{H_\gamma(z)}{Q(z)^2R(z)}.
}
\]

This proves existence and uniqueness of the normalized endpoint seed in the
chosen chart by finite-dimensional linear algebra.  The Plemelj formula then
defines \(G_\gamma\) through

\[
\delta_\gamma F(z)=
\int_J\frac{G_\gamma(x)\omega(x)}{z-x}\,dx,
\]

and

\[
V_\gamma(s)=
\int_J\log\frac1{|s-x|}G_\gamma(x)\omega(x)\,dx.
\]

The endpoint singularity is only \(O(|x-\gamma|^{-1/2})\), hence integrable.
Cutting it off in a \(\rho\)-neighborhood changes all smooth rows and
logarithmic potentials by \(O(\sqrt\rho|\log\rho|)\).  Thus
\(V_\gamma^{(\rho)}(u),V_\gamma^{(\rho)}(v),E(G_{\gamma,\rho})\), and
\(V_\gamma^{(\rho)}|_{Z_0}\) have the limits needed for the reduced Schiffer
table.  The table entries are now well-defined as

\[
b_\gamma=aV_\gamma(u)+bV_\gamma(v),
\qquad
f_\gamma=
V_\gamma-(U_{\psi_1},U_{\psi_2})M^{-1}E(G_\gamma).
\]

The equality rows are read from the normalized Cauchy transform:

\[
R_0(G_\gamma)=[z^{-1}]_\infty\,\delta_\gamma F(z),
\qquad
R_c(G_\gamma)=-\delta_\gamma F(c),
\]

and for \(s,t\notin J\),

\[
V_\gamma(t)-V_\gamma(s)
=-\int_s^t\delta_\gamma F(y)\,dy.
\]

The absolute endpoint values \(V_\gamma(u),V_\gamma(v)\) are the logarithmic
integrals defining \(V_\gamma\).  Hence the reduced table is computable from
the normalized rational function \(\delta_\gamma F\).

The reduced Schiffer seed table is therefore:

\[
C_j(z):=\int_J\frac{G_j(x)\omega(x)}{z-x}\,dx,\qquad
E_j=\binom{R_0(G_j)}{R_c(G_j)}.
\]

\[
\boxed{
\begin{array}{c|c|c|c|c}
j & C_j(z) & E_j & b_j & f_j(x)\\ \hline
\Pi
&
\displaystyle C_\Pi(z)=\frac{H_\Pi(z)}{Q(z)^2R(z)}
&
\displaystyle \binom{[z^{-1}]_\infty C_\Pi}{-C_\Pi(c)}
&
\displaystyle aV_\Pi(u)+bV_\Pi(v)
&
\displaystyle V_\Pi(x)-(U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}E_\Pi
\\[1.2em]
\gamma\in\{\alpha_1,\beta_1,\alpha_2,\beta_2\}
&
\displaystyle C_\gamma(z)=\frac{H_\gamma(z)}{Q(z)^2R(z)}
&
\displaystyle \binom{[z^{-1}]_\infty C_\gamma}{-C_\gamma(c)}
&
\displaystyle aV_\gamma(u)+bV_\gamma(v)
&
\displaystyle V_\gamma(x)-(U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}E_\gamma
\end{array}
}
\]

where

\[
H_\gamma
=
-\frac12PQD_\gamma-H_\gamma^{\rm corr},
\qquad
\mathcal N(H_\gamma^{\rm corr})
=
\mathcal N\!\left(-\frac12PQD_\gamma\right).
\]

This table gives the \(F,b,\tau,\tau_*\) used in the positive-circuit test:

\[
F=(f_{\alpha_1},f_{\beta_1},f_{\alpha_2},f_{\beta_2})^T,
\quad
b=(b_{\alpha_1},b_{\beta_1},b_{\alpha_2},b_{\beta_2})^T,
\quad
\tau=f_\Pi,\quad \tau_*=b_\Pi.
\]

To compute the endpoint columns, choose a basis \(B_1,\ldots,B_r\) of
\(\mathcal H_{\rm norm}\) and independent normalization rows
\(\mathcal N_1,\ldots,\mathcal N_r\).  Let

\[
A_{im}=\mathcal N_i(B_m),\qquad
n_\gamma=(\mathcal N_i(-\tfrac12PQD_\gamma))_{i=1}^r,
\qquad
h_\gamma=A^{-1}n_\gamma.
\]

Then

\[
H_\gamma=-\frac12PQD_\gamma-\sum_{m=1}^r(h_\gamma)_mB_m.
\]

For any numerator \(H\), define

\[
C_H=\frac{H}{Q^2R},\qquad
E(H)=\binom{[z^{-1}]_\infty C_H}{-C_H(c)},
\]

\[
b(H)=aV_H(u)+bV_H(v),
\qquad
f_H=V_H-(U_{\psi_1},U_{\psi_2})M^{-1}E(H).
\]

By linearity,

\[
E_\gamma=E(-\tfrac12PQD_\gamma)-\sum_m(h_\gamma)_mE(B_m),
\]

\[
b_\gamma=b(-\tfrac12PQD_\gamma)-\sum_m(h_\gamma)_mb(B_m),
\]

\[
f_\gamma=f_{-\frac12PQD_\gamma}-\sum_m(h_\gamma)_mf_{B_m}.
\]

Thus the table is reduced to one invertible normalization matrix \(A\), four
raw normalization vectors \(n_\gamma\), and the basis rows
\(E(B_m),b(B_m),f_{B_m}\).  This is the computable finite-dimensional form of
the endpoint Schiffer table.

In the free-period fixed-\(Q\) chart this becomes explicit.  Assume

\[
Q(z)=\prod_{k=1}^d(z-p_k),
\qquad
p_k\notin J\cup\{u,c,v\},\qquad Q'(p_k)\ne0.
\]

The only normalization rows are pole-cancellation rows

\[
\mathcal N_{k,0}(H)=H(p_k),\qquad
\mathcal N_{k,1}(H)=H'(p_k).
\]

Let

\[
L_k(z)=\prod_{\ell\ne k}\frac{z-p_\ell}{p_k-p_\ell}.
\]

Use the Hermite basis

\[
B_{k,0}(z)=\bigl(1-2L_k'(p_k)(z-p_k)\bigr)L_k(z)^2,
\qquad
B_{k,1}(z)=(z-p_k)L_k(z)^2.
\]

Then the normalization matrix is the identity:

\[
B_{k,0}(p_\ell)=\delta_{k\ell},\quad B'_{k,0}(p_\ell)=0,\qquad
B_{k,1}(p_\ell)=0,\quad B'_{k,1}(p_\ell)=\delta_{k\ell}.
\]

For

\[
H_\gamma^{raw}=-\frac12PQD_\gamma,
\]

\[
H_\gamma^{raw}(p_k)=0,\qquad
(H_\gamma^{raw})'(p_k)
=-\frac12P(p_k)Q'(p_k)D_\gamma(p_k).
\]

Thus

\[
\boxed{
H_\gamma(z)
=
-\frac12P(z)Q(z)D_\gamma(z)
+
\frac12\sum_{k=1}^d
P(p_k)Q'(p_k)D_\gamma(p_k)B_{k,1}(z).
}
\]

This \(H_\gamma\) satisfies \(H_\gamma(p_k)=H_\gamma'(p_k)=0\), so
\(H_\gamma/(Q^2R)\) has no off-cut pole at the fixed \(Q\)-zeros.  If \(d=0\),
the correction sum is empty.

The endpoint column then simplifies.  The correct decay input is
\(\deg P\le d-3\), not necessarily equality.  Therefore

\[
\frac{H_\gamma^{raw}}{Q^2R}=O(z^{-2}),\qquad
\frac{B_{k,1}}{Q^2R}=O(z^{-3}),
\]

so

\[
\boxed{
R_0(G_\gamma)=0,\qquad
R_c(G_\gamma)=-C_\gamma(c)
=-\frac{H_\gamma(c)}{Q(c)^2R(c)}.
}
\]

With zero total mass, normalize \(V_\gamma(\infty)=0\).  Since
\(V_\gamma'=-C_\gamma\),

\[
\boxed{
V_\gamma(s)=\int_s^\infty C_\gamma(y)\,dy
\qquad(s\notin J).
}
\]

Thus

\[
\boxed{
b_\gamma=
a\int_u^\infty C_\gamma(y)\,dy+
b\int_v^\infty C_\gamma(y)\,dy.
}
\]

Let

\[
e_2=\binom01,\qquad
A_c(x)=(U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}e_2.
\]

Since \(E_\gamma=(0,-C_\gamma(c))^T\), the equality-corrected \(Z_0\)-column is

\[
\boxed{
f_\gamma(x)=V_\gamma(x)+C_\gamma(c)A_c(x).
}
\]

The period-transfer column in the same chart is

\[
\boxed{
H_\Pi=\kappa Q^2,\qquad C_\Pi=\frac{\kappa}{R}.
}
\]

Choose the sign of \(\kappa\) so that the boundary density has the oriented
positive period-transfer form

\[
G_\Pi=\sigma h_\Pi,\qquad h_\Pi>0.
\]

Since \(R(z)\sim z^2\),

\[
R_0(G_\Pi)=0,\qquad R_c(G_\Pi)=-C_\Pi(c)=-\frac{\kappa}{R(c)}.
\]

Thus

\[
E_\Pi=\binom{0}{-C_\Pi(c)}.
\]

With \(V_\Pi(\infty)=0\),

\[
V_\Pi(s)=\int_s^\infty C_\Pi(y)\,dy
=\kappa\int_s^\infty\frac{dy}{R(y)}.
\]

Thus

\[
b_\Pi=aV_\Pi(u)+bV_\Pi(v),
\]

\[
f_\Pi=V_\Pi-(U_{\psi_1},U_{\psi_2})M^{-1}E_\Pi.
\]

Now remove the auxiliary bump potential from the circuit test.  Define

\[
\rho_j:=R_c(G_j)=-C_j(c).
\]

All seed columns have zero mass row, so

\[
f_j=V_j-\rho_jA_c.
\]

Let

\[
V_S=(V_{\alpha_1},V_{\beta_1},V_{\alpha_2},V_{\beta_2})^T,
\qquad
\rho_S=(\rho_{\alpha_1},\rho_{\beta_1},\rho_{\alpha_2},\rho_{\beta_2})^T.
\]

A corrected positive circuit gives

\[
\eta b+\sum_k w_k(V_S(x_k)-\rho_SA_c(x_k))=0.
\]

With

\[
\lambda=\sum_k w_kA_c(x_k),
\]

this becomes the raw augmented relation

\[
\boxed{
\eta b+\sum_k w_kV_S(x_k)-\lambda\rho_S=0.
}
\]

The lifted value becomes

\[
\boxed{
\eta b_\Pi+\sum_k w_kV_\Pi(x_k)-\lambda\rho_\Pi.
}
\]

Therefore it is enough to prove the stronger raw test: every such relation,
for arbitrary real \(\lambda\), has strictly negative lifted value.  This
criterion is independent of the chosen equality-correction bumps.

The exact missing sign theorem is:

\[
\boxed{\textbf{RawAugmentedCircuitSign}}
\]

If

\[
\eta b+\sum_k w_kV_S(x_k)-\lambda\rho_S=0,
\qquad
\eta\ge0,\quad w_k>0,\quad x_k\in Z_0,\quad \lambda\in\mathbb R,
\]

then

\[
\boxed{
\eta b_\Pi+\sum_k w_kV_\Pi(x_k)-\lambda\rho_\Pi<0.
}
\tag{RAS}
\]

Equivalently, the extended family

\[
\mathcal T=
(V_{\alpha_1},V_{\beta_1},V_{\alpha_2},V_{\beta_2},-\rho)
\]

with lift \(V_\Pi\) must be an oriented raw augmented Chebyshev system on
\(Z_0\).  Differentiating the determinant identities gives

\[
V_j'(x)=-C_j(x),
\qquad
C_\Pi=\kappa/R,\qquad
C_\gamma=H_\gamma/(Q^2R).
\]

Thus the desired determinant proof must control the two-cut Cauchy/rational
columns generated by the Hermite-normalized numerators \(H_\gamma\) and the
period numerator \(\kappa Q^2\).  The existing six-kernel Chebyshev determinant
only applies to the local jet kernels

\[
1,\ (x-u)^{-1},\ (x-c)^{-1},\ (x-v)^{-1},\ L_-,\ L_+,
\]

so it does not by itself prove `RawAugmentedCircuitSign`.

The formal proof attempt differentiates the determinant in a moving point.
Using

\[
V_j'(x)=-C_j(x),
\]

and multiplying the differentiated row by \(Q(x)^2R(x)\), the endpoint columns
become

\[
\begin{aligned}
&-H_{\alpha_1}(x),\quad -H_{\beta_1}(x),\\
&-H_{\alpha_2}(x),\quad -H_{\beta_2}(x),
\end{aligned}
\]

while the lifted period derivative becomes

\[
-\kappa Q(x)^2.
\]

Thus the missing lemma is a two-cut oriented determinant statement for the
Hermite-corrected columns

\[
H_{\alpha_1},H_{\beta_1},H_{\alpha_2},H_{\beta_2},\kappa Q^2.
\]

The current documents do not prove this sign identity.  The obstruction is the
Hermite pole-cancellation correction

\[
\frac12\sum_kP(p_k)Q'(p_k)D_\gamma(p_k)B_{k,1},
\]

which is not shown to be a positive Cauchy average of the six local jet
kernels.  Therefore the determinant-sign proof stops at this exact point.

There is also a sharper fixed-\(Q\) audit.  In the \(g=2\) decay normalization
\(\deg P=d-3\), while \(\deg D_\gamma=3\).  Hence
\(\deg H_\gamma^{\rm raw}\le2d\), and the Hermite correction has degree at most
\(2d-1\).  Since the normalization enforces

\[
H_\gamma(p_k)=H_\gamma'(p_k)=0
\quad(k=1,\ldots,d),
\]

one has \(Q^2\mid H_\gamma\).  Therefore \(H_\gamma=q_\gamma Q^2\) with
constant \(q_\gamma\).  Comparing leading coefficients gives

\[
\boxed{
H_{\alpha_1}=H_{\beta_1}=H_{\alpha_2}=H_{\beta_2}
=-\frac12\operatorname{lc}(P)\,Q^2
}
\]

under the monic convention for \(Q\).  Thus the endpoint columns currently
written in the fixed-\(Q\) Hermite table are all proportional to
\(C_\Pi=\kappa/R\).  The endpoint Schiffer table is therefore degenerate, not
just missing a sign proof.

The repaired endpoint seed must use the full moving-chart Schiffer variation

\[
\delta_\gamma F
=
\frac{\Delta_\gamma P}{Q}R
-\frac{PR}{2Q(z-\gamma)}
-\frac{PR}{Q^2}\Delta_\gamma Q.
\]

Equivalently,

\[
\boxed{
H_\gamma^{\rm rep}
=
QD\,\Delta_\gamma P
-PD\,\Delta_\gamma Q
-\frac12PQD_\gamma,
\qquad
C_\gamma^{\rm rep}=\frac{H_\gamma^{\rm rep}}{Q^2R}.
}
\]

The pair \((\Delta_\gamma P,\Delta_\gamma Q)\) is determined by the finite
moving-chart linear system fixing zero mass, the chosen free-period/filling
normalization, the pole/residue gauge, and regularity in the separated
non-pinched chart.  The branch row \(R_c\) remains outside this system because
it is corrected by the boundary-neutral bump pair.  The collapsed fixed-\(Q\)
conditions \(H(p_k)=H'(p_k)=0\) are not used as the endpoint seed table unless
they are embedded in a larger moving-\(Q\) system.

The repaired reduced column is

\[
\boxed{
b_\gamma=aV_\gamma(u)+bV_\gamma(v),
\qquad
f_\gamma=V_\gamma-\rho_\gamma A_c,
\qquad
\rho_\gamma=-C_\gamma^{\rm rep}(c).
}
\]

The next Gate 1 check is now the noncollapse condition

\[
\operatorname{rank}
\{C_{\alpha_1}^{\rm rep},C_{\beta_1}^{\rm rep},
C_{\alpha_2}^{\rm rep},C_{\beta_2}^{\rm rep}\}
=4
\quad\text{modulo }C_\Pi,
\]

followed by the raw augmented determinant sign proof.

In a regular moving Schiffer chart, this rank condition passes by chart
injectivity.  Indeed, the differential

\[
(\dot\alpha_1,\dot\beta_1,\dot\alpha_2,\dot\beta_2,\dot\tau)
\mapsto
\sum_\gamma\dot\gamma\,C_\gamma^{\rm rep}+\dot\tau C_\Pi
\]

is injective by the definition of a regular non-pinched endpoint chart after
the moving-chart rows have been imposed.  If it is not injective, the point is a
chart-rank degeneration and is routed to boundary/lower genus, not to the
rank-defect interior.

Gate 1 subcheck status:

\[
\boxed{
\textbf{Rank subcheck: PASS.}\quad
\text{Endpoint columns do not collapse in the regular moving chart.}
}
\]

The algebraic reductions are usable, and the repaired moving-chart table
removes the fixed-\(Q\) endpoint-column collapse.

Why the rank check alone was insufficient: rank says the
endpoint columns do not collapse modulo \(C_\Pi\); the raw augmented circuit
test asks that every positive relation in the first four coordinates has
negative \(V_\Pi\)-lift.  Full rank alone does not imply this.  For example,
in an abstract four-dimensional model one may take

\[
F(x_i)=e_i,\qquad b=-(1,1,1,1),
\]

so \(b+\sum_iF(x_i)=0\) is a positive circuit with full-rank endpoint columns.
The lifted sign is positive if \(\tau_*=1,\tau(x_i)=0\), and negative if
\(\tau_*=-1,\tau(x_i)=0\).  The rank data are identical.  Therefore Gate 1
cannot close from chart injectivity alone.

To close it one must prove the actual two-cut determinant orientation for the
repaired Schiffer columns

\[
H_{\alpha_1}^{\rm rep},H_{\beta_1}^{\rm rep},
H_{\alpha_2}^{\rm rep},H_{\beta_2}^{\rm rep},\kappa Q^2
\]

together with the equality row \(\rho_j=-C_j^{\rm rep}(c)\).  The current note
still defines the repaired columns through the abstract moving-chart system, so
that determinant identity has not yet been established.

The explicit Gate 1 repair attempt is now:

\[
H_\gamma^{\rm rep}
=-\frac12PQD_\gamma-BA^{-1}r_\gamma,
\]

where \(A X_\gamma=-r_\gamma\) is the finite moving-chart system for
\((\Delta_\gamma P,\Delta_\gamma Q)\).  The rows of \(A\) are the zero-mass
row, the free-period/filling convention, the moving-\(Q\) gauge,
pole/residue-state rows, and regular chart rows; \(R_c\) is excluded because
it is corrected by the bump pair.  If \(A\) is singular, the point is routed to
boundary/lower genus.

For any raw augmented determinant, the repaired endpoint columns satisfy the
Schur-complement identity

\[
\det L(H_\Gamma^{\rm rep})
=
\frac{
\det
\begin{pmatrix}
A&r_\Gamma\\
LB&L(H_\Gamma^{raw})
\end{pmatrix}}
{\det A},
\]

up to the fixed column-order sign.  After differentiating in a moving point
and multiplying by \(Q(x)^2R(x)\), the endpoint rows are
\(-H_\gamma^{\rm rep}(x)\) and the period lift is \(-\kappa Q(x)^2\).

The real-pole part is now closed in the regular positive chart.  Since
\(F\) is the Cauchy transform of a positive dual measure, every \(Q\)-pole is
a real atom with positive residue; on each complementary real interval

\[
F'(x)=-\int\frac{d\lambda(t)}{(x-t)^2}<0,
\]

so zeros, branch endpoints, and poles interlace.  Non-real, multiple,
zero-residue, or colliding poles are boundary/lower-genus cases.

The remaining missing sign theorem is the Schur-block orientation:

\[
\boxed{
\text{confluent Cauchy sign of the Schur block}
\Rightarrow
\text{RawAugmentedCircuitSign}.
}
\]

The document currently has the correct formal Schur-complement identity, but
not yet a proof-grade sign computation.  To close this gate one still must
expand the Schur numerator as an explicit signed product,

\[
\det
\begin{pmatrix}
A&r_\Gamma\\
LB&L(H_\Gamma^{raw})
\end{pmatrix}
=
(\text{positive row/column factors})
\cdot
(\text{ordered Cauchy/Vandermonde product}),
\]

and then sign every factor.  In particular, it remains to prove that the
moving-chart rows, free-period/filling convention, moving-\(Q\) gauge rows,
pole/residue-state rows, and equality row are all compatible with one ordered
real Cauchy/confluent Cauchy orientation.  Choosing \(\det A>0\) fixes a chart
orientation; it does not by itself prove the sign of every augmented Schur
minor.

\[
\boxed{
\textbf{Gate 1 status: BLOCKED at SchurBlockTotalPositivityLemma.}\quad
\text{Rank-defect is reduced to the raw augmented circuit obstruction.}
}
\]

This is a genuine obstruction, not just a missing citation.  The repaired
moving chart currently proves noncollapse and invertibility, but those are rank
statements.  A positive-circuit sign is a strictly stronger oriented-cone
statement.  In the finite-dimensional model

\[
F(x_i)=e_i,\qquad b=-(1,1,1,1),
\]

the endpoint block is full rank and \(b+\sum_iF(x_i)=0\) is a positive
circuit; changing only the lifted scalar \(\tau_*\) flips the lifted sign.
Therefore rank, Schur-complement form, and \(\det A>0\) do not determine
`RawAugmentedCircuitSign`.

The precise theorem still needed is an explicit block determinant formula

\[
\det
\begin{pmatrix}
A&r_\Gamma\\
LB&L(H_\Gamma^{raw})
\end{pmatrix}
=
(\text{positive factors})
\cdot
(\text{ordered Cauchy/Vandermonde product})
\]

with the product sign fixed for every admissible raw augmented circuit.  Until
that theorem is proved from an explicit moving Schiffer chart, Gate 1 remains
blocked and the compact \(g=2\) rank-defect chamber remains open.

The algebraic part of this reduction is now separated from the analytic row
realization.  If the full block

\[
\mathcal M=
\begin{pmatrix}
A&R\\
B&C
\end{pmatrix}
\]

is an oriented sign-regular Cauchy/confluent Cauchy block and \(\det A>0\),
then its Schur complement \(S=C-BA^{-1}R\) inherits the required minor signs by
Sylvester's determinant identity:

\[
\det S[I,J]
=
\frac{
\det
\begin{pmatrix}
A&R_{\*,J}\\
B_{I,\*}&C_{I,J}
\end{pmatrix}}
{\det A}.
\]

Thus the remaining Gate 1 problem is exactly
`TPRowRealizationLemma`: write the actual moving-chart rows \(\ell_r\) and
prove that, after positive row/column factors, they form the ordered
sign-regular block required above.  Once that lemma is proved, Schur-block
total positivity and RawAugmentedCircuitSign follow formally.

The row-realization toolbox is now fixed.  Ordered Cauchy rows have signed
determinants by the Cauchy product formula; confluent pole rows inherit the
same sign by differentiating and taking coalescing-node limits; positive
averages of ordered Cauchy rows preserve the sign by multilinearity and
Fubini/Cauchy-Binet.  Therefore the zero-mass row, real pole evaluation and
derivative rows, moving point evaluation rows, and equality row \(\rho\) are
already compatible with the TP block.  The only remaining Gate 1 row audit is
to prove that the period/filling row is a positive Cauchy average and that any
additional regular chart rows are replaced by, or proved equivalent to, this
canonical TP gauge.

That row audit is now reduced in the canonical free-period chart.  The
period/filling constraint is quotiented by the filling variable \(\tau\), so it
does not enter \(A\) as an equality row; the period direction remains only as
the lift column \(C_\Pi=\kappa/R\).  The regular chart conditions are open
inequalities, not equality rows, and failure of any of them routes to Gate 3.
Thus the canonical Gate 1 rows are only the infinity/zero-mass row and the
real pole-state evaluation/confluent derivative rows, plus the raw circuit
evaluation and equality rows.  These rows are all covered by the TP row
toolbox.

So the row side of Gate 1 is now closed in the canonical gauge.  The remaining
Gate 1 obstruction is column-side:

\[
\boxed{\textbf{EndpointPeriodColumnOrientationLemma}}
\]

which must sign the full canonical block containing the four raw endpoint
columns \(PQD_\gamma\) and the period lift column \(Q^2\).  Only after this
column-orientation lemma is proved does RawAugmentedCircuitSign follow.

There is one important refinement.  The column sign cannot be checked from the
rows alone.  If the correction space is the old fixed-\(Q\) Hermite
pole-cancellation space, the endpoint columns collapse back to a multiple of
the period column.  Therefore the final Gate 1 datum is the actual moving
correction column basis

\[
B_\nu=QD\,\Delta P_\nu-PD\,\Delta Q_\nu.
\]

The remaining theorem is

\[
\boxed{\textbf{MovingCorrectionColumnOrientationLemma}}
\]

for the full block whose correction columns are \(B_\nu\), endpoint columns are
\(-\frac12PQD_\gamma\), and period lift is \(\kappa Q^2\).  Once this full
moving block has the required ordered sign, Sylvester transfer gives
SchurBlockTotalPositivityLemma and then RawAugmentedCircuitSign.  Without this
moving correction column determinant, Gate 1 remains open.

The moving-column algebra now gives a sharper audit.  In the monic \(Q\)-chart,

\[
QD\Delta P-PD\Delta Q=D(Q\Delta P-P\Delta Q),
\]

and, since \(\gcd(P,Q)=1\),

\[
(\Delta P,\Delta Q)\mapsto Q\Delta P-P\Delta Q
\]

is an isomorphism from

\[
\mathbb R[z]_{\le d-3}\oplus\mathbb R[z]_{\le d-1}
\]

onto \(\mathbb R[z]_{\le 2d-3}\).  Thus the actual moving correction image is

\[
\boxed{D\mathbb R[z]_{\le 2d-3}.}
\]

For the raw endpoint columns \(E_\gamma=PQD_\gamma\), endpoint interpolation
gives

\[
\boxed{
\mathbb R[z]_{\le 2d+1}
=
D\mathbb R[z]_{\le 2d-3}
\oplus
\operatorname{span}\{E_{\alpha_1},E_{\beta_1},E_{\alpha_2},E_{\beta_2}\}.
}
\]

Since \(Q^2\in\mathbb R[z]_{\le 2d}\), the period numerator satisfies

\[
\boxed{
Q^2
=
DW_Q
+
\sum_\gamma
\frac{Q(\gamma)}{P(\gamma)D_\gamma(\gamma)}\,PQD_\gamma,
\qquad
W_Q\in\mathbb R[z]_{\le 2d-3}.
}
\]

Therefore, modulo the actual moving correction image, the period lift is
already an endpoint interpolation class.  A purely first-order
endpoint-period determinant cannot be the missing nonzero total-positive block
in this quotient.  Gate 1 does not close by determinant orientation alone.
The proof-grade continuation is the second-variation effective endpoint
Hessian:

\[
\boxed{\textbf{EffectiveEndpointHessianLemma}}
\]

which must compute the finite form

\[
Q_{\rm eff}
=
P_{\rm ep}^{T}
\bigl(B_{\rm loc}+C_{\log}^{-1}\bigr)
P_{\rm ep}
\]

after the minimal moving correction has been eliminated, and prove that every
nonnegative atomic Farkas certificate produces an endpoint direction \(h\) with

\[
h^TQ_{\rm eff}h<0.
\]

This is the current Gate 1 hard mouth.  The row-realization and moving-column
interpolation audits are now explicit; the remaining sign is second-order.

Gate 1 data dictionary.  The fixed-\(Q\) Hermite endpoint table is audit-only.
The proof-grade columns are

\[
C_\Pi=\kappa/R,\qquad
C_\gamma=H_\gamma^{\rm rep}/(Q^2R)
\quad(\gamma=\alpha_1,\beta_1,\alpha_2,\beta_2).
\]

For every seed \(j\in\{\Pi,\alpha_1,\beta_1,\alpha_2,\beta_2\}\),

\[
\rho_j=-C_j(c),\qquad
V_j(s)=\int_s^\infty C_j(y)\,dy,\qquad
b_j=aV_j(u)+bV_j(v).
\]

We use

\[
V_S=(V_{\alpha_1},V_{\beta_1},V_{\alpha_2},V_{\beta_2})^T,
\quad
b_S=(b_{\alpha_1},b_{\beta_1},b_{\alpha_2},b_{\beta_2})^T,
\quad
\rho_S=(\rho_{\alpha_1},\rho_{\beta_1},\rho_{\alpha_2},\rho_{\beta_2})^T.
\]

The exact second-order replacement is now the following finite statement.  For
each minimal raw augmented atomic certificate

\[
\mathfrak c=(\eta;\,w_k,x_k;\lambda)
\]

with

\[
\eta b_S+\sum_kw_kV_S(x_k)-\lambda\rho_S=0
\]

on the four endpoint Schiffer columns, define the endpoint-row vector

\[
r_{\mathfrak c}
=
\eta p_b+\sum_kw_kp(x_k)-\lambda p_\rho
\in V^\sharp.
\]

The first-order route wanted to prove the lifted scalar

\[
\eta b_\Pi+\sum_kw_kV_\Pi(x_k)-\lambda\rho_\Pi<0.
\]

After the moving-column interpolation audit, the proof-grade replacement is

\[
\boxed{\textbf{QeffNegativeCertificate:}\quad
Q_{\rm eff}(r_{\mathfrak c},r_{\mathfrak c})<0
\text{ for every non-boundary minimal certificate.}}
\]

This statement is sufficient.  The separated-chart minimal-lift theorem gives
\(\xi_{\mathfrak c}=Sr_{\mathfrak c}\) with
\(\rho^\sharp(\xi_{\mathfrak c})=r_{\mathfrak c}\) and with no row-kernel
energy cross term.  Hence

\[
G_{\rm br}(\xi_{\mathfrak c},\xi_{\mathfrak c})
=
Q_{\rm eff}(r_{\mathfrak c},r_{\mathfrak c}).
\]

If `QeffNegativeCertificate` holds, the rank-defect atomic fallback gives a
two-sided feasible tangent with negative second variation, contradicting the
second-order necessary condition for a compact non-pinched regular minimizer.
Thus Gate 1 is now reduced to a finite \(Q_{\rm eff}\) sign computation, with
zero-vector, support-collision, and chart-rank degeneracies routed to Gate 3.

This finite computation can be stated without ambiguity.  Choose a basis
\(q_1,\ldots,q_m\) of the endpoint-row image and write

\[
r_{\mathfrak c}=\sum_\mu\alpha_\mu(\mathfrak c)q_\mu.
\]

Let

\[
\mathcal H_{\mu\nu}=b(q_\mu,q_\nu)+(C^{-1})_{\mu\nu},
\]

where \(C\) is the Riesz Gram matrix of the row representers.  Then

\[
Q_{\rm eff}(r_{\mathfrak c},r_{\mathfrak c})
=
\alpha(\mathfrak c)^T\mathcal H\alpha(\mathfrak c).
\]

Let \(\mathcal C_{\rm at}\) be the cone of all coordinate vectors
\(\alpha(\mathfrak c)\) coming from non-boundary atomic certificates, and set

\[
\Lambda_{\rm at}
=
\max_{\alpha\in \mathcal C_{\rm at}\cap S^{m-1}}
\alpha^T\mathcal H\alpha.
\]

By conic Carathéodory, \(N\le5\); after excluding support collision and
chart-rank boundary, the normalized certificate set is compact.  Hence

\[
\boxed{
\text{QeffNegativeCertificate}
\Longleftrightarrow
\Lambda_{\rm at}<0.
}
\]

This is now the precise remaining Gate 1 computation: calculate the matrix
\(\mathcal H\) and prove the cone maximum is strictly negative.

Equivalently, split

\[
\mathcal H=B_{\rm at}+N_{\log},\qquad N_{\log}=C^{-1}.
\]

On the normalized certificate cone define

\[
\mu_{\rm loc}
=
\min_{\alpha\in\mathcal C_{\rm at}\cap S^{m-1}}
\left(-\alpha^TB_{\rm at}\alpha\right),
\qquad
\nu_{\log}
=
\max_{\alpha\in\mathcal C_{\rm at}\cap S^{m-1}}
\alpha^TN_{\log}\alpha.
\]

Then

\[
\mu_{\rm loc}>\nu_{\log}
\Longrightarrow
\Lambda_{\rm at}<0.
\]

For pointwise verification one may avoid \(C^{-1}\): for each certificate
vector \(\alpha\), with \(T_{\rm loc}(\alpha)=-\alpha^TB_{\rm at}\alpha\),

\[
\alpha^T(B_{\rm at}+C^{-1})\alpha<0
\]

is equivalent to the Schur condition

\[
\begin{pmatrix}
C&\alpha\\
\alpha^T&T_{\rm loc}(\alpha)
\end{pmatrix}\succ0.
\]

So the next concrete Gate 1 calculation is to compute or certify
\(B_{\rm at}\), \(C\), and \(\mathcal C_{\rm at}\), then prove either
\(\Lambda_{\rm at}<0\) directly or the stronger local-margin versus
capacity-load inequality above.

The row Gram \(C\) is now reduced to a finite-Hilbert formula.  In the
separated two-cut chart

\[
J=[\alpha_1,\beta_1]\cup[\alpha_2,\beta_2],
\qquad
R^2=\prod_{r=1}^2(z-\alpha_r)(z-\beta_r),
\]

for a row kernel \(k_\mu\), set \(f_\mu=-k_\mu'\).  If
\(\operatorname{PP}_\mu\) is the principal part of \(R f_\mu\) at all off-cut
poles, then the Riesz representer has Cauchy transform

\[
C_\mu(z)
=
f_\mu(z)
-
\frac{\operatorname{PP}_\mu(z)}{R(z)}
+
\frac{A_\mu+B_\mu z}{R(z)}.
\]

The two constants \(A_\mu,B_\mu\) are fixed by zero mass and fixed period:

\[
[z^{-1}]_\infty C_\mu=0,\qquad \Pi(C_\mu)=0.
\]

The density is the jump

\[
dg_\mu(x)
=
\frac{C_{\mu,-}(x)-C_{\mu,+}(x)}{2\pi i}\,dx,
\]

and hence

\[
\boxed{
C_{\mu\nu}
=
\int_J k_\mu(x)\,
\frac{C_{\nu,-}(x)-C_{\nu,+}(x)}{2\pi i}\,dx.
}
\]

Thus the capacity-load matrix is no longer abstract.  The remaining concrete
work is to plug the actual endpoint-certificate row kernels into this formula,
evaluate \(C\), and compare it against \(B_{\rm at}\) on
\(\mathcal C_{\rm at}\).

The actual separated-chart row kernels are

\[
1,\quad (x-u)^{-1},\quad (x-c)^{-1},\quad (x-v)^{-1},
\quad
L_-,\quad L_+,\quad \log\frac1{|c-x|}.
\]

With \(f=-k'\), their principal parts for \(R f\) are:

\[
\operatorname{PP}_{(x-s)^{-1}}
=
\frac{R(s)}{(z-s)^2}+\frac{R'(s)}{z-s},
\quad s\in\{u,c,v\},
\]

\[
\operatorname{PP}_{L_-}
=
-\frac{R(u)}{z-u}+\frac{R(c)}{z-c},
\qquad
\operatorname{PP}_{L_+}
=
-\frac{R(c)}{z-c}+\frac{R(v)}{z-v},
\]

\[
\operatorname{PP}_{\log(1/|c-x|)}
=
\frac{R(c)}{z-c}.
\]

The constant row has zero principal part.  The period coordinate is not an
arbitrary interior step kernel; it is handled by \(\Pi(C_\mu)=0\), or by a
gap-supported \(H^{1/2}\) kernel.  If the period jump enters the active support,
this separated Riesz-Gram chart is invalid and the case is routed to boundary.

The normalization constants are explicit.  With

\[
\widetilde C_\mu=f_\mu-\operatorname{PP}_\mu/R,
\qquad
m(T)=[z^{-1}]_\infty T,\quad p(T)=\Pi(T),
\]

\[
\begin{pmatrix}
m(R^{-1})&m(zR^{-1})\\
p(R^{-1})&p(zR^{-1})
\end{pmatrix}
\binom{A_\mu}{B_\mu}
=
-
\binom{m(\widetilde C_\mu)}{p(\widetilde C_\mu)}.
\]

Since \(R(z)\sim z^2\), the first row is \((0,1)\).  Writing
\(\pi_0=p(R^{-1})\), \(\pi_1=p(zR^{-1})\),
\(m_\mu=m(\widetilde C_\mu)\), and \(p_\mu=p(\widetilde C_\mu)\), one gets

\[
B_\mu=-m_\mu,\qquad
A_\mu=\frac{-p_\mu+m_\mu\pi_1}{\pi_0}
\]

provided \(\pi_0\ne0\).  If \(\pi_0=0\), the period normalization degenerates
and the point must be treated as chart-rank boundary or reparametrized.

The unnormalized transforms are explicit.  The constant row gives
\(\widetilde C_0=0\), so it is removed from the zero-mass Gram basis.  For
\(s\in\{u,c,v\}\),

\[
\widetilde C_s
=
\frac{R(z)-R(s)-R'(s)(z-s)}
{(z-s)^2R(z)}.
\]

For the split log rows,

\[
\widetilde C_-
=
-\frac1{z-u}+\frac1{z-c}
-
\frac1R\left(-\frac{R(u)}{z-u}+\frac{R(c)}{z-c}\right),
\]

\[
\widetilde C_+
=
-\frac1{z-c}+\frac1{z-v}
-
\frac1R\left(-\frac{R(c)}{z-c}+\frac{R(v)}{z-v}\right).
\]

For the anchor row,

\[
\widetilde C_{\log c}
=
\frac1{z-c}-\frac{R(c)}{(z-c)R(z)}.
\]

The mass coefficients are

\[
m(\widetilde C_s)=m(\widetilde C_-)=m(\widetilde C_+)=0,
\qquad
m(\widetilde C_{\log c})=1.
\]

Thus \(B_\mu=0\) for all Cauchy and split-log rows, while
\(B_{\log c}=-1\).  The remaining \(A_\mu\)'s are one-dimensional period
evaluations through the formula above.

In particular, putting \(p_\mu=p(\widetilde C_\mu)\), the final normalized
transforms are

\[
C_s=\widetilde C_s-\frac{p_s}{\pi_0R}\quad(s=u,c,v),
\qquad
C_\pm=\widetilde C_\pm-\frac{p_\pm}{\pi_0R},
\]

and

\[
C_{\log c}
=
\widetilde C_{\log c}
+
\frac1R\left(\frac{-p_{\log c}+\pi_1}{\pi_0}-z\right).
\]

Equivalently \(C_\mu=N_\mu/R\), where

\[
N_s=
\frac{R(z)-R(s)-R'(s)(z-s)}{(z-s)^2}
-\frac{p_s}{\pi_0},
\]

\[
N_-=
-\frac{R(z)-R(u)}{z-u}
+\frac{R(z)-R(c)}{z-c}
-\frac{p_-}{\pi_0},
\]

\[
N_+=
-\frac{R(z)-R(c)}{z-c}
+\frac{R(z)-R(v)}{z-v}
-\frac{p_+}{\pi_0},
\]

and

\[
N_{\log c}
=
\frac{R(z)-R(c)}{z-c}
+\frac{-p_{\log c}+\pi_1}{\pi_0}
-z.
\]

With

\[
d\Omega_R(x)=\frac{R_-(x)^{-1}-R_+(x)^{-1}}{2\pi i}\,dx,
\]

the Riesz density and Gram entries are

\[
dg_\mu(x)=N_\mu(x)d\Omega_R(x),
\qquad
C_{\nu\mu}=\int_J k_\nu(x)N_\mu(x)d\Omega_R(x).
\]

Thus the remaining Gate 1 sign is no longer an abstract PV or density-closure
issue.  It is the finite matrix test

\[
\alpha^T(B_{\rm at}+C^{-1})\alpha<0
\quad
\text{for all nonzero }\alpha\in\mathcal C_{\rm at},
\]

or equivalently

\[
\begin{pmatrix}
C&\alpha\\
\alpha^T&-\alpha^TB_{\rm at}\alpha
\end{pmatrix}\succ0
\quad(\alpha\in\mathcal C_{\rm at}).
\]

The finite local block \(B_{\rm at}\) is also explicit.  With
\(\lambda_-=1/X\), \(\lambda_+=-1/Y\),

\[
D^2E_-[\delta y]^2
=
-\frac2a\delta q\,\delta a+\frac q{a^2}(\delta a)^2
+A_2(\delta c-\delta a)^2,
\]

\[
D^2E_+[\delta y]^2
=
-\frac2b\delta q\,\delta b+\frac q{b^2}(\delta b)^2
+B_2(\delta c+\delta b)^2,
\]

and

\[
B_{\rm at}^{(y)}
=
\lambda_-D^2E_-+\lambda_+D^2E_+.
\]

For a row

\[
r=(r_0,r_u,r_c,r_v,r_-,r_+,r_{\log},r_\Pi),
\]

the branch-state lift is

\[
\delta q=-r_0,\qquad
\delta c=r_c/F_c,
\]

\[
\delta a=
\frac{-\ell_-r_0+A\,r_c/F_c+r_{\log}-r_-}{X},
\]

\[
\delta b=
\frac{-r_++\ell_+r_0-B\,r_c/F_c-r_{\log}}{Y}.
\]

Thus

\[
B_{\rm at}(r,r')=B_{\rm at}^{(y)}[T_y r,T_y r'].
\]

In the formal endpoint-length state basis
\((e_u^0,e_v^0,e_\zeta^0)\), this gives

\[
B_{\rm at}^0=
\begin{pmatrix}
\dfrac{q/a^2+A_2}{X}&0&\dfrac{q}{a^2X}\\[0.8em]
0&-\dfrac{q/b^2+B_2}{Y}&\dfrac{q}{b^2Y}\\[0.8em]
\dfrac{q}{a^2X}&\dfrac{q}{b^2Y}&
\dfrac{q}{a^2X}-\dfrac{q}{b^2Y}
\end{pmatrix}.
\]

The positive \(e_\zeta^0\) diagonal explains why the diagonal shortcut did
not work.  Gate 1 now depends on the coupled Schur test using both this local
block and the Riesz Gram matrix \(C\).

For an actual atomic Farkas certificate one must also include the point rows
\(x_k\in Z_0\).  The raw certificate kernel is

\[
k_{\mathfrak c}(t)
=
\eta\left(a\log\frac1{|u-t|}+b\log\frac1{|v-t|}\right)
+\sum_k w_k\log\frac1{|x_k-t|}
-\lambda\frac1{t-c},
\]

so

\[
f_{\mathfrak c}(z)
=
\eta\left(\frac a{z-u}+\frac b{z-v}\right)
+\sum_k\frac{w_k}{z-x_k}
-\frac{\lambda}{(z-c)^2}.
\]

The off-cut principal parts at \(u,v,c\) are explicit:

\[
\eta a\frac{R(u)}{z-u}
+\eta b\frac{R(v)}{z-v}
-\lambda\left(
\frac{R(c)}{(z-c)^2}+\frac{R'(c)}{z-c}
\right).
\]

The \(x_k\)-terms are on-cut singularities, so they must be handled by
symmetric regularized rows

\[
k_{x,\varepsilon}(t)
=
\frac12\log\frac1{|x+i\varepsilon-t|}
+\frac12\log\frac1{|x-i\varepsilon-t|}
\]

and the limit \(\varepsilon\downarrow0\).  For \(\varepsilon>0\) the point
principal part is

\[
\frac{w_k}{2}
\left(
\frac{R(x_k+i\varepsilon)}{z-(x_k+i\varepsilon)}
+\frac{R(x_k-i\varepsilon)}{z-(x_k-i\varepsilon)}
\right).
\]

Thus the final Gate 1 sign check is the regularized atomic Schur limit:

\[
\liminf_{\varepsilon\downarrow0}
\left[
B_{\rm at}(r_{\mathfrak c,\varepsilon},r_{\mathfrak c,\varepsilon})
+N_{\log,\varepsilon}(r_{\mathfrak c,\varepsilon},r_{\mathfrak c,\varepsilon})
\right]<0
\]

for every normalized non-boundary atomic certificate.  The fixed \(C\)-matrix
above is the off-cut subblock; the point rows enter through this regularized
limit.

The point-row limit has a positive blow-up.  For \(x\) in the interior of
\(Z_0\cap J\),

\[
\mathcal E_{\log}(g_{x,\varepsilon},g_{x,\varepsilon})
=
\log\frac1\varepsilon+O(1),
\]

while separated cross terms are \(O(1)\).  Hence for positive atomic weights,

\[
\mathcal E_{\log}\left(\sum_k w_kg_{x_k,\varepsilon},
\sum_k w_kg_{x_k,\varepsilon}\right)
=
\left(\sum_\chi W_\chi^2\right)\log\frac1\varepsilon+O(1),
\]

with \(W_\chi>0\) for every nonempty cluster.  Thus a certificate with a
nonzero \(Z_0\)-atomic part cannot be excluded by a finite negative
\(Q_{\rm eff}\) lift: the point-row Riesz load diverges with positive sign,
while \(B_{\rm at}\) remains finite.  Gate 1 therefore splits into:

\[
\zeta=0:\ \text{finite off-cut Schur test};
\qquad
\zeta\ne0:\ \text{prove a no-}Z_0\text{-atom theorem or return to raw sign}.
\]

The no-atom branch is finite.  If \(\zeta=0\), the certificate equations reduce
to

\[
\eta b_S-\lambda\rho_S=0.
\]

In the nondegenerate interior, \(\eta>0\), so after normalization

\[
b_S=\Lambda\rho_S.
\]

Hence no-atom fallback exists only on the collinearity locus
\(b_S\in\mathbb R\rho_S\).  When it exists, the lifted value is

\[
\Theta_\Pi^0=\eta(b_\Pi-\Lambda\rho_\Pi).
\]

Thus the no-atom subcase is excluded by the explicit finite test

\[
b_S=\Lambda\rho_S\Rightarrow b_\Pi-\Lambda\rho_\Pi<0.
\]

Equivalently, with

\[
\Delta_{\gamma\gamma'}=b_\gamma\rho_{\gamma'}-b_{\gamma'}\rho_\gamma,
\]

the no-atom branch is absent if some \(\Delta_{\gamma\gamma'}\ne0\).  If all
minors vanish and \(\rho_S\ne0\), then

\[
\Lambda=b_\gamma/\rho_\gamma
\]

for any nonzero \(\rho_\gamma\), and the branch is excluded by

\[
b_\Pi-\frac{b_\gamma}{\rho_\gamma}\rho_\Pi<0.
\]

If all minors vanish and \(\rho_S=b_S=0\), this is a repaired-column row-rank
boundary mode, not an interior no-atom certificate.

The remaining Gate 1 branch is exactly the \(\zeta\ne0\) branch: it requires a
no-\(Z_0\)-atom theorem for the reduced Farkas fallback, or a direct raw
first-order sign proof with the \(Z_0\)-atoms included.

The atom branch has an exact cone-envelope formulation.  Define

\[
\mathcal V_Z(x)=\binom{V_S(x)}{V_\Pi(x)}
\]

and

\[
\Phi_Z(y)=
\sup\left\{
\sum_kw_kV_\Pi(x_k):
\sum_kw_kV_S(x_k)=y,\quad w_k>0,\ x_k\in Z_0
\right\}.
\]

By conic Carathéodory, at most five points are needed.  For \(\eta>0\), after
normalizing \(\eta=1\), the \(Z_0\)-atomic obstruction exists exactly when

\[
\Phi_Z(-b_S+\Lambda\rho_S)\ge -b_\Pi+\Lambda\rho_\Pi
\]

for some real \(\Lambda\).  Therefore the atom branch is excluded exactly by

\[
\Phi_Z(-b_S+\Lambda\rho_S)<-b_\Pi+\Lambda\rho_\Pi
\qquad(\Lambda\in\mathbb R).
\]

The homogeneous case \(\eta=0\) is the analogous condition

\[
\Phi_Z(\lambda\rho_S)<\lambda\rho_\Pi
\qquad(\lambda\ne0).
\]

So the remaining hard statement is not a vague no-atom claim; it is this
lifted cone-envelope inequality for the explicit \(Z_0\)-columns.

The same criterion has a dual form.  Assuming the conic hull has no positive
lift recession ray

\[
\sum_kw_kV_S(x_k)=0,\qquad \sum_kw_kV_\Pi(x_k)>0,
\]

finite-dimensional conic duality gives

\[
\Phi_Z(y)=
\inf_{\theta\in\mathbb R^4}
\left\{
\theta\cdot y:\theta\cdot V_S(x)\ge V_\Pi(x)\ \forall x\in Z_0
\right\}.
\]

Thus for every \(\Lambda\) it is enough to construct
\(\theta_\Lambda\) with

\[
\theta_\Lambda\cdot V_S(x)\ge V_\Pi(x)\quad(x\in Z_0)
\]

and

\[
\theta_\Lambda\cdot(-b_S+\Lambda\rho_S)
<-b_\Pi+\Lambda\rho_\Pi.
\]

The homogeneous case is the same with

\[
\theta_\lambda\cdot(\lambda\rho_S)<\lambda\rho_\Pi.
\]

For any \(\theta\), set

\[
G_\theta(x)=\theta\cdot V_S(x)-V_\Pi(x).
\]

Then \(G_\theta\ge0\) on \(Z_0\) is the required dual majorant, and

\[
G_\theta'(x)=-\theta\cdot C_S(x)+C_\Pi(x).
\]

Using the repaired columns,

\[
Q(x)^2R(x)G_\theta'(x)
=
P_\theta(x),
\qquad
P_\theta=\kappa Q^2-\sum_\gamma\theta_\gamma H_\gamma^{\rm rep}.
\]

Thus the remaining proof is a one-dimensional sign problem for \(P_\theta\)
plus endpoint/contact values of \(G_\theta\).  If the required alternation
system for \(P_\theta\) degenerates, the case routes to Gate 3; if it has no
sign table, the \(Z_0\)-atomic branch is a concrete obstruction rather than a
closed case.

The strict lifted gap has to be checked with the same residual.  With
\[
G_\theta=\theta\cdot V_S-V_\Pi
\]
define
\[
G_\theta^{(b)}=\theta\cdot b_S-b_\Pi
=aG_\theta(u)+bG_\theta(v),
\qquad
G_\theta^{(c)}=\theta\cdot\rho_S-\rho_\Pi.
\]
Then the \(\eta>0\) strict dual inequality is equivalent to
\[
G_{\theta_\Lambda}^{(b)}
-\Lambda G_{\theta_\Lambda}^{(c)}>0,
\]
and the homogeneous strict dual inequality is equivalent to
\[
\lambda G_{\theta_\lambda}^{(c)}<0.
\]
Thus Gate 1 still reduces to a finite explicit task: construct the dual
majorants, prove the \(P_\theta\)-sign tables on \(Z_0\), and verify these
strict residual inequalities.  Equality is not an interior closure; it routes
to Gate 3 contact/boundary degeneration or remains a concrete Gate 1
obstruction.

The cone-envelope assembly is now formal.  If the no-atom collinearity test is
excluded or routed to boundary, and if the majorants
\(\theta_\Lambda,\theta_\lambda\) satisfy the \(Z_0\)-majorant and strict
residual inequalities above, then any raw augmented Farkas certificate
contradicts its own lifted nonnegativity.  Thus finite-dimensional Farkas plus
Carathéodory gives the reduced LP.

Equivalently:
\[
\boxed{
\text{majorants + strict residuals}
\Rightarrow
\text{RawAugmentedCircuitSign}
\Rightarrow
\text{reduced LP feasible.}
}
\]
The only remaining Gate 1 input is the explicit construction of those
majorants, i.e. the \(P_\theta\)-sign tables on \(Z_0\) and the strict boundary
/ anchor residual checks.  This is not yet an unconditional Gate 1 PASS.

Equivalently, define the dual majorant cone
\[
\mathcal D_Z=\{\theta:\theta\cdot V_S(x)-V_\Pi(x)\ge0\quad(x\in Z_0)\}.
\]
The affine atom branch is closed exactly by
\[
\sup_{\theta\in\mathcal D_Z}
\left(G_\theta^{(b)}-\Lambda G_\theta^{(c)}\right)>0
\qquad(\Lambda\in\mathbb R),
\]
and the homogeneous branch is closed exactly by
\[
\inf_{\theta\in\mathcal D_Z}G_\theta^{(c)}<0
\quad(\lambda>0),
\qquad
\sup_{\theta\in\mathcal D_Z}G_\theta^{(c)}>0
\quad(\lambda<0).
\]
Through \(Q^2R\,G_\theta'=P_\theta\), these are finite alternation/sign-table
problems for
\[
P_\theta=\kappa Q^2-\sum_\gamma\theta_\gamma H_\gamma^{\rm rep}.
\]
This is the remaining hard mouth: prove those margins, give an explicit signed
determinant/product formula implying them, or produce a genuine non-boundary
counter-certificate.

The abstraction alone cannot close this.  A four-point model with
\(V_S(x_i)=e_i\), \(V_\Pi(x_i)=0\), \(b_S=-(1,1,1,1)\), \(\rho_S=0\),
\(b_\Pi=1\), \(\rho_\Pi=0\) has a positive raw circuit
\[
b_S+\sum_iV_S(x_i)=0
\]
with lifted value \(1>0\).  Its dual cone is \(\theta_i\ge0\), and the affine
margin at \(\Lambda=0\) is \(-1\), not positive.  This does not refute the
actual moving-Schiffer chart; it proves that the remaining theorem must use
the explicit repaired columns \(H_\gamma^{\rm rep}\), not just abstract Farkas
or Schur-complement language.

So the precise missing theorem is:
\[
\boxed{\textbf{MovingSchifferMajorantSignTheorem}.}
\]
It must prove the two margin inequalities from
\[
H_\gamma^{\rm rep}
=QD\,\Delta_\gamma P-PD\,\Delta_\gamma Q-\frac12PQD_\gamma
\]
and the actual moving-chart system \(AX_\gamma=-r_\gamma\), either through an
explicit signed determinant/product formula for the \(P_\theta\)-alternation
system or through a direct solution of the two-cut extremal majorant problem.

There is now also a structural no-go for closing Gate 1 by quotient rank alone.
In the moving correction quotient
\[
\mathbb R[z]_{\le 2d+1}/D\mathbb R[z]_{\le 2d-3},
\]
the raw endpoint classes \(E_\gamma=PQD_\gamma\) form the endpoint
interpolation basis, and
\[
[Q^2]=
\sum_\gamma
\frac{Q(\gamma)}{P(\gamma)D_\gamma(\gamma)}[E_\gamma].
\]
So the period lift is already in the endpoint span modulo moving corrections.
Any strict first-order margin must therefore use the actual \(Z_0\)
contact/alternation structure of \(P_\theta\), not merely rank,
Schur-complement algebra, or the endpoint quotient.  If that sign theorem is
not proved, the route must switch to genuinely second-order data.

This is the current review position: the quotient obstruction is accepted, but
its scope is limited.  It kills quotient/rank/Schur-only closures; it does not
settle the non-quotient \(P_\theta\)-alternation route.  Any numerical or
symbolic probe of that route must use the repaired moving-chart columns and
the actual \(AX_\gamma=-r_\gamma\) rows, not the collapsed fixed-\(Q\)
endpoint table.

Gate 2 is the first-variation interface.  If the reduced LP produces an
equality-corrected perturbation with

\[
R_0=R_c=0,\qquad
B_{\rm safe}<0,\qquad
\widehat V<0\quad\text{on }Z_0,
\]

then the regularized Schiffer cutoffs and smooth bump correctors satisfy the
regularity hypotheses of Proposition 4.1.  The \(Z_0\)-negativity prevents new
positive components, and

\[
aX\,\delta L_{uv}=a\widehat V(u)+b\widehat V(v)=B_{\rm safe}<0.
\]

Thus the one-sided length derivative is negative and the candidate is not a
minimizer.

\[
\boxed{
\textbf{Gate 2 result: PASS.}
}
\]

Hence the first-variation interface is closed, but the rank-defect conclusion
still depends on Gate 1 supplying reduced LP feasibility:

\[
\boxed{
\text{RawAugmentedCircuitSign}
\Rightarrow
\text{compact }g=2\text{ rank-defect chamber ruled out.}
}
\]

Gate 3 is the boundary-routing proof obligation.  The
compactification uses coefficient convergence of \(D,Q\), weak convergence of
positive pole and endpoint atoms, \(L^1_{\rm loc}\) convergence of densities on
non-colliding cut interiors, Hausdorff convergence of \(Z_0\), and local
uniform convergence of potentials off the limiting support.  If none of the
following failures occurs, all discriminants, resultants, residues, density
signs, chart determinants, and anchor distances stay nonzero, so the point is
still in the regular non-pinched \(g=2\) chart.  Hence the boundary modes are
exhaustive:

\[
\begin{array}{c|c}
\text{mode} & \text{route} \\ \hline
\text{branch pinching} & \text{lower genus or endpoint atom} \\
Q\text{-pole collision / multiple pole} & \text{merged atom or lower pole stratum} \\
\text{density sign loss / residue zero} & \text{positivity boundary or atom deletion} \\
\text{endpoint atom creation} & \text{corrected }g=1\text{ / one-cut face} \\
Z_0\text{-collision or closure} & \text{active-set boundary / lower genus} \\
c\text{ hitting a forbidden set} & \text{anchor singular boundary}
\end{array}
\]

Branch pinching is handled by writing
\(D_n=(z-\alpha_n)(z-\beta_n)\widetilde D_n\).  Away from the collision point,
\(R_n/(z-\gamma)\to\widetilde R\).  The mass on the shrinking cut has weak
limit \(m_\gamma\delta_\gamma\), \(m_\gamma\ge0\); if \(m_\gamma=0\) the genus
drops, and if \(m_\gamma>0\) one gets the corrected endpoint-atom lower-genus
problem.  Colliding \(Q\)-poles merge positive Stieltjes atoms; zero residues
delete atoms; leaving the real interlacing class is density-sign loss.  A
vanishing density either cancels a branch factor or makes the regular chart
rank drop.  Endpoint atom creation is therefore already branch pinching or
pole-endpoint collision.  If \(Z_0\) collides with a boundary, Gate 2 remains
stable after regularization or a component pinches.  If \(c\) hits an endpoint,
pole, atom, or active zero, the anchor rows are singular and the state is in
the listed boundary/state-lift stratum.

\[
\boxed{
\textbf{Gate 3 status: proof route identified, compactness proof still required.}\quad
\text{The boundary cases are routed, but the compactness lemma is not yet
proof-grade.}
}
\]

To upgrade Gate 3 to PASS, the proof must still supply coefficient
convergence, weak convergence of atoms, \(L^1_{\rm loc}\) density convergence,
Hausdorff closure of active zero sets, local uniform convergence of potentials,
and a check that endpoint atoms or pole collisions do not create a new
counterexample stratum.  The remaining global gates are high-genus local-neck
reduction, Lemma R, and the one-cut upper construction.

Gate 4 gives the intended regular compact high-genus local-neck
lemma.  For a regular non-pinched chamber with \(g\ge3\), let \(K\) be the
actual KKT normal after the free-period quotient.  If \(K\) projected to zero
on every adjacent two-cut block, overlapping adjacent blocks would force
\(K=0\) on every cut, contradicting the nontrivial separating normal.
Therefore some adjacent block has a nonzero normal projection:

\[
J_i\cup J_{i+1}
= [\alpha_i,\beta_i]\cup[\alpha_{i+1},\beta_{i+1}].
\]

Freeze all rows outside this block.  The outside row matrix on smooth signed
bumps supported in outside positive-density interiors is invertible by the
regular chart hypothesis; if it is not, the full chart has dropped rank and
Gate 3 applies.  The Schur complement corrector
\[
\widehat G_{\rm loc}=G_{\rm loc}-\Psi_{\rm out}R_{\rm out}(G_{\rm loc})
\]
kills all frozen rows and is supported away from the neck.  The remaining rows
are precisely the \(g=2\) neck rows for endpoint columns
\(\alpha_i,\beta_i,\alpha_{i+1},\beta_{i+1}\).

The free-period quotient remains harmless in high genus: the filling variables
\(\tau_1,\ldots,\tau_{g-1}\) force all period multipliers in an extended
left-cokernel to vanish, so no independent pointwise sign-shifter is created.

The intended local block has three outcomes:

1. regular, giving the same positive-lineality/KKT-normal contradiction as the
   regular \(g=2\) case;
2. rank-defect non-pinched, giving the Gate 1 reduced LP and the Gate 2
   first-variation descent;
3. degenerate, routed by Gate 3 to lower genus, corrected \(g=1\), one-cut, or
   an already excluded \(g=2\) case.

\[
\boxed{
\textbf{Gate 4 status: proof route identified, global Schur complement proof
still required.}\quad
\text{The high-genus local-neck reduction is not yet proof-grade.}
}
\]

To upgrade Gate 4 to PASS, the proof must show that freezing outside rows and
using outside bump correctors gives a legitimate Schur complement whose local
rows are exactly the \(g=2\) neck rows, with the non-local logarithmic-capacity
tails fully accounted for.  If the Schur complement loses rank or changes
orientation, the case must be routed to Gate 3 boundary/lower genus.  Thus,
conditional on the Gate 1, Gate 3, and Gate 4 proof obligations, the
high-genus chambers are reduced to the one-cut/lower-genus branch or the local
\(g=2\) obstruction.

Gate 5 is the non-regular minimizer regularization proof obligation.
Let \(\mu\) be a compactified normalized minimizer with
\(|E_\mu|<M_{\rm oc}\).  Split multiple poles, separate coincident endpoints,
replace persistent zero residues by small positive residues, and add a small
smooth positive density floor on active cuts, compensating the added mass from
an existing positive atom or density interval.  The raw approximants converge
weakly to \(\mu\), their potentials converge locally uniformly off the
limiting support, and their Cauchy transforms converge in \(C^1\) near
non-colliding boundaries; hence \(|E_{\mu_\epsilon^{raw}}|\to |E_\mu|\).

If the finite row Jacobian is invertible, the implicit function theorem
restores mass, filling, pole-state, active-zero, endpoint, and anchor rows by
an \(O(\epsilon)\) correction.  Positivity and the strict inequality
\(|E_{\mu_\epsilon}|<M_{\rm oc}\) persist, giving a regular finite-gap
counterexample, contradicted by Gates 1--4.  If no invertible Jacobian exists,
some regular-chart determinant tends to zero; by Gate 3 this is precisely
branch pinching, pole collision, residue zero, density sign loss,
\(Z_0\)-collision, or anchor singularity.

The Proposition 4.1 inequalities are open under this approximation:
\(C^1\) convergence preserves boundary derivatives, uniform convergence near
\(Z_0\) preserves strict negativity, and the density floor preserves compact
lower bounds.

\[
\boxed{
\textbf{Gate 5 status: proof route identified, Lemma R still required.}\quad
\text{The regularization and row-restoration argument is not yet proof-grade.}
}
\]

To upgrade Gate 5 to PASS, the proof must still define the compactified
finite-gap charts and row-restoration map, prove the needed IFT hypotheses,
show positivity and strict length defect survive the correction, and prove that
Jacobian degeneration is exactly a Gate 3 boundary/lower-genus collapse.

Gate 6 defines the one-cut upper construction by equations.  For \(a\in(-1,1)\),
set

\[
s(a)=\sqrt{2(1+a)},\qquad
J(a)=\frac1\pi\int_a^1
\frac{\log(1/(1-t))}
{(t+1)\sqrt{(1-t)(t-a)}}\,dt,
\]

and choose

\[
A(a)=\frac{\log(4/(1-a))}{\log2+s(a)J(a)}.
\]

Then

\[
d\mu_a
=A(a)\delta_{-1}
+
\frac{x+1-A(a)s(a)}
{\pi(x+1)\sqrt{(1-x)(x-a)}}\,\mathbf1_{[a,1]}(x)\,dx.
\]

The standard mass identity gives \(\mu_a(\mathbb R)=1\), and
\(0<A(a)<\sqrt{(1+a)/2}\) gives positivity.  The admissible set is nonempty;
for instance \(a=1/2\) gives
\[
A(1/2)=\frac{\log8}{\log(7+4\sqrt3)}<\frac{\sqrt3}{2}.
\]
With

\[
R_a(z)=\sqrt{(z-a)(z-1)},\qquad R_a(z)\sim z,\quad R_a(z)<0\ (z<a),
\]

the exterior derivative is

\[
U_a'(z)=
-\frac{z+1-A(a)s(a)}{(z+1)R_a(z)}.
\]

This gives the monotonicity table on
\((-\infty,-1)\), \((-1,A(a)s(a)-1)\), and \((A(a)s(a)-1,a)\).  Since
\(A(a)<\sqrt{(1+a)/2}\), the middle minimum is strictly below zero, so there
are exactly two exterior zeros
\[
x_L(a)<-1<x_R(a)<A(a)s(a)-1<a,
\]
and

\[
E_{\mu_a}=(x_L(a),x_R(a))
\quad\text{up to endpoints}.
\]

Define

\[
M_{\rm oc}
=\inf_a \bigl(x_R(a)-x_L(a)\bigr)
\]

over this exact admissible one-cut parameter set.  The decimal is only a
numerical evaluation of these equations.  Every admissible \(a\) gives
\(|E_{\mu_a}|=x_R(a)-x_L(a)\), so an infimizing sequence gives

\[
\boxed{
\textbf{Gate 6 result: PROOF-GRADE PASS.}\quad
L_-\le M_{\rm oc}.
}
\]

The remaining step is final theorem assembly, but it is conditional until Gate
1, Gate 3, Gate 4, and Gate 5 are upgraded to proof-grade lemmas.

Gate 7 assembles the conditional theorem.  If the remaining proof obligations
are closed, Gates 1--5 imply the lower bound: any normalized minimizer with
\(|E_\mu|<M_{\rm oc}\) either regularizes to a regular finite-gap
counterexample, excluded by Gates 1--4, or collapses to a Gate 3
boundary/lower-genus branch.  The only surviving branch is the one-cut branch,
and \(M_{\rm oc}\) is defined as its exact infimum.  Under those conditional
inputs,

\[
L_-\ge M_{\rm oc}.
\]

Gate 6 gives the admissible one-cut construction with length \(M_{\rm oc}\),
so

\[
L_-\le M_{\rm oc}.
\]

Therefore

\[
\boxed{
\textbf{Gate 7 assembly: CONDITIONAL.}\quad
\text{If the remaining proof obligations are closed, then }L_- = M_{\rm oc}.
}
\]

Again, \(M_{\rm oc}\) is defined by the one-cut equations, not by the decimal.

## 8. Forum Positioning

Separate the two messages:

1. Finite-certificate progress:

   > Conditional on the standard normalized minimizer reduction, a
   > required-domain 560-block five-atom certificate gives
   > \(L_-\ge1.814600\).

2. Exact route:

   > The corrected endpoint-atom two-interval finite-gap route supports the
   > current one-cut candidate / provisional upper candidate, with the exact
   > value still defined by the one-cut equations rather than by the decimal.

Do not write "Erdős 1038 solved."  Do not merge the \(1.814600\) finite
certificate with the exact-value claim.
