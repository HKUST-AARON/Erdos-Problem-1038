# Erdős 1038: Detailed Route Ledger

This is the working ledger for the infimum side of Erdős Problem 1038.
It is intentionally more detailed than a forum note: it records what worked,
what failed, why it failed, and which route should be continued.

The main research goal is still the exact two-interval / finite-gap route.
The finite-atom bounds are important deliverables, but they are not the exact
infimum proof.

## Ledger Update Rule

Every future mathematical push on this project should update this file before
continuing to a new route.  The update must answer:

1. what was attempted;
2. what mathematical statement it was meant to prove;
3. whether it worked, failed, or only gave diagnostic evidence;
4. if it failed, the exact failure mechanism;
5. whether the route is active, retired, or kept as backup;
6. the next highest-priority pure mathematical task.

Do not replace this ledger by a short forum summary.  The short summary lives
in `1038_tao_ready_next_step_sup_closed.md`.  This file is meant to prevent
the proof search from circling back to already-retired directions.

## 0. Current Honest Status

For a monic real-rooted polynomial

\[
f(x)=\prod_{j=1}^n(x-r_j),\qquad r_j\in[-1,1],
\]

write

\[
\mu_f=\frac1n\sum_j\delta_{r_j},\qquad
U_\mu(x)=\int \log\frac1{|x-t|}\,d\mu(t),\qquad
E_\mu=\{x:U_\mu(x)>0\}.
\]

Then

\[
\{x:|f(x)|<1\}=E_{\mu_f}.
\]

The supremum side is closed:

\[
L_+=2\sqrt2.
\]

For the infimum side, the current exact-value candidate is

\[
M_*=x_R-x_L=1.8344304757626617\ldots,
\]

with

\[
x_L=-1.8081073680988165,\qquad x_R=0.02632310766384517.
\]

The current finite-atom lower-bound status in this repository is

\[
\boxed{L_-\ge1.814600}
\]

conditional on the standard Tao/natso normalized minimizer reduction

\[
\mu(\{-1\})\ge\frac12,\qquad
\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1].
\]

The exact equality

\[
L_-=M_*
\]

is not proved.

Thus the current honest interval is:

\[
\boxed{1.814600\le L_-\le 1.8344304757626617\ldots}
\]

with the lower endpoint conditional on the standard reduction and finite
certificate framework.

### 0.1 Frozen Exact-Route Statements

These are the statements the exact route is trying to prove.  Future work
should not blur them with the finite-atom progress bound.

**Theorem U: one-cut upper construction.**

\[
\boxed{L_-\le M_*}
\]

There exists an admissible one-cut measure

\[
\mu_{a_*}=A(a_*)\delta_{-1}
+f_{a_*}(x)\mathbf1_{[a_*,1]}(x)\,dx
\]

such that

\[
U_{\mu_{a_*}}=0\quad\text{on }[a_*,1],
\]

the two exterior zeros of \(U_{\mu_{a_*}}\) are

\[
x_L=-1.8081073680988165,\qquad
x_R=0.02632310766384517,
\]

and

\[
|E_{\mu_{a_*}}|=x_R-x_L=M_*.
\]

This is the matching construction.  It is not a proof of the lower bound.

**Theorem L: normalized exact lower bound.**

Under the standard Tao/natso normalized minimizer reduction,

\[
\mu(\{-1\})\ge\frac12,\qquad
\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1],
\]

there is no admissible minimizer with

\[
|E_\mu|<M_*.
\]

This is the hard theorem.  It requires global finite-gap classification, not
more local slab tuning.

**Final exact statement.**

Once Theorem U and Theorem L are both proved in the same normalization,

\[
\boxed{L_-=M_*=1.8344304757626617\ldots}.
\]

The current repository does not yet prove this final exact statement.

### 0.2 Current Review Decision

The 2026-05-06 route review is accepted with one implementation adjustment:
do not create a new "Exact Route Core Statements" file unless the project
later needs a separate note.  Under the local instruction "如无必要，勿增实体",
the core statements and priority queue live in this ledger and in the short
Tao-facing summary.

The technical decision is:

\[
\text{main effort}=\text{global finite-gap classification},
\]

not

\[
\text{main effort}=\text{small-eta/top-slab verifier tuning}.
\]

Small-eta and Krawczyk records stay in the ledger as diagnostics.  They are
not the route that can prove \(L_-\ge M_*\).

## 1. Duality Framework Used by the Finite Certificates

The working reduced support is

\[
S=\{-1\}\cup[0,1].
\]

The standard certificate mechanism is:

If \(\mu\) is supported on \(S\), \(E=E_\mu\), and a finite nonnegative measure
\(\nu\) satisfies

\[
\operatorname{supp}\nu\subset E^c,\qquad U_\nu(x)\ge0\quad(x\in S),
\]

then the symmetry identity

\[
\int U_\nu\,d\mu=\int U_\mu\,d\nu
\]

forces a contradiction unless the corresponding support/selector conclusion
holds.  All finite-atom packages below are ways of building such moving dual
witnesses and sweeping disjoint intervals.

Important caveat:

The finite-atom lower bounds do not by themselves prove the original
unreduced polynomial problem.  They rely on the standard minimizer reduction
to the normalized support/mass class.

## 2. Finite-Atom Lower-Bound Progression

This section records the lower-bound line.  It is not the exact-value route,
but it is the cleanest shareable progress.

### 2.1 Closed baseline: \(1.7875\)

The earlier three-atom certificate established, under the normalized support
reduction,

\[
L_-\ge1.7875.
\]

This used a fixed three-atom family

\[
\nu_a=\delta_a+A\delta_{a+M}+B\delta_{a+D}
\]

and a one-variable positivity check on the relevant interval.

What worked:

- simple finite-root check;
- clean disjoint sweep;
- useful baseline above the older informal lower bounds.

What limited it:

- fixed three-atom geometry has little room;
- it is not close to the conjectural \(M_*\).

### 2.2 \(1.7877\): reproducible but not the frontier

A fixed-parameter upgrade near

\[
M=1.7877
\]

passed a reproducible high-precision one-variable check.

Status:

- good numerical/certificate evidence;
- not the current strongest package;
- superseded by later finite-atom branches.

### 2.3 \(1.8\) route: split into forcing and tail

The \(1.8\) line split into:

1. forcing a longer base interval, such as \((-1.7,0)\) or \((-1.708,0)\);
2. adding a finite-atom tail block for the remaining length.

What worked:

- the tail positivity blocks could be made quite strong;
- the two-parameter forcing family eventually became certifiable.

What was wrong or incomplete at first:

- early versions treated grid evidence as too strong;
- the four-atom tail alone did not prove \(1.8\);
- the true bottleneck was the two-parameter forcing branch, not the
  one-variable tail positivity alone.

### 2.4 \(1.806304\): fixed five-atom tail certificate

The fixed five-atom package proved, under the same reduction,

\[
L_-\ge1.806304.
\]

Forcing branch:

\[
a\in[-1.708,-\sqrt2],\qquad b\in[0,1.836+a],
\]

with

\[
\nu_{a,b}=\delta_a+(1.395-b)\delta_b+C(a,b)\delta_{1.071-b},
\]

where \(C(a,b)>0\) is chosen by \(U_{\nu_{a,b}}(-1)=10^{-4}\).

Recorded verifier output:

```text
PASS
certified_boxes 5955
split_boxes 5954
worst_lower_bound 0.0000027692109390833507690739
max_depth 35
```

Tail block:

\[
a\in[-1.806304,-1.708],
\]

with shifts and weights

\[
\lambda_a=
\delta_a
+1.174168821\,\delta_{a+1.80650001}
+0.025921118\,\delta_{a+2.57053197}
+0.118647936\,\delta_{a+2.68367709}
+0.180553554\,\delta_{a+2.79017717}.
\]

The relevant one-variable potential was

\[
\begin{aligned}
V(y)={}&\log\frac1{|y|}
+1.174168821\log\frac1{|y-1.80650001|}
+0.025921118\log\frac1{|y-2.57053197|}\\
&+0.118647936\log\frac1{|y-2.68367709|}
+0.180553554\log\frac1{|y-2.79017717|}.
\end{aligned}
\]

Critical brackets:

```text
[0.77003805, 0.77003806]
[2.52642600, 2.52642601]
[2.60759965, 2.60759966]
[2.74249871, 2.74249872]
```

The high-endpoint margin was about

\[
4.054663365147\times10^{-6}.
\]

What worked:

- exact sweep arithmetic;
- forcing branch strong enough for \(1.806304\);
- internal Mathlib real-log checks for the six fixed one-variable points or
  brackets in `1038/FiveAtom1806304Mathlib.lean`;
- no Float and no `sorry` in those internal log checks.

What failed:

- the same fixed tail block fails at \(M=1.806305\);
- searches at \(M=1.807,1.808,1.810,1.815\) with five to seven fixed shifted
  atoms did not produce a positive full-domain tail certificate.

Reason:

The fixed global tail block is too rigid.  This led to the piecewise
required-domain construction below.

### 2.5 \(1.807100\): pole-free finite-atom package

The repository records a separate finite-atom package at

\[
M=1.807100.
\]

Relevant folders:

```text
finite_atoms/five_atom_1807100/
finite_atoms/route_1807100/
```

This package includes the pole-free interval-box certificate, exact arithmetic
checks, and route bookkeeping for the tail sweep.

Status:

- stronger than \(1.806304\);
- superseded by the \(1.814600\) piecewise required-domain branch;
- still useful as a cleaner intermediate package.

### 2.6 Current strongest finite package: \(1.814600\)

The current strongest finite-atom package is

\[
\boxed{M=1.814600}
\]

using a piecewise five-atom tail with \(K=560\) blocks.

Relevant files and folders:

```text
README.md
1038/README.md
1038/certificates/piecewise_five_atom_181460_560blocks_required_domain_certificate.md
1038/certificates/piecewise_five_atom_181460_560blocks_required_domain_certificate.json
finite_atoms/piecewise_five_atom_181460_560/
finite_atoms/route_181460_560/
```

The route uses the same forcing split:

\[
B=1.708,\qquad M=1.814600.
\]

The tail contribution is

\[
M-B=1.814600-1.708=0.106600.
\]

The closing arithmetic is

\[
1.708+(1.814600-1.708)=1.814600.
\]

#### Required-domain interpretation

This is the crucial point.

The \(1.814600\) package is not a full \([-1,1]\) positivity certificate.
It is a required-domain certificate under the normalized support condition

\[
\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1].
\]

For each block \(a\in[-A,-C]\), the dual atom sum only needs

\[
U_{\lambda_a}(x)>0\qquad x\in\{-1\}\cup[0,1].
\]

In the variable \(y=x-a\), this corresponds to the two disjoint required
domains

\[
[C-1,A-1]\qquad\text{and}\qquad[C,A+1].
\]

The middle interval

\[
(A-1,C)
\]

corresponds to \(x\in(-1,0)\).  This is not part of the normalized support
except for the handled endpoint \(x=-1\).  Some blocks are negative in this
middle overcheck region; this is recorded and is not used by the argument.

This distinction is essential.  Do not describe the \(1.814600\) package as a
full \([-1,1]\) positivity certificate.

#### Certificate data

The piecewise shifts are:

```text
d1 = 1.8146001
d2 = 2.55506
d3 = 2.675215475
d4 = 2.781815575
```

For each block,

\[
\lambda_a=\delta_a+w_1\delta_{a+d_1}
+w_2\delta_{a+d_2}
+w_3\delta_{a+d_3}
+w_4\delta_{a+d_4}.
\]

The generated certificate records:

```text
M = 1.814600
K = 560
overall_worst_required.value = 9.534343713646365e-06
all_required_blocks_ok = true
num bad required blocks = 0
```

The irrelevant middle gap may have negative diagnostic values.  This is not a
failure of the required-domain argument.

#### Formalization and verification status

The Lean files formalize:

- exact geometry;
- all 560 block weights;
- block coverage of `[1.708,1.814600]`;
- the required-domain map from normalized support to
  \([C-1,A-1]\cup[C,A+1]\);
- non-negative finite-atom selector;
- route arithmetic and tail sweep.

The 560 individual one-variable log positivity blocks are generated Lean
chunks under:

```text
finite_atoms/piecewise_five_atom_181460_560/lean/box_list_chunks/
```

Each chunk stores rational boxes and proves the corresponding required-domain
log positivity theorem via the shared `Real.log` bridge.

The independent Python required-domain checker reports the same margin.

Repro commands recorded in the package:

```bash
python3 scripts/verify_piecewise_181460_560.py
bash scripts/verify_piecewise_181460_560_test.sh
```

Full Lean/chunk check:

```bash
MATHLIB_WORKSPACE=/path/to/mathlib PIECEWISE_BOX_JOBS=8 \
  finite_atoms/piecewise_five_atom_181460_560/scripts/check_lean_box_list_chunks.sh
```

Repository-level finite-atom check:

```bash
MATHLIB_WORKSPACE=/path/to/mathlib finite_atoms/check_all.sh
```

#### Status of \(1.814600\)

This is the current strongest finite-atom lower-bound package in the
repository:

\[
\boxed{L_-\ge1.814600}
\]

conditional on the standard normalized-support reduction and the finite-atom
duality/sweep framework.

It is not a proof of the exact value \(M_*\), and it is not a full
unconditional proof of the original polynomial problem.

## 3. Corrected Two-Interval Exact Route

The exact route is the corrected endpoint-atom two-interval finite-gap route.
This is the route that could plausibly lead to the exact value \(M_*\).

For

\[
E_\varepsilon=(x_L+\varepsilon,x_R)\cup(1-\varepsilon,1),
\]

put

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

With

\[
F(z)=\int\frac{d\lambda(t)}{z-t},\qquad U_\lambda'(x)=-F(x),
\]

the dual measure is

\[
\lambda
=m_\ell\delta_\ell+m_r\delta_r+m_1\delta_1
+g(x)\mathbf1_{[\alpha,\beta]}(x)\,dx.
\]

The endpoint atom is forced:

\[
m_1=
\frac{(1+A)\sqrt{(1-\alpha)\varepsilon}}{(1-\ell)(1-r)}>0.
\]

Target geometry to be proved for the active chamber:

\[
\ell<-1<r<\alpha<\beta<1,
\]

together with the corresponding sign inequalities on \(A\).  Under the
correct sign chart, residues and density have the expected positive signs, and
the branch is governed by the two contact equations:

\[
U_\lambda(\alpha)=0,\qquad U_\lambda(-1)=0.
\]

### 3.1 Retired old ansatz

The no-endpoint-atom ansatz is retired.

Why:

Since \(z=1\) is a simple pole of the corrected \(F\), the residue \(m_1\) is
positive in the target geometry.  Omitting \(m_1\delta_1\) removes a required
positive atom and changes the boundary-layer cancellation.

Do not revive the no-endpoint-atom route.

## 4. Two-Interval Attempt Record

This section keeps the local computational/proof attempts so the same bad
routes are not repeated.

### 4.1 Fixed epsilon skeleton

Fixed rows:

```text
epsilon = 0.002, 0.001, 0.0005, 0.0002, 0.0001, 0.00005
```

Status:

```text
OVERALL TWO-INTERVAL SKELETON CHECK: PASS
(6 rows; tamper self-test PASS 6 cases; verifier integrity only, not a math proof)
```

Meaning:

- strong evidence for the implemented corrected branch at fixed epsilon;
- not a continuum theorem in \(\varepsilon\);
- not a global proof of \(L_-=M_*\).

### 4.2 Sampled adjacent slab diagnostics

Sampled adjacent slabs passed:

```text
[0.00005,0.0001]  PASS
[0.0001, 0.0002]  PASS
[0.0002, 0.0005]  PASS
[0.0005, 0.001]   PASS
[0.001,  0.002]   PASS
```

Why this is not proof:

- center correction was sampled;
- \(DK\) dependence on \(\eta=\sqrt\varepsilon\) was sampled;
- no outward-rounded continuum enclosure over the whole slab.

Use this only as branch evidence.

### 4.3 Eta-uniform interval Krawczyk closure

This is the local certificate gap for the two-interval branch.

What closed after tuning:

```text
0.00005:0.0001   PASS, radius=0.0003,  eta=224
0.0001:0.0002    PASS, radius=0.0003,  eta=224
0.0002:0.0005    PASS, radius=0.00029, eta=1344
0.0005:0.001     PASS, radius=0.0006,  eta=1344
```

What remains open in this verifier:

```text
0.001:0.002      open
```

Representative failed top-slab runs:

```text
slab=0.001:0.002, radius=0.0008,  eta=1344  FAIL, margin=-2.030082e-04
slab=0.001:0.002, radius=0.00065, eta=2688  FAIL, margin=-1.115617e-04
slab=0.001:0.002, radius=0.0009,  eta=2688  FAIL, margin=-1.682608e-04
```

Diagnosis:

- simply increasing eta subdivisions is not enough;
- the top slab needs a better continuation/center model or a row-to-row split;
- this is a certificate-technology gap, not a mathematical disproof of the
  branch.

### 4.4 Small-eta singular endpoint

This should not be the main route.

Observed bad interval behavior:

```text
whole-slab Div2 joint layer: [+/- 39.1]
```

Observed true scale from sampled derivative diagnostics:

```text
B=+0.01: max_abs_derivative=1.712468090857, integral_width_bound=0.005015702912464
B=-0.01: max_abs_derivative=1.694222774641, integral_width_bound=0.004962263618518
```

What this means:

- the branch is not dying at small eta;
- the interval expression has artificial dependency;
- the proof-grade local lemma would be a direct shared-variable derivative
  bound
  \[
  |B'(s)|\le2.
  \]

Why it is deprioritized:

Even if this local lemma closes, the exact value still needs the global
finite-gap classification.  So small eta is a backup local task, not the
main mathematical route.

### 4.5 Residue-log and paired-pole experiments

Useful lesson:

The endpoint atom and continuous density must be combined at the residual
level before interval evaluation.  Splitting terms too early loses the
removable \(\eta\)-factors.

What failed:

- direct Arb intervalization of \(DK\) gives overly wide boxes;
- eta-divided residue-log primitives match point values but remain too wide
  when each preimage/residue/log factor is divided separately;
- paired smooth-pole grouping helped diagnose the cancellation but did not by
  itself produce a proof-grade interval enclosure.

Correct replacement:

Work with a shared \(s=t\eta\) derivative or a fully combined residual-level
kernel before interval evaluation.

## 5. Main Exact-Value Route

The exact-value proof should be organized globally, not around small-eta
slabs.

### 5.1 Upper bound

The one-cut primal candidate should supply

\[
L_-\le M_*.
\]

This still needs a clean written proof in the same normalization as the lower
bound.  It is conceptually the easier side.

### 5.2 Lower bound

To prove

\[
L_-\ge M_*,
\]

one must show that every regular counterexample with

\[
|E|<M_*
\]

either:

1. lies on the corrected one-cut/two-interval finite-gap branch;
2. pinches or degenerates to a lower-genus branch;
3. violates residue/density positivity or the real interlacing constraints.

This is the global interlacing-collapse / topology lemma.

This is the real mathematical gap.

## 6. Compact Non-Pinched \(g=2\) Ledger

After pinching reductions, the first genuine escape is a compact non-pinched
\(g=2\) chamber.

This route produced several useful corrections.

### 6.1 Naive three-kernel determinant: wrong

Old idea:

Use the three kernels

\[
1,\qquad (x-c)^{-1},\qquad \int_u^v\frac{ds}{x-s}.
\]

Why wrong:

The factor \(c-s\) changes sign when \(s\) crosses \(c\).  The determinant sign
is not uniform.

Do not use this determinant as the compact proof.

### 6.2 Split-kernel repair: useful

Correct split:

\[
L_-=\int_u^c\frac{ds}{x-s},\qquad
L_+=\int_c^v\frac{ds}{x-s}.
\]

What worked:

The oriented split determinant has the right sign behavior on separated real
ovals.  This remains useful for variation-diminishing arguments.

What it does not do alone:

It does not automatically derive the KKT row ledger.  It only gives a sign
tool once the correct rows are known.

### 6.3 Pure-\(q\) Schur scalar: insufficient

Old target:

Reduce the compact obstruction to one scalar \(\mathfrak S_q\).

Why insufficient:

\(\mathfrak S_q\) is only a sufficient pivot.  The full stationarity Schur
complement also sees endpoint derivative and field-jet terms.

Correct target:

Use the full field-jet Schur functional.

### 6.4 Rank-six Schur target: dimensionally wrong

Old target:

Show a rank-six Schur row family after adding the objective row.

Why wrong:

After eliminating local variables, the KKT structure selects a
two-dimensional cokernel subspace, not six independent density moment rows.

Correct target:

Compute the two-dimensional KKT cokernel subspace and show no nonzero element
has the admissible compact sign pattern.

### 6.5 First-order block is not the Hessian

Old mistake:

The first-order local matrix \(A\) was treated as if it already supplied the
second-variation obstruction.

Why wrong:

The compact closure needs a reduced Hessian / bordered Schur complement, not
just first-order stationarity.

Correct target:

Derive the reduced tangent Hessian \(G\) from the finite-gap Cauchy-transform
energy after imposing the KKT constraints.

### 6.6 Current compact hard mouth

The compact \(g=2\) branch should now be attacked through:

1. exact KKT row ledger;
2. period row accounted for explicitly;
3. two-dimensional cokernel basis;
4. reduced Hessian \(G\);
5. curvature clamp / Wronskian sign contradiction.

This is the most serious mathematical route after the finite certificate
work.

## 7. Retired or Deprioritized Lines

Do not continue these as active main routes:

1. No-endpoint-atom two-interval ansatz.
   It omits a forced positive residue at \(z=1\).

2. Brute-force small-eta slab subdivision.
   It treats a global mathematical problem as a local verifier problem.

3. Whole-slab `Div2` intervalization.
   It creates artificial eta dependency and huge boxes.

4. Sampled-center correction as proof.
   It is diagnostic only.

5. Naive three-kernel compact determinant.
   It misses the split at \(c\).

6. Pure-\(q\) Schur scalar as the final compact target.
   It is insufficient.

7. Rank-six Schur conclusion.
   The corrected object is the KKT cokernel and reduced Hessian.

8. Full \([-1,1]\) positivity demand for the \(1.814600\) tail.
   The correct statement is required-domain positivity under normalized
   support; the middle gap corresponds to \(x\in(-1,0)\) and is not needed.

## 8. Current Priorities

### Priority A: exact route global classification

The main route now runs:

\[
\text{minimizer}
\Rightarrow
\text{finite-gap KKT}
\Rightarrow
\text{pinching/degeneration}
\Rightarrow
\text{\(F(c)\)-branch repair}
\Rightarrow
\text{compact }g=2\text{ exclusion}
\Rightarrow
\text{global closure}.
\]

The next mathematical deliverables, in order, are:

1. write Theorem U as a clean one-cut upper construction;
2. write the corrected \(g=1\) endpoint-atom branch as a proposition;
3. prove the pinching / degeneration lemma before further slab work;
4. prove the branch-parametrized \(F(c)\) repair:
   \(F(c)=0\) is a branch equation and the state lift uses
   \(A=(E_-,E_+,M,F)\), while \(\Pi\) restricts density directions;
5. derive the compact \(g=2\) KKT row ledger with the period row accounted
   for explicitly;
6. compute the bordered reduced Hessian Schur complement
   \[
   G_0
   =
   H_{\xi\xi}
   -
   \begin{pmatrix}H_{\xi y}&A_\xi^T\end{pmatrix}
   \begin{pmatrix}
   H_{yy}&A_y^T\\
   A_y&0
   \end{pmatrix}^{-1}
   \begin{pmatrix}
   H_{y\xi}\\
   A_\xi
   \end{pmatrix}
   \]
   on actual density perturbations satisfying \(\delta\Pi=0\);
7. prove the density-to-row quotient / realization lemma
   \[
   \ker(\rho|_{\mathcal X_\Pi})\subset\operatorname{Rad}(G_{\rm br}),
   \]
   or keep the compact obstruction directly on the row-map image
   \(V=\rho(\mathcal X_\Pi)\);
8. prove the five scalar identities
   \[
   e_u^TMe_u=\lambda a,\quad
   e_v^TMe_v=\lambda b,\quad
   e_\zeta^TMe_\zeta=\lambda Q_c,
   \]
   \[
   e_u^TMe_\zeta=-\frac{\lambda}{2}\Gamma(c-u),\quad
   e_v^TMe_\zeta=\frac{\lambda}{2}\Gamma(v-c);
   \]
9. use them to prove the curvature clamp and Wronskian/sign-pattern
   contradiction for compact non-pinched \(g=2\);
10. formulate high-genus induction as a local \(g=2\)-type neck obstruction;
11. only then attack the regularity-removal layer.

### Priority B: preserve finite certificate records accurately

The finite lower bound currently to cite is

\[
\boxed{L_-\ge1.814600}
\]

not \(1.806304\).

The wording must include:

- conditional on standard Tao/natso reduction;
- required-domain certificate, not full \([-1,1]\) positivity;
- 560-block generated certificate;
- exact value still open.

This is a shareable progress result, but it is not the exact-value proof.

### Priority C: avoid local verifier traps

Small eta and top-slab Krawczyk work are kept only as local attempt records.
They should not consume the main proof strategy unless the global route later
requires a specific local lemma from that branch.

## 9. Pure Mathematical Next-Step Ledger

This section is the active mathematical queue.  It should be updated every
time the route advances.  It deliberately avoids verifier engineering unless a
specific certificate is needed to support a mathematical lemma.

### 9.1 Exact upper construction at \(M_*\)

Target theorem:

\[
\boxed{L_-\le M_*}.
\]

The expected extremal is the one-cut primal candidate.  In the current
normalization, write it as

\[
\mu_a=A(a)\delta_{-1}+f_a(x)\mathbf1_{[a,1]}(x)\,dx,
\]

where

\[
f_a(x)=
\frac{x+1-A(a)\sqrt{2(1+a)}}
{\pi(x+1)\sqrt{(1-x)(x-a)}}.
\]

The required upper-bound proof should show:

1. \(\mu_a\ge0\) and has the correct total mass at the critical parameter
   \(a=a_*\);
2. \(U_{\mu_a}=0\) on \([a,1]\);
3. the two exterior zeros of \(U_{\mu_{a_*}}\) are exactly
   \[
   x_L=-1.8081073680988165,\qquad x_R=0.02632310766384517;
   \]
4. the positive set has length
   \[
   |E_{\mu_{a_*}}|=x_R-x_L=M_*.
   \]

This is conceptually the easiest exact-route task.  It should be written
cleanly because the lower-bound proof must use the same normalization.

Current gap in this statement:

\(A(a)\) is named but not yet defined.  Total mass does not determine it.  The
missing scalar condition is the level normalization \(U_{\mu_a}=0\) on the
cut.

Set

\[
s=\sqrt{2(1+a)},\qquad c=A(a)s.
\]

Then

\[
d\mu_a=A(a)\delta_{-1}
+\frac{x+1-c}{\pi(x+1)\sqrt{(1-x)(x-a)}}\mathbf1_{[a,1]}(x)\,dx.
\]

The mass identity is

\[
\frac1\pi\int_a^1
\frac{dx}{(x+1)\sqrt{(1-x)(x-a)}}=\frac1s,
\]

so the continuous mass is \(1-A(a)\), and total mass is automatically one.
The scalar normalization can be imposed as

\[
U_{\mu_a}(1)=0.
\]

Equivalently,

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

With

\[
y=\sqrt{\frac{1+a}{2}},
\]

the expected closed form is

\[
A(a)=
\frac{\log(4/(1-a))}
{\log((1+y)/(1-y))}.
\]

This closed-form evaluation still needs to be included in the proof, or
replaced by an exact defining equation plus certified interval enclosures.

Positivity of the candidate requires

\[
0\le A(a)\le\sqrt{\frac{1+a}{2}}.
\]

If the normalized lower-bound class is required for the same construction,
one also has to track

\[
A(a)\ge\frac12.
\]

For \(z\notin[a,1]\), with

\[
R_a(z)=\sqrt{(z-a)(z-1)},\qquad R_a(z)\sim z,
\]

the derivative should be

\[
U'_{\mu_a}(z)=-
\frac{z+1-c}{(z+1)R_a(z)}.
\]

This gives the monotonicity needed to prove that the only exterior zeros are
\(x_L,x_R\), once those zeros are defined by exact equations or certified
intervals.

### 9.2 Corrected \(g=1\) finite-gap branch

Target local theorem:

\[
\boxed{
\text{Every regular one-cut/two-interval extremal dual has the corrected
endpoint-atom Cauchy form.}
}
\]

Assume the active dual zero set is

\[
Z_0=[\alpha,\beta],
\]

with boundary poles

\[
\ell,\ r,\ 1,\qquad \ell<-1<r<\alpha<\beta<1.
\]

If

\[
F(z)=\int\frac{d\lambda(t)}{z-t}
\]

and \(U_\lambda=0\) on \([\alpha,\beta]\), then

\[
\operatorname{Re}F_+(x)=0\qquad(\alpha<x<\beta).
\]

With

\[
R(z)=\sqrt{(z-\alpha)(z-\beta)},\qquad R(z)\sim z,
\]

the quotient \(F/R\) has no jump across the cut.  Therefore

\[
F(z)=
c\frac{z+A}{(z-\ell)(z-r)(z-1)}
\sqrt{(z-\alpha)(z-\beta)}.
\]

The positive scalar \(c>0\) is a normalization constant.  It was suppressed in
earlier shorthand formulas but should be kept in the proposition statement.

The residues and density are

\[
m_\ell=
c\frac{(\ell+A)R(\ell)}{(\ell-r)(\ell-1)},\quad
m_r=
c\frac{(r+A)R(r)}{(r-\ell)(r-1)},\quad
m_1=
c\frac{(1+A)R(1)}{(1-\ell)(1-r)},
\]

and

\[
g(x)=
-\frac{c}{\pi}
\frac{x+A}{(x-\ell)(x-r)(x-1)}
\sqrt{(x-\alpha)(\beta-x)}.
\]

With the branch convention \(R(x)<0\) for \(x<\alpha\) and \(R(1)>0\), the
local sign chamber is

\[
\boxed{-r<A<-\ell}
\]

under

\[
\ell<-1<r<\alpha<\beta<1.
\]

Indeed \(A>-r\) implies \(x+A>0\) on \((\alpha,\beta)\), and \(A<-\ell\)
gives the left residue sign.  This proves local residue/density positivity for
the corrected \(g=1\) algebra.

The global positivity check then reduces to

\[
U_\lambda(\alpha)=0,\qquad U_\lambda(-1)=0.
\]

Open point:

The local algebra is in good shape.  The missing exact proof is not here; it is
the global classification showing that all potential counterexamples reduce
to this branch or to a lower-genus degeneration.

### 9.3 Global interlacing-collapse theorem

Target theorem:

\[
\boxed{
|E|<M_*
\quad\Longrightarrow\quad
\text{no positive finite-gap counterexample survives outside the corrected }
g=1\text{ branch.}
}
\]

More explicitly, let \(F\) be a positive Stieltjes finite-gap transform for a
regular minimising counterexample.  If \(E\) has more than the main component
and the endpoint split-off component, then at least one of the following must
hold:

1. a residue or density is negative;
2. a gap-pinching / Schiffer variation decreases \(|E|\);
3. the configuration degenerates to the corrected \(g=1\) branch.

The controlling monotonicity is

\[
F'(x)=-\int\frac{d\lambda(t)}{(x-t)^2}<0
\]

on every real component disjoint from \(\operatorname{supp}\lambda\).  Hence
each extra positive component can contain only one zero of \(F\), and that
zero must interlace with boundary poles and cut endpoints.

This theorem is the true exact-value bottleneck.  The current local and
finite-atom work does not replace it.

### 9.4 Pinching / degeneration lemma

Target lemma:

\[
\boxed{
\text{Endpoint pinching of a positive finite-gap transform lowers genus and
does not create a new extremal family.}
}
\]

For \(g=2\), consider

\[
F_n(z)=
\frac{P_n(z)}{Q_n(z)}
\sqrt{
(z-\alpha_{1,n})(z-\beta_{1,n})
(z-\alpha_{2,n})(z-\beta_{2,n})
}.
\]

Suppose adjacent branch points pinch:

\[
\beta_{1,n}\to\gamma,\qquad \alpha_{2,n}\to\gamma.
\]

Then locally

\[
\sqrt{(z-\beta_{1,n})(z-\alpha_{2,n})}
\longrightarrow z-\gamma.
\]

After cancelling removable pole/zero factors, the limit has the lower-genus
form

\[
\boxed{
F_\infty(z)=
\frac{P_\infty(z)}{Q_\infty(z)}
\sqrt{(z-\alpha_1)(z-\beta_2)}
}
\]

possibly with a non-negative endpoint atom recorded in \(Q_\infty\).

Cases to record in the proof:

1. no pole of \(Q_n\) pinches at \(\gamma\);
2. a pole \(p_n\) of \(Q_n\) pinches at \(\gamma\);
3. a zero of \(P_n\) pinches at \(\gamma\).

In all cases, positivity of residues and density is closed under weak limits.
Thus a pinched \(g=2\) candidate is a \(g=1\) candidate with possible endpoint
atoms, not a new compact extremal.

This lemma should be written before further local slab work.

### 9.5 First high-genus target: compact non-pinched \(g=2\)

After pinching reductions, the first true escape is a compact non-pinched
\(g=2\) chamber.

Model active zero set:

\[
Z_0=[\alpha_1,\beta_1]\cup[\alpha_2,\beta_2],
\qquad
\alpha_1<\beta_1<\alpha_2<\beta_2.
\]

Finite-gap transform:

\[
F(z)=
\frac{P(z)}{Q(z)}
\sqrt{(z-\alpha_1)(z-\beta_1)(z-\alpha_2)(z-\beta_2)}.
\]

For a first extra positive component

\[
I=(u,v)\subset(0,1),\qquad \mu|_I=q\delta_c,\qquad u<c<v,
\]

the primal stationarity condition is

\[
(c-u)U_\mu'(u)=(v-c)|U_\mu'(v)|.
\]

The dual complementarity condition is

\[
F(c)=0,\qquad F'(c)<0.
\]

The concrete \(g=2\) inequality is

\[
\boxed{
|E|=(R_0-L_0)+(v-u)\ge M_*.
}
\]

The compact branch is closed if one proves that no positive non-pinched
finite-gap point with \(|E|<M_*\) satisfies the KKT equations, positivity, and
interlacing constraints simultaneously.

### 9.6 Extra-component stationarity identities

On an extra component \(I=(u,v)\) with atom \(q\delta_c\), write

\[
U_\mu(x)=q\log\frac1{|x-c|}+W(x),
\]

where \(W\) is the external field from all mass outside \(I\).  Then

\[
U_\mu'(u)=\frac{q}{c-u}+W'(u),
\qquad
U_\mu'(v)=-\frac{q}{v-c}+W'(v).
\]

The stationarity equation gives the exact cancellation:

\[
\boxed{
(c-u)W'(u)+(v-c)W'(v)=0.
}
\]

Endpoint zero equations give

\[
W(u)=q\log(c-u),\qquad W(v)=q\log(v-c),
\]

hence

\[
\boxed{
W(v)-W(u)=q\log\frac{v-c}{c-u}.
}
\]

Since

\[
W''(x)=\int_{\mathbb R\setminus I}\frac{d\mu(t)}{(x-t)^2}>0
\qquad(x\in I),
\]

\(W'\) is strictly increasing and the escaping component has a rigid convex
shape.  This is the first pure mathematical input toward ruling out compact
\(g=2\).

### 9.7 KKT row ledger for compact \(g=2\)

The compact KKT calculation must be written exactly, not with vague "rank"
language.

Let the density variation be

\[
d\eta(x)=G(x)\omega(x)\,dx
\]

on the two real ovals after clearing the positive weight

\[
\omega(x)=\frac1{|Q(x)|^2\sqrt{|D(x)|}}.
\]

Local variables:

\[
q,\qquad a=c-u,\qquad b=v-c,\qquad c.
\]

Active local equations:

\[
E_-=0,\qquad E_+=0,\qquad F(c)=0,\qquad S=0.
\]

The six local jet rows are expected to be

\[
\boxed{
\begin{array}{rcl}
R_0(G)&=&\displaystyle\int_J G(x)\omega(x)\,dx,\\[0.7em]
R_u(G)&=&\displaystyle\int_J \frac{G(x)\omega(x)}{x-u}\,dx,\\[0.7em]
R_c(G)&=&\displaystyle\int_J \frac{G(x)\omega(x)}{x-c}\,dx,\\[0.7em]
R_v(G)&=&\displaystyle\int_J \frac{G(x)\omega(x)}{x-v}\,dx,\\[0.7em]
R_-(G)&=&\displaystyle\int_J L_-(x)G(x)\omega(x)\,dx,\\[0.7em]
R_+(G)&=&\displaystyle\int_J L_+(x)G(x)\omega(x)\,dx.
\end{array}
}
\]

where

\[
L_-(x)=\int_u^c\frac{ds}{x-s},
\qquad
L_+(x)=\int_c^v\frac{ds}{x-s}.
\]

The period row is real and must be included:

\[
\pi_0(x)=
\begin{cases}
1,&x\in I_1,\\
-\theta_{\rm per},&x\in I_2,
\end{cases}
\qquad \theta_{\rm per}>0.
\]

Correction already made:

The period row is not generally in the six local jet span.  It is a seventh
KKT bookkeeping row, but the six local rows are the ones used for the oriented
Chebyshev determinant.

### 9.8 Correct Schur/cokernel target

Let the augmented rows be ordered as

\[
(\mathcal L,M,F_c,E_-,E_+,S),
\]

and let

\[
y=(q,a,b,c)
\]

be the local variables.  For a density perturbation, record six local jets

\[
\xi_0,\xi_u,\xi_c,\xi_v,\xi_-,\xi_+
\]

corresponding to

\[
1,\ (x-u)^{-1},\ (x-c)^{-1},\ (x-v)^{-1},\ L_-,\ L_+.
\]

Linearization:

\[
d\mathcal K=A\,dy+B\,\xi.
\]

The old target

\[
\operatorname{rank}B_{\rm Schur}=6
\]

was wrong.  Since \(A\) has four local variables and six augmented rows, the
generic cokernel dimension is

\[
6-4=2.
\]

Correct object:

\[
\boxed{
B_{\rm cok}:=\ker(A^T)B,\qquad \operatorname{rank}B_{\rm cok}=2.
}
\]

The compact adjoint density kernel therefore has the form

\[
K_\lambda(x)=
\lambda_0
+\frac{\lambda_u}{x-u}
+\frac{\lambda_c}{x-c}
+\frac{\lambda_v}{x-v}
+\lambda_-L_-(x)
+\lambda_+L_+(x),
\]

where \(\lambda\) lies in the two-dimensional cokernel selected by the local
KKT equations.

The compact proof target is:

\[
\boxed{
\text{show no nonzero }K_\lambda\text{ in this two-dimensional cokernel has
the admissible compact sign pattern.}
}
\]

### 9.9 Explicit cokernel basis already found

Put

\[
p=\log(1/a),\qquad r=\log(1/b),
\]

\[
U_u=U'(u)>0,\qquad U_v=U'(v)<0,\qquad F_c=F'(c)<0,
\]

and

\[
A_u=W'(u),\quad B_v=W'(v),\quad A_{2,u}=W''(u),\quad B_{2,v}=W''(v).
\]

In the basis

\[
(1,\ (x-u)^{-1},\ (x-c)^{-1},\ (x-v)^{-1},\ L_-,\ L_+),
\]

one cokernel vector is

\[
\boxed{
\kappa_1=
\left(
\frac{-U_u r+U_v p}{U_u},\
0,\
-\frac{A_uU_v-B_vU_u}{F_cU_u},\
0,\
\frac{U_v}{U_u},\
1
\right).
}
\]

The second is

\[
\boxed{
\begin{aligned}
\kappa_2
=\bigg(&
\frac{p(-A_u+aA_{2,u}+B_v+bB_{2,v})}{U_u},\
a,\\
&
\frac{
A_u^2-A_uaA_{2,u}-A_uB_v-A_ubB_{2,v}
+aA_{2,u}U_u+bB_{2,v}U_u
}{F_cU_u},\\
&b,\
\frac{-A_u+aA_{2,u}+B_v+bB_{2,v}}{U_u},\
0
\bigg).
\end{aligned}
}
\]

This is useful work and should be preserved.  It replaces an abstract rank
claim with an explicit two-dimensional adjoint-kernel family.

### 9.10 Six-kernel determinant / Chebyshev tool

For ordered points

\[
x_1<\cdots<x_6,\qquad x_i\notin[u,v],
\]

define

\[
\Delta_6(x_1,\ldots,x_6)
:=
\det
\begin{bmatrix}
1 &(x-u)^{-1}&(x-c)^{-1}&(x-v)^{-1}&L_-(x)&L_+(x)
\end{bmatrix}_{x=x_i}.
\]

Expanding the two averaged columns:

\[
\Delta_6=
\int_u^c\int_c^v
\det
\begin{bmatrix}
1 &(x-u)^{-1}&(x-c)^{-1}&(x-v)^{-1}&(x-s)^{-1}&(x-t)^{-1}
\end{bmatrix}_{x=x_i}
\,dt\,ds .
\]

For \(u<s<c<t<v\), the integrand is a Cauchy determinant with one source at
infinity, hence has fixed oriented sign.  Therefore

\[
\boxed{
\left(\prod_{i=1}^6\sigma(x_i)\right)
\Delta_6(x_1,\ldots,x_6)
\text{ has one fixed nonzero sign,}
\qquad
\sigma(x)=\operatorname{sgn}(x-c).
}
\]

What this proves:

The six local jet kernels form an oriented strict Chebyshev system.

What it does not prove:

It does not by itself prove exactness.  One still has to connect the KKT
cokernel/sign-pattern problem to this Chebyshev tool.

### 9.11 Wronskian reduction for the two-dimensional cokernel

Write

\[
K_1=R_1+\alpha L_-+\beta L_+,\qquad
K_2=R_2+\gamma L_-+\delta L_+,
\]

where \(R_1,R_2\) are rational combinations of

\[
1,\ (x-u)^{-1},\ (x-c)^{-1},\ (x-v)^{-1}.
\]

In the current basis:

\[
\alpha=\frac{U_v}{U_u},\qquad
\beta=1,\qquad
\gamma=\frac{-A_u+aA_{2,u}+B_v+bB_{2,v}}{U_u},\qquad
\delta=0.
\]

Since

\[
L_-'=\frac1{x-u}-\frac1{x-c},\qquad
L_+'=\frac1{x-c}-\frac1{x-v},
\]

the Wronskian

\[
W_{12}=K_1K_2'-K_1'K_2
\]

has the form

\[
\boxed{
W_{12}=C_0(x)+C_-(x)L_-(x)+C_+(x)L_+(x).
}
\]

With \(\delta=0\),

\[
\boxed{
C_-(x)=\alpha R_2'(x)-\gamma R_1'(x)-\gamma L_+'(x),
}
\]

and

\[
\boxed{
C_+(x)=R_2'(x)+\gamma L_-'(x).
}
\]

This is a strong reduction: only two logarithmic coefficients and one rational
remainder control the ratio-monotonicity obstruction.

Open mathematical question:

\[
\boxed{
\text{Do stationarity and }W''>0\text{ force the signs of }
C_-,C_+,C_0\text{ needed for }W_{12}\text{ to have one sign?}
}
\]

### 9.12 Curvature clamp

The one-oval inequalities reduce to an elementary sharp condition.

On \(I_1=(u,c)\), put

\[
A=x-u>0,\qquad B=c-x>0,\qquad d_-=c-u.
\]

Then \(A+B=d_-\) and

\[
\frac1{x-u}-\frac1{x-c}
=\frac1A+\frac1B
=\frac{d_-}{AB}.
\]

The inequality

\[
\Gamma\left(\frac1{x-u}-\frac1{x-c}\right)
\le
\frac{a}{(x-u)^2}+\frac{Q_c}{(x-c)^2}
\]

is equivalent to

\[
\Gamma d_-AB\le aB^2+Q_cA^2.
\]

The sharp condition is

\[
\Gamma\le \frac{2\sqrt{aQ_c}}{c-u}.
\]

Similarly, on \(I_2=(c,v)\),

\[
-\Gamma\le \frac{2\sqrt{bQ_c}}{v-c}.
\]

Thus the compact branch would close by this route if one proves

\[
\boxed{
Q_c\ge0,\qquad
-\frac{2\sqrt{bQ_c}}{v-c}
\le \Gamma \le
\frac{2\sqrt{aQ_c}}{c-u}.
}
\]

This is called the curvature clamp.

### 9.13 Reduced Hessian theorem

The curvature clamp should come from second variation, not first-order rank.

Let \(G\) be the reduced second-variation form on six density jets after the
local variables \(y=(q,a,b,c)\) are eliminated.  Let

\[
T(h)=Ph,\qquad h=(h_u,h_v,h_-,h_+)
\]

be the tangent lift.  The true tangent Hessian is

\[
\boxed{
M=P^TGP.
}
\]

Let

\[
e_u=(1,0,0,0),\qquad e_v=(0,1,0,0),\qquad
e_\zeta=(0,0,-1,1).
\]

The required scalar identities are:

\[
\boxed{
e_\zeta^TMe_\zeta=\lambda Q_c,
}
\]

\[
\boxed{
e_u^TMe_\zeta=-\frac{\lambda}{2}\Gamma(c-u),
}
\]

and

\[
\boxed{
e_v^TMe_\zeta=\frac{\lambda}{2}\Gamma(v-c).
}
\]

If these identities hold and \(G\succeq0\), then

\[
G\succeq0
\Rightarrow M\succeq0
\Rightarrow\text{curvature clamp}
\Rightarrow\text{Wronskian sign}
\Rightarrow\text{compact }g=2\text{ branch excluded.}
\]

This is the current smallest honest hard mouth.

### 9.14 Decomposition of the Hessian

The reduced Hessian should be computed as

\[
\boxed{
\delta^2\mathcal L
=
\mathcal E_{\log}(\delta\nu)
+\mathcal E_{\rm edge}(\delta\nu)
+\mathcal E_{\rm Schur}(\delta\nu).
}
\]

Here

\[
\mathcal E_{\log}(\delta\nu)
=
\iint -\log|x-y|\,d(\delta\nu)(x)d(\delta\nu)(y)
\]

is the direct log-energy contribution.

The edge term supplies the endpoint diagonal coefficients \(a,b\).

The Schur term comes from eliminating \(y=(q,a,b,c)\).  In block form,

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
\end{pmatrix}
}
\]

on actual density perturbations satisfying \(\delta\Pi=0\), where
\(A=(E_-,E_+,M,F)\).  The older unbordered formula is kept only as a
shorthand for a nonconstrained toy chart.

The immediate calculation is:

\[
\boxed{
\text{compute }H_{\xi y}H_{yy}^{-1}H_{y\xi}
\text{ for the neck and endpoint-transfer jets.}
}
\]

This is the next pure mathematical task to do, ahead of any new verifier work.

### 9.15 Regularity / finite-gap reduction interface

The exact lower-bound route eventually needs to leave the regular finite-gap
class.  This must not be hidden inside the compact \(g=2\) argument.

Interface lemma:

\[
\boxed{
\text{Lemma R: every minimizing counterexample can be approximated by regular
finite-gap counterexamples without increasing }|E_\mu|\text{ past }M_*.
}
\]

If such approximation fails, the failure should itself be a degeneration:

\[
\text{nonregular limit}
\Rightarrow
\text{pinching, endpoint atom creation, or lower-genus collapse}.
\]

The exact lower-bound proof may temporarily be written as:

\[
\text{regular finite-gap classification}
\quad+\quad
\text{Lemma R}
\quad\Rightarrow\quad
L_-\ge M_*.
\]

Status:

- not proved;
- should not be assumed silently;
- lower priority than Theorem U, corrected \(g=1\), pinching, and compact
  \(g=2\) reduced Hessian;
- becomes necessary before claiming the unconditional exact infimum.

## 10. Active Global Finite-Gap Classification Attempt

This section starts the actual global route.  It should be updated before any
new computational work.  The target is not another local certificate; the
target is a regular finite-gap classification theorem.

### 10.1 Regular finite-gap classification theorem

Working theorem:

\[
\boxed{
\text{No admissible regular finite-gap minimizer has } |E_\mu|<M_*.
}
\]

The exact lower-bound proof is intended to be:

\[
\text{regular finite-gap classification}
+\text{Lemma R}
\Rightarrow
L_-\ge M_*.
\]

The classification theorem is now split into five mathematical assertions:

1. finite-gap representation and sign/interlacing;
2. boundary pinching lowers genus or becomes inadmissible;
3. the \(F(c)\)-row is repaired: \(F(c)=0\) is treated as a finite-gap
   branch equation, not as a free multiplier in local \(y\)-stationarity;
4. compact non-pinched \(g=2\) chambers are impossible under the repaired
   branch-parametrized Hessian;
5. every compact \(g\ge3\) chamber contains a local \(g=2\)-type neck
   obstruction.

### 10.2 Lemma FG: finite-gap representation

Precise regularity hypotheses needed:

- the flat zero set is a finite union of intervals
  \[
  Z=\bigcup_{j=1}^g[\alpha_j,\beta_j];
  \]
- the dual measure has only absolutely continuous density on these cuts plus
  finitely many atoms at boundary/pole points;
- \(F(z)=\int (z-t)^{-1}\,d\lambda(t)\) has no singularities away from these
  cuts and atoms;
- \(F(z)=\lambda(\mathbb R)/z+O(z^{-2})\) at infinity.

On each flat interval,

\[
U_\lambda=0
\quad\Rightarrow\quad
\operatorname{Re}F_+(x)=0
\qquad(\alpha_j<x<\beta_j).
\]

Let

\[
D(z)=\prod_{j=1}^g(z-\alpha_j)(z-\beta_j),
\qquad
R(z)=\sqrt{D(z)},\qquad R(z)\sim z^g.
\]

Across a cut, \(R_+=-R_-\) and \(F_+=-\overline{F_+}\) in the flat direction,
so \(F/R\) has matching boundary values on the two sides of each cut.  By
Schwarz reflection, \(F/R\) is meromorphic on the sphere after the cuts are
removed.  Therefore

\[
\boxed{
F(z)=\frac{P(z)}{Q(z)}R(z).
}
\]

Here \(Q\) records atom/pole locations and \(P\) is fixed up to finitely many
parameters by the decay condition at infinity and the chosen residues.  If
\(\deg Q=d\), the decay condition

\[
F(z)=O(1/z)
\]

imposes

\[
\deg P\le d-g-1.
\]

Status:

- this lemma is standard and should be provable under the regular finite-gap
  hypotheses above;
- the hypotheses must be stated explicitly, otherwise the reflection argument
  silently ignores singular continuous or accumulating support.

### 10.3 Sign and interlacing lemma

For a positive dual measure \(\lambda\),

\[
F'(x)
=-\int\frac{d\lambda(t)}{(x-t)^2}<0
\]

on every real interval disjoint from \(\operatorname{supp}\lambda\).

Consequences:

1. each complementary real interval contains at most one zero of \(F\);
2. zeros, poles, and branch endpoints must interlace;
3. residue signs are determined by one-sided signs of \(F\):
   \[
   m_p=\operatorname{Res}_{z=p}F\ge0;
   \]
4. cut density signs are determined by
   \[
   \rho(x)=-\frac1\pi\operatorname{Im}F_+(x)\ge0.
   \]

This is the bridge between the analytic finite-gap form and the combinatorial
classification of chambers.

Open item:

Write the chamber sign table explicitly.  The current ledger has formulas for
the corrected \(g=1\) branch, but it does not yet contain a complete sign table
for every possible \(g=2\) chamber.

### 10.4 Boundary pinching theorem

Let

\[
F_n(z)=\frac{P_n(z)}{Q_n(z)}
\sqrt{\prod_{j=1}^g(z-\alpha_{j,n})(z-\beta_{j,n})}
\]

be a sequence of positive finite-gap transforms in a fixed total-mass
normalization.  Suppose two adjacent branch points pinch:

\[
\beta_{k,n}\to\gamma,\qquad
\alpha_{k+1,n}\to\gamma.
\]

Then, locally away from \(\gamma\),

\[
\sqrt{(z-\beta_{k,n})(z-\alpha_{k+1,n})}
\to z-\gamma.
\]

After cancelling any removable common factor with \(P_n\) or \(Q_n\), a
subsequence has a lower-genus limit

\[
\boxed{
F_\infty(z)
=
\frac{P_\infty(z)}{Q_\infty(z)}
\sqrt{\prod_{j\ne k,k+1}(z-\alpha_j)(z-\beta_j)}.
}
\]

Cases:

1. no pole of \(Q_n\) pinches at \(\gamma\): the factor \(z-\gamma\) lowers
   genus directly, or a pure gap-closing sign flip makes the limit
   inadmissible;
2. a pole \(p_n\) of \(Q_n\) pinches at \(\gamma\): the limit records either a
   nonnegative endpoint atom at an allowed boundary/pole point or an
   inadmissible interior/negative residue;
3. a zero of \(P_n\) pinches at \(\gamma\): the zero cancels part of the
   limiting factor, again lowering genus or killing the density.

The positivity input is weak closure:

\[
\lambda_n\ge0,\quad \lambda_n(\mathbb R)\le C
\quad\Rightarrow\quad
\lambda_n\rightharpoonup\lambda_\infty\ge0.
\]

Thus a boundary point of a positive finite-gap chamber cannot create a new
better compact extremal.  It either lowers genus or violates residue/density
positivity.

Status:

- this is the first boundary theorem to write fully;
- it must include coefficient normalization so that \(P_n/Q_n\) does not
  escape to infinity;
- endpoint atom creation is allowed and must not be treated as a failure.

### 10.5 Compact \(g=2\): local equations now fixed

For the first extra positive component

\[
I=(u,v),\qquad u<c<v,\qquad a=c-u,\qquad b=v-c,
\]

write

\[
U(x)=q\log\frac1{|x-c|}+W(x),
\]

where \(W\) is the external field from all mass outside \(I\).

Endpoint equations:

\[
E_-=q\log\frac1a+W(u)=0,
\qquad
E_+=q\log\frac1b+W(v)=0.
\]

Stationarity gives

\[
S=aW'(u)+bW'(v)=0.
\]

The dual complementarity row is

\[
F(c)=0,\qquad F'(c)<0.
\]

If the local variables are

\[
y=(q,a,b,c),
\]

then, holding the external field jets fixed,

\[
\partial_qE_-=\log\frac1a,\quad
\partial_aE_-=-\frac qa-W'(u),\quad
\partial_cE_-=W'(u),
\]

\[
\partial_qE_+=\log\frac1b,\quad
\partial_bE_+=-\frac qb+W'(v),\quad
\partial_cE_+=W'(v),
\]

and

\[
\partial_aS=W'(u)-aW''(u),\quad
\partial_bS=W'(v)+bW''(v),\quad
\partial_cS=aW''(u)+bW''(v).
\]

These derivatives explain why the previously found cokernel basis naturally
uses

\[
W'(u),\quad W'(v),\quad W''(u),\quad W''(v),\quad F'(c).
\]

If

\[
p=\log\frac1a,\qquad r=\log\frac1b,
\]

\[
A=W'(u),\quad B=W'(v),\quad A_2=W''(u),\quad B_2=W''(v),
\]

then

\[
U_u=\frac qa+A,\qquad U_v=-\frac qb+B,
\]

and the first-order rows are

\[
\nabla_yE_-=(p,-U_u,0,A),
\]

\[
\nabla_yE_+=(r,0,U_v,B),
\]

\[
\nabla_yS=(0,A-aA_2,B+bB_2,aA_2+bB_2).
\]

Let

\[
A_3=W'''(u),\qquad B_3=W'''(v).
\]

The currently available residual Hessian pieces are:

\[
\nabla_y^2E_-=
\begin{pmatrix}
0&-1/a&0&0\\
-1/a&q/a^2+A_2&0&-A_2\\
0&0&0&0\\
0&-A_2&0&A_2
\end{pmatrix},
\]

\[
\nabla_y^2E_+=
\begin{pmatrix}
0&0&-1/b&0\\
0&0&0&0\\
-1/b&0&q/b^2+B_2&B_2\\
0&0&B_2&B_2
\end{pmatrix},
\]

\[
\nabla_y^2S=
\begin{pmatrix}
0&0&0&0\\
0&-2A_2+aA_3&0&A_2-aA_3\\
0&0&2B_2+bB_3&B_2+bB_3\\
0&A_2-aA_3&B_2+bB_3&aA_3+bB_3
\end{pmatrix}.
\]

Old bookkeeping variant:

If the scalar Lagrangian is artificially augmented with an independent
\(\lambda_SS\) row,

\[
\Phi=
\lambda_{\mathcal L}\mathcal L+\lambda_M M+\lambda_FF(c)
+\lambda_-E_-+\lambda_+E_++\lambda_SS,
\]

then the part of \(H_{yy}\) already forced by the local endpoint and
stationarity rows is

\[
H_{yy}^{\rm local}
=
\lambda_-\nabla_y^2E_-
+\lambda_+\nabla_y^2E_+
+\lambda_S\nabla_y^2S
+\lambda_F\nabla_y^2F(c).
\]

The term \(\nabla_y^2F(c)\) is still not defined in the ledger and must be
derived from the exact dual complementarity row.

Current status:

This \(\lambda_SS\) version is not the proof-grade convention.  The later
calculation also shows that a free \(\lambda_FF(c)\) row is not proof-grade.
The active convention is recorded in §§10.17b-10.17g:

\[
S=0\text{ is derived from endpoint stationarity, and }F(c)=0
\text{ is imposed as a branch equation.}
\]

The Hessian used for the Schur complement contains neither an independent
\(\lambda_S\nabla_y^2S\) contribution nor a free
\(\lambda_F\nabla_y^2F(c)\) contribution.

### 10.6 Compact \(g=2\): what blocks the Schur complement

The Schur complement target is no longer the unbordered expression

\[
G=H_{\xi\xi}-H_{\xi y}H_{yy}^{-1}H_{y\xi}.
\]

The active target is the fixed-chart state-lift Schur complement in §10.17c,
using \(A=(E_-,E_+,M,F)\) for the \(y\)-lift and \(\delta\Pi=0\) as a separate
density admissibility condition.  The current ledger is still under-specified
for a literal computation of \(H_{yy}\) and \(H_{\xi y}\).  To compute them,
the proof must first choose the actual second-variation functional:

\[
\mathcal L
=
\text{length term}
+\text{log-energy term}
+\text{mass/endpoint/period constraints}.
\]

Without this explicit \(\mathcal L\), the matrix \(A=dK/dy\) is defined, but
the Hessian block

\[
H_{yy}=\frac{\partial^2\mathcal L}{\partial y^2}
\]

is not.

There is a second convention issue: one must decide whether the density jets
\(\xi\) are fixed coordinates at the base point or \(y\)-dependent kernel
coordinates.  This changes \(H_{\xi y}\).  For a cokernel kernel

\[
K_\kappa(x)=
\kappa_0+\frac{\kappa_u}{x-u}+\frac{\kappa_c}{x-c}+\frac{\kappa_v}{x-v}
+\kappa_-L_-(x)+\kappa_+L_+(x),
\]

the formal \(y\)-derivatives of the kernel coordinates are

\[
\partial_qK_\kappa=0,
\]

\[
\partial_aK_\kappa
=-\frac{\kappa_u}{(x-u)^2}+\frac{\kappa_-}{x-u},
\]

\[
\partial_bK_\kappa
=\frac{\kappa_v}{(x-v)^2}+\frac{\kappa_+}{x-v},
\]

and

\[
\begin{aligned}
\partial_cK_\kappa={}&
\frac{\kappa_u}{(x-u)^2}
+\frac{\kappa_c}{(x-c)^2}
+\frac{\kappa_v}{(x-v)^2}\\
&+\kappa_-\left(-\frac1{x-u}+\frac1{x-c}\right)
+\kappa_+\left(-\frac1{x-c}+\frac1{x-v}\right).
\end{aligned}
\]

These formulas are useful, but they become \(H_{\xi y}\) only after the scalar
functional and jet convention are fixed.

The curvature-clamp derivation also needs endpoint diagonal identities of the
form

\[
e_u^TMe_u=\lambda a,\qquad e_v^TMe_v=\lambda b,
\]

or their correct signed replacements.  Without these diagonal entries,
positive semidefiniteness of \(M\) does not by itself imply the stated clamp.

Therefore the immediate next mathematical task is sharper than before:

\[
\boxed{
\text{write the exact branch-parametrized Lagrangian }\Phi_{\rm br}
\text{ whose }y\text{-Euler equations imply }E_-=E_+=S=0.
}
\]

Only after this is fixed can one compute

\[
H_{\xi y}H_{yy}^{-1}H_{y\xi}
\]

without ambiguity.

### 10.7 Current hard-mouth update

The previous hard mouth was stated as:

\[
\text{compute }H_{\xi y}H_{yy}^{-1}H_{y\xi}.
\]

The more precise hard mouth is:

\[
\boxed{
\text{first prove the state-lift/period-splitting lemma, then compute the
bordered Schur complement using }A=(E_-,E_+,M,F).
}
\]

This is not a retreat.  It prevents a false calculation: a Schur complement
computed from the first-order KKT rows alone would not prove the curvature
clamp.

Smallest missing definitions:

1. exact scalar functional \(\Phi_{\rm br}\), including length, mass, period,
   and endpoint terms, but excluding free \(S\) and \(F(c)\) multiplier rows;
2. exact residual equations with density-jet entry;
3. treatment of the period row in the Hessian calculation;
4. exact branch state-lift rows
   \[
   A=(E_-,E_+,M,F),\qquad \det A_y=-XYF'(c);
   \]
5. edge term and endpoint-transfer tangent lift \(T(h)=Ph\);
6. endpoint diagonal identities needed for the curvature clamp.

### 10.8 Formal local KKT template for \(\Phi\)

The previous augmented template with independent \(\lambda_SS\) and
\(\lambda_FF(c)\) rows is now kept only as bookkeeping.  The proof-grade
direction is:

\[
\boxed{
S\text{ is derived from endpoint stationarity, while }F(c)=0\text{ is a
finite-gap branch equation.}
}
\]

Therefore the scalar functional used for the Hessian should not include a
\(\lambda_SS\) term or a free \(\lambda_FF(c)\) term unless a separate lemma
proves that doing so does not overcount the tangent space.  The later
calculation in §10.17a proves that the free \(\lambda_FF(c)\) row is false in
the fixed chart.

Let

\[
u=c-a,\qquad v=c+b,
\]

and let the external field, including the selected density coordinate
\(\xi\), be

\[
W_\xi(x)=W_{\rm out}(x)+\delta W_\xi(x).
\]

Define

\[
E_-(y,\xi)=q\log\frac1a+W_\xi(c-a),
\]

\[
E_+(y,\xi)=q\log\frac1b+W_\xi(c+b),
\]

\[
S(y,\xi)=aW_\xi'(c-a)+bW_\xi'(c+b).
\]

A coherent branch-parametrized functional is

\[
\begin{aligned}
\Phi_{\rm br}(q,a,b,c,\xi;\lambda)
={}&
(a+b)+\ell_{\rm ext}(\xi)
+\lambda_M\big(q+m_{\rm ext}(\xi)-1\big)
+\lambda_{\rm per}\Pi(\xi)\\
+\lambda_-E_-(y,\xi)
+\lambda_+E_+(y,\xi).
\end{aligned}
\]

Multiplier variation gives the independent rows:

\[
\partial_{\lambda_-}\Phi=E_-=0,\qquad
\partial_{\lambda_+}\Phi=E_+=0,
\]

plus the mass and period rows

\[
q+m_{\rm ext}(\xi)=1,\qquad \Pi(\xi)=0.
\]

The stationarity row

\[
S(y,\xi)=0
\]

must be recovered from \(d_y\Phi=0\), not imposed as
\(\partial_{\lambda_S}\Phi=0\).

The dual complementarity row is imposed separately:

\[
F_\xi(c)=0,\qquad F_\xi'(c)<0,
\]

and contributes only through the branch tangent condition

\[
\delta F_\xi(c)=F_\xi'(c)\delta c+\delta_\xi F_\xi(c)=0.
\]

The length multiplier should be normalized as

\[
\lambda_\ell=1
\]

for length minimization.  If the sign convention is instead
\(M_*-|E|\), all Hessian signs must be flipped consistently.

The branch Cauchy transform \(F_\xi\) still needs a fixed scale.  The sign
condition

\[
F_\xi'(c)<0
\]

orients the row, but does not normalize it.  One possible normalization is

\[
F_\xi(z)=\frac{m}{z}+O(z^{-2}),\qquad m>0,
\]

with \(m\) fixed.

Working normalization:

\[
\boxed{
F_\xi(z)=\int\frac{d\lambda_\xi(t)}{z-t},\qquad
\lambda_\xi(\mathbb R)=m_F>0\text{ fixed.}
}
\]

Thus

\[
F_\xi(z)=\frac{m_F}{z}+O(z^{-2})
\qquad(z\to\infty).
\]

Do not normalize by \(F'(c)\) or by one residue.  Such a normalization would
depend on moving local data and would contaminate the branch Hessian.

### 10.9 First variation of the endpoint-derived template

Holding external jets fixed, the \(y=(q,a,b,c)\) derivatives of the formal
template include

\[
\partial_q\Phi
=\lambda_M+\lambda_-\log\frac1a+\lambda_+\log\frac1b+\cdots,
\]

\[
\partial_a\Phi
=\lambda_\ell
+\lambda_-\left(-\frac qa-W'(u)\right)+\cdots,
\]

\[
\partial_b\Phi
=\lambda_\ell
+\lambda_+\left(-\frac qb+W'(v)\right)+\cdots,
\]

\[
\partial_c\Phi
=
\lambda_-W'(u)+\lambda_+W'(v)
+\lambda_FF'(c)+\cdots.
\]

The omitted terms are exactly the dangerous pieces:

\[
\ell_{\rm ext},\qquad m_{\rm ext},\qquad \Pi,\qquad F_\xi,
\]

and their \(y,\xi\) dependence.  They cannot be dropped in a proof-grade Schur
complement.

### 10.10 Reduced endpoint-only sanity check

There is a useful warning from the simpler endpoint-only problem.  If one
starts from

\[
\Phi_0=a+b+\lambda_-E_-+\lambda_+E_+,
\]

then first variation gives

\[
\lambda_-=\frac1{U'(u)},\qquad
\lambda_+=-\frac1{U'(v)}.
\]

The \(c\)-variation becomes

\[
\frac{W'(u)}{U'(u)}-\frac{W'(v)}{U'(v)}=0,
\]

which is equivalent, using

\[
U'(u)=\frac qa+W'(u),\qquad U'(v)=-\frac qb+W'(v),
\]

to the stationarity identity

\[
\boxed{aW'(u)+bW'(v)=0.}
\]

Thus \(S=0\) can arise as an Euler consequence of endpoint-constrained length
minimization.  Treating \(S\) as an independent constraint in \(\Phi\) is
therefore a formal KKT bookkeeping choice and may overcount unless justified.

The same endpoint-only variation also gives a \(q\)-row:

\[
\frac{\log(1/a)}{U'(u)}
-\frac{\log(1/b)}{U'(v)}=0.
\]

This row should be compared with the dual complementarity condition at the
atom.  It is not automatically the same as the Cauchy-transform condition

\[
F(c)=0.
\]

This distinction is important: \(W\) is the primal external field, while
\(F=-U_\lambda'\) is the dual Cauchy transform.  Treating \(F\) as a derivative
of \(W\) would be a category error.

Endpoint-only conclusion:

The endpoint-derived calculation is useful but insufficient.  It shows that
\(S=0\) can be recovered from length stationarity, so adding \(S\) as an
independent constraint risks overcounting.  But if one keeps only

\[
\Phi_0=a+b+\lambda_-E_-+\lambda_+E_+,
\]

then the \(q\)-row produces an extra condition.  Eliminating
\(\lambda_\pm\) gives

\[
\frac{\log(1/a)}{U'(u)}
-\frac{\log(1/b)}{U'(v)}=0.
\]

Together with

\[
S=aW'(u)+bW'(v)=0,
\]

this reduces formally to

\[
q=-aW'(u),
\]

which is not an acceptable general Euler equation for the compact neck.

Therefore the proof-grade local functional cannot be endpoint-only.  It must
include at least the mass row, period row, and dual-complementarity row, and it
must explain which rows are independent after reduction.

Working convention to test next:

\[
\boxed{
S=0\text{ is derived from endpoint stationarity, while }F(c)=0
\text{ remains a separate dual-complementarity condition.}
}
\]

The role of the mass/period rows is then to absorb the \(q\)-variation and
global density variations without introducing a false scalar constraint.

No-overcount Hessian convention:

\[
\boxed{
\text{The Hessian for the Schur complement contains no }
\lambda_S\nabla^2S\text{ term.}
}
\]

The row \(dS\) may appear after differentiating the reduced Euler equations,
but it is not an independent feasible-tangent constraint.

### 10.11 Density-jet convention to use next

For the proof-grade Hessian, \(\xi\) should first be an actual signed density
perturbation, not just six formal numbers.

Use

\[
d\eta(x)=G(x)\omega(x)\,dx
\]

on the active finite-gap ovals, with positive background weight

\[
\omega(x)=\frac1{|Q(x)|^2\sqrt{|D(x)|}}.
\]

The six local rows are then linear functionals of \(G\):

\[
R_0(G),\quad R_u(G),\quad R_c(G),\quad R_v(G),\quad R_-(G),\quad R_+(G).
\]

The finite vector

\[
\xi=(\xi_0,\xi_u,\xi_c,\xi_v,\xi_-,\xi_+)
\]

should denote these row values:

\[
\xi_i=R_i(G).
\]

This convention avoids pretending that every six-tuple is automatically a
valid density perturbation.  The proof must later show that the required
finite-dimensional tangent directions are realizable by actual \(G\)'s, or
else use the cokernel directly as a separating functional on the image of the
row map.

Under this convention, \(H_{\xi y}\) is shorthand for the mixed second
variation pairing

\[
(G,\delta y)\longmapsto
\delta_G\delta_y\Phi,
\]

not an ordinary derivative with respect to six independent coordinates until
the row map has been quotient/projection-reduced.

Period row:

\[
\Pi(G)=0
\]

must stay outside the six local rows unless a separate lemma proves it lies in
their span.  The current working assumption is that it is a seventh global
constraint.

Updated coordinate lemma to prove:

\[
\boxed{
\text{The density perturbation space maps to the six local rows plus period
row, and the compact cokernel obstruction acts on this image.}
}

More explicitly, in a fixed base-point chart write

\[
d\xi(x)=G(x)\omega_0(x)\,dx,
\qquad
\omega_0(x)=\frac1{|Q_0(x)|^2\sqrt{|D_0(x)|}}.
\]

The perturbations of the primal external field and dual Cauchy row are

\[
\delta W_\xi(s)=\int_J\log\frac1{|s-x|}\,d\xi(x),
\]

\[
\delta F_\xi(z)=\int_J\frac{d\xi(x)}{z-x}.
\]

Thus

\[
E_-(y,\xi)=q\log\frac1a+W_0(u)+\delta W_\xi(u),
\]

\[
E_+(y,\xi)=q\log\frac1b+W_0(v)+\delta W_\xi(v).
\]

At first order,

\[
\delta_\xi S
=a\,\delta W_\xi'(u)+b\,\delta W_\xi'(v).
\]

With the row convention

\[
R_u(G)=\delta W_\xi'(u),\qquad
R_v(G)=\delta W_\xi'(v),
\]

this is

\[
\delta_\xi S=aR_u(G)+bR_v(G).
\]

For the dual row, using

\[
F(z)=\int\frac{d\xi(x)}{z-x},
\]

one has

\[
\delta_\xi F(c)=\delta F_\xi(c)=-R_c(G)
\]

if \(R_c(G)\) is defined by the kernel \((x-c)^{-1}\).

Mass is

\[
\delta_\xi M=R_0(G)=\int_Jd\xi.
\]

The period row is

\[
\delta_\xi\Pi=\int_J\pi_0(x)\,d\xi(x),
\]

and remains a seventh global row.

Endpoint value warning:

The rows \(R_-,R_+\) give differences,

\[
R_-(G)=\delta W_\xi(c)-\delta W_\xi(u),
\]

\[
R_+(G)=\delta W_\xi(v)-\delta W_\xi(c).
\]

They do not by themselves determine the absolute endpoint values
\(\delta W_\xi(u)\) and \(\delta W_\xi(v)\).  Therefore the endpoint equations
cannot be proof-grade functions of six arbitrary numbers unless the common
anchor \(\delta W_\xi(c)\) is fixed, absorbed by another normalization, or the
proof keeps \(\xi\) as an actual density perturbation.

This is the reason to do the Schur complement first on the actual density
space and only afterwards push it down to finite rows.

### 10.12 Branch-parametrized Phi-Euler-Hessian lemma

The next lemma should now be stated in the branch-parametrized convention:

\[
\boxed{\textbf{Lemma Branch-Parametrized Phi-Euler-Hessian.}}
\]

Let \(I=(u,v)\), \(u<c<v\), \(a=c-u\), \(b=v-c\), and

\[
y=(q,a,b,c).
\]

Fix a regular compact non-pinched \(g=2\) base point, a fixed finite-gap
density chart

\[
d\xi=G\omega_0dx,
\]

a fixed mass normalization, a fixed period row, and a fixed Cauchy-transform
branch scale

\[
F_\xi(z)=\frac{m_F}{z}+O(z^{-2}).
\]

Define

\[
\begin{aligned}
\Phi_{\rm br}(y,\xi;\lambda)
={}&
(a+b)+\ell_{\rm ext}(\xi)
+\lambda_M(q+m_{\rm ext}(\xi)-1)
+\lambda_{\rm per}\Pi(\xi)\\
+\lambda_-E_-(y,\xi)
+\lambda_+E_+(y,\xi),
\end{aligned}
\]

with no independent \(\lambda_SS\) term and no free
\(\lambda_FF_\xi(c)\) term.

Assuming regular rank of the mass, period, endpoint rows, and the finite-gap
branch equation, prove that

\[
d_y\Phi_{\rm br}=0,\qquad \partial_\lambda\Phi_{\rm br}=0
\]

is equivalent, after eliminating the multipliers, to

\[
E_-=E_+=0,
\]

\[
q+m_{\rm ext}(\xi)=1,\qquad \Pi(\xi)=0,
\]

and

\[
S=aW_\xi'(u)+bW_\xi'(v)=0,
\]

with no additional scalar \(q\)-row.

The branch equation is imposed outside the multiplier system:

\[
F_\xi(c)=0,\qquad F_\xi'(c)<0,
\]

and supplies the fourth state-lift row together with the endpoint and mass
rows.  In the fixed period chart, period is not included in this lift because
\(\Pi_y=0\).  The state rows are

\[
A=(E_-,E_+,M,F_\xi(c)).
\]

The tangent equations are

\[
A_y\delta y+A_\xi\xi=0,\qquad \delta\Pi(\xi)=0.
\]

Explicitly,

\[
A_y=
\begin{pmatrix}
p&-X&0&A\\
r&0&Y&B\\
1&0&0&0\\
0&0&0&F_\xi'(c)
\end{pmatrix},
\qquad
\det A_y=-XYF_\xi'(c).
\]

At such a point the Hessian blocks

\[
H_{yy},\qquad H_{\xi y},\qquad H_{\xi\xi}
\]

are the second derivatives of this fixed-chart \(\Phi_{\rm br}\).  The
reduced density Hessian is the bordered Schur complement on actual density
perturbations:

\[
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
\end{pmatrix},
\]

on actual perturbations satisfying \(\delta\Pi=0\).

The six-jet matrix is defined only after proving a realization/projection
lemma for the row map

\[
G\longmapsto
(R_0,R_u,R_c,R_v,R_-,R_+,\Pi)(G).
\]

### 10.15 Failed no-overcount multiplier-elimination attempt

This attempt is retained because it found the obstruction.  It is no longer
the proof-grade functional.  Write the old trial functional without
\(\lambda_SS\) but still with a free \(\lambda_FF(c)\) row:

\[
\Phi=(a+b)+\ell_{\rm ext}(\xi)
+\lambda_-E_-+\lambda_+E_+
+\lambda_FF_\xi(c)
+\lambda_M(q+m_{\rm ext}(\xi)-1)
+\lambda_{\rm per}\Pi(y,\xi).
\]

At fixed \(\xi\), ignore for the moment any hidden \(y\)-dependence of
\(\ell_{\rm ext}\) and \(m_{\rm ext}\).  Put

\[
U_u=U'(u)=\frac qa+W'(u),
\qquad
U_v=U'(v)=-\frac qb+W'(v),
\]

\[
A=W'(u),\qquad B=W'(v),\qquad
p=\log\frac1a,\qquad r=\log\frac1b.
\]

The \(y\)-stationarity equations have the schematic form

\[
\lambda_M+\lambda_-p+\lambda_+r
+\lambda_{\rm per}\Pi_q=0,
\]

\[
1-\lambda_-U_u+\lambda_{\rm per}\Pi_a=0,
\]

\[
1+\lambda_+U_v+\lambda_{\rm per}\Pi_b=0,
\]

\[
\lambda_-A+\lambda_+B+\lambda_FF_\xi'(c)
+\lambda_{\rm per}\Pi_c=0.
\]

Eliminating \(\lambda_-,\lambda_+\) from the endpoint equations gives

\[
\lambda_-=\frac{1+\lambda_{\rm per}\Pi_a}{U_u},
\qquad
\lambda_+=-\frac{1+\lambda_{\rm per}\Pi_b}{U_v}.
\]

Then the \(q\)-row becomes

\[
\lambda_M+\lambda_{\rm per}\Pi_q
+\frac{(1+\lambda_{\rm per}\Pi_a)p}{U_u}
-\frac{(1+\lambda_{\rm per}\Pi_b)r}{U_v}
=0.
\]

The \(c\)-row becomes

\[
\frac{(1+\lambda_{\rm per}\Pi_a)A}{U_u}
-\frac{(1+\lambda_{\rm per}\Pi_b)B}{U_v}
+\lambda_FF_\xi'(c)
+\lambda_{\rm per}\Pi_c=0.
\]

In the endpoint-only case \(\lambda_{\rm per}=\lambda_F=0\), the \(c\)-row
reduces to

\[
\frac{A}{U_u}-\frac{B}{U_v}=0,
\]

which is equivalent to

\[
S=aA+bB=0.
\]

But in the full finite-gap problem, the period and \(F\)-rows change the
\(c\)-row.  Therefore \(S=0\) follows from \(d_y\Phi=0\) only if the proof
supplies an additional identity:

\[
\boxed{
\lambda_{\rm per}\left(\frac{\Pi_aA}{U_u}
-\frac{\Pi_bB}{U_v}+\Pi_c\right)
+\lambda_FF_\xi'(c)
\text{ has exactly the correction needed to recover }S=0.
}
\]

Equivalently, one must prove a geometric period/dual-complementarity identity
showing that period and \(F\)-row contributions are tangent to the allowed
endpoint movement and do not create a new scalar neck condition.

Current status:

- endpoint-only \(\Phi_0\) proves \(S=0\) but creates a bad \(q\)-row;
- full \(\Phi\) can absorb the \(q\)-row through mass/global rows;
- full \(\Phi\) no longer yields \(S=0\) unless the period and \(F\)
  contributions are controlled;
- in the fixed chart the period contribution is zero, so the failure is caused
  by the free \(F(c)\)-row;
- the active repair is therefore the branch-parametrized convention in
  §10.17b, not a period/dual cancellation lemma.

### 10.16 Retired period/dual cancellation target

The previous next lemma was stated as:

\[
\boxed{\textbf{Lemma Period-Dual Cancellation.}}
\]

In the compact non-pinched \(g=2\) local chart, for endpoint translations
\((u,v,c)\) preserving the mass and period constraints, the \(F(c)\)-row and
period-row contributions to the \(c\)-Euler equation combine so that the
remaining endpoint stationarity condition is exactly

\[
S=aW_\xi'(u)+bW_\xi'(v)=0.
\]

In formulas, after eliminating \(\lambda_-,\lambda_+\), prove that

\[
\frac{(1+\lambda_{\rm per}\Pi_a)A}{U_u}
-\frac{(1+\lambda_{\rm per}\Pi_b)B}{U_v}
+\lambda_FF_\xi'(c)
+\lambda_{\rm per}\Pi_c=0
\]

is equivalent to

\[
aA+bB=0
\]

under the mass, period, and dual complementarity rows.

This target is now retired in this form.  The fixed-chart calculation below
shows

\[
\Pi_y=0,
\]

so the period row does not alter endpoint stationarity in this chart.  The
actual obstruction is the free \(F(c)\)-row.  Therefore the next proof-grade
repair is not a period/dual cancellation lemma, but a branch-parametrized
formulation in which \(F(c)=0\) is solved as a finite-gap branch equation and
does not carry a free multiplier in local \(y\)-stationarity.

### 10.17a Failure of the current free \(F(c)\)-row convention

The algebraic no-overcount attempt exposes a real obstruction.

Let

\[
A=W_\xi'(u),\qquad B=W_\xi'(v),
\]

\[
X=U'(u)=\frac qa+A,\qquad
Y=U'(v)=B-\frac qb,
\]

\[
L_a=\log\frac1a,\qquad L_b=\log\frac1b,
\qquad
S=aA+bB.
\]

For any row-gradient

\[
r=(r_q,r_a,r_b,r_c),
\]

define the two projected derivatives

\[
D_q(r)=r_q+\frac{L_a}{X}r_a-\frac{L_b}{Y}r_b,
\]

\[
D_c(r)=r_c+\frac{A}{X}r_a-\frac{B}{Y}r_b.
\]

After eliminating \(\lambda_-,\lambda_+\) from the endpoint equations, the four
\(d_y\Phi=0\) equations reduce to

\[
D_q(K)=0,\qquad D_c(K)=0,
\]

where

\[
K=\ell_y+\lambda_MM_y+\lambda_{\rm per}\Pi_y+\lambda_FF_y.
\]

The endpoint length part satisfies

\[
D_c(\nabla_y(a+b))
=\frac{A}{X}-\frac{B}{Y}
=-\frac{qS}{abXY}.
\]

Thus endpoint length contributes exactly the desired \(S\)-term.  The global
rows must not add an independent \(c\)-condition after the \(q\)-row is used to
solve \(\lambda_M\).

A sufficient projected-null package would be:

\[
D_q(M_y)\ne0,\qquad
\kappa=\frac{D_c(M_y)}{D_q(M_y)},
\]

\[
D_c(\Pi_y)-\kappa D_q(\Pi_y)=0,
\]

\[
D_c(F_y)-\kappa D_q(F_y)=0,
\]

and

\[
D_c(\ell_y)-\kappa D_q(\ell_y)=\gamma S,\qquad \gamma\ne0.
\]

Then \(D_q(K)=0\) fixes \(\lambda_M\), and the remaining projected \(D_c\)
equation reduces to \(S=0\).

However, under the current convention

\[
R_F(y,\xi)=F_\xi(c),
\]

with \(F_\xi\) fixed in \(y\), one has

\[
F_y=(0,0,0,F_\xi'(c)),
\]

so

\[
D_c(F_y)=F_\xi'(c)\ne0.
\]

Therefore the projected-null identity for \(F_y\) fails unless one proves an
additional cancellation involving \(\lambda_F\).  Equivalently:

\[
\boxed{
\text{with a free multiplier }\lambda_F\text{ on }F_\xi(c),\ d_y\Phi=0
\text{ does not imply }S=0.
}
\]

Consequences:

1. The current no-overcount Phi-Euler-Hessian lemma is false as stated.
2. The \(F(c)\)-row cannot simply be included as a free independent KKT row in
   \(y\)-stationarity.
3. One must choose one of three repairs:
   - remove \(F(c)\) from \(y\)-stationarity and treat it as a separate
     branch equation;
   - prove \(\lambda_F=0\) or otherwise fix \(\lambda_F\) before endpoint
     elimination;
   - redefine the \(F\)-row so its projected derivative satisfies
     \(D_c(F_y)-\kappa D_q(F_y)=0\).

This is now the actual hard mouth, replacing the earlier vague
Phi-Euler-Hessian statement.

Period row clarification:

In the current fixed-chart convention, the period row is a density row only:

\[
\Pi(G)=
\int_{J_1}G(x)\omega_0(x)\,dx
-\theta_{\rm per}\int_{J_2}G(x)\omega_0(x)\,dx,
\qquad \theta_{\rm per}>0.
\]

Equivalently,

\[
\Pi(G)=\int_J\pi_0(x)\,d\xi(x),
\qquad
\pi_0=1_{J_1}-\theta_{\rm per}1_{J_2}.
\]

Since \(y=(q,a,b,c)\) moves only the local primal neck in this chart,

\[
\Pi_q=\Pi_a=\Pi_b=\Pi_c=0.
\]

Thus

\[
\Pi_{yy}=0,\qquad \Pi_{y\xi}=0,\qquad \Pi_{\xi\xi}=0
\]

for the affine fixed period row.  The period constraint restricts admissible
density directions by \(\Pi(G)=0\), but it does not affect endpoint
stationarity.  Therefore the projected obstruction above is really an
\(F\)-row obstruction, not a period obstruction, in the fixed-chart
formulation.

If one later lets \(\theta_{\rm per}\), the ovals, or the weight move with
\(y\), this becomes a different moving-chart formulation and must be derived
from scratch.

### 10.17b Branch-parametrized repair

The best current repair is:

\[
\boxed{
F_\xi(c)=0\text{ is a finite-gap branch equation, not a free multiplier row
in }d_y\Phi.
}
\]

Thus replace the false free-\(F\) template by

\[
\begin{aligned}
\Phi_{\rm br}(y,\xi;\lambda)
={}&
(a+b)+\ell_{\rm ext}(\xi)
+\lambda_M(q+m_{\rm ext}(\xi)-1)
+\lambda_{\rm per}\Pi(\xi)\\
&+\lambda_-E_-(y,\xi)
+\lambda_+E_+(y,\xi),
\end{aligned}
\]

with no terms

\[
\lambda_FF_\xi(c),\qquad \lambda_SS.
\]

The branch equations are imposed separately:

\[
F_\xi(c)=0,\qquad F_\xi'(c)<0.
\]

At first order they restrict the tangent space by

\[
\boxed{
\delta F_\xi(c)=F_\xi'(c)\,\delta c+\delta_\xi F_\xi(c)=0.
}
\]

Important correction:

In the fixed period chart one must not set

\[
R=(E_-,E_+,M,\Pi)
\]

and invert \(R_y\).  Since \(\Pi_y=0\), the fourth row of this matrix is zero,
so \(R_y^{-1}\) does not exist.  Period is an admissibility condition on
density perturbations:

\[
\delta\Pi(\xi)=0,
\]

not a local state row for solving \(y=(q,a,b,c)\).

The correct state-lift rows are

\[
\boxed{A=(E_-,E_+,M,F_\xi(c)).}
\]

Then a branch-compatible tangent lift solves

\[
A_y\,\delta y+A_\xi\xi=0,
\qquad
\delta\Pi(\xi)=0.
\]

For reference, with

\[
p=\log(1/a),\qquad r=\log(1/b),
\]

\[
A=W'(u),\qquad B=W'(v),
\]

\[
X=U'(u)=q/a+A,\qquad Y=U'(v)=B-q/b,
\]

the local row matrix is

\[
A_y=
\begin{pmatrix}
p&-X&0&A\\
r&0&Y&B\\
1&0&0&0\\
0&0&0&F_\xi'(c)
\end{pmatrix}.
\]

Thus

\[
\det A_y=-XYF_\xi'(c).
\]

The branch state-lift is regular under the nondegeneracy assumptions

\[
X\ne0,\qquad Y\ne0,\qquad F_\xi'(c)\ne0.
\]

For a density perturbation, write

\[
\delta E_-=\delta W_\xi(u),\qquad
\delta E_+=\delta W_\xi(v),
\]

\[
\delta M=\delta m_{\rm ext},\qquad
\delta F=\delta F_\xi(c).
\]

Solving \(A_y\delta y+A_\xi\xi=0\) gives

\[
\delta q=-\delta M,
\]

\[
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

The period row remains separate.  In the fixed period chart,

\[
\Pi_q=\Pi_a=\Pi_b=\Pi_c=0.
\]

Therefore the admissible density directions are exactly those satisfying

\[
\delta\Pi(\xi)=0,
\]

plus the sign-linearized admissibility constraints.

The next lemma is therefore:

\[
\boxed{\textbf{Lemma Branch-Parametrized Phi-Euler-Hessian.}}
\]

In the fixed chart, the \(y\)-Euler part is now proved under
\(q,a,b,X,Y\ne0\):

\[
d_y\Phi_{\rm br}=0
\Longleftrightarrow
E_-=E_+=S=0
\]

together with the mass, period, and branch rows.

Indeed,

\[
d_y\Phi_{\rm br}
=(0,1,1,0)+\lambda_M(1,0,0,0)
+\lambda_-(p,-X,0,A)+\lambda_+(r,0,Y,B).
\]

The \(a,b\)-rows give

\[
\lambda_-=\frac1X,\qquad \lambda_+=-\frac1Y.
\]

The \(c\)-row gives

\[
\frac{A}{X}-\frac{B}{Y}=0.
\]

Since

\[
\frac{A}{X}-\frac{B}{Y}
=-\frac{q(aA+bB)}{abXY},
\]

this is equivalent to

\[
S=aW'(u)+bW'(v)=0.
\]

The \(q\)-row only fixes

\[
\lambda_M=-\frac{p}{X}+\frac{r}{Y};
\]

it does not impose an extra scalar condition.

Its second variation has no \(\lambda_F\nabla^2F(c)\) and no
\(\lambda_S\nabla^2S\) term.

### 10.17c Bordered Schur complement on the branch tangent

Let

\[
H=D^2_{(y,\xi)}\Phi_{\rm br}
=
\begin{pmatrix}
H_{yy}&H_{y\xi}\\
H_{\xi y}&H_{\xi\xi}
\end{pmatrix}.
\]

The constrained state response is computed from the branch state-lift system

\[
A_y\delta y+A_\xi\xi=0,\qquad \delta\Pi(\xi)=0,
\]

not from an inverse containing the period row.

Equivalently, \(\delta y=T\xi=-A_y^{-1}A_\xi\xi\), and the reduced Hessian on
actual density perturbations is

\[
\boxed{
G_{\rm br}(\xi,\zeta)
=
D^2_{(y,\xi)}\Phi_{\rm br}
\big((T\xi,\xi),(T\zeta,\zeta)\big),
\qquad
\delta\Pi(\xi)=\delta\Pi(\zeta)=0.
}
\]

If one wants a bordered matrix expression, use the state rows
\(A=(E_-,E_+,M,F)\):

\[
\begin{pmatrix}
H_{yy}&A_y^T\\
A_y&0
\end{pmatrix}
\begin{pmatrix}
\delta y\\
\delta\lambda
\end{pmatrix}
=-
\begin{pmatrix}
H_{y\xi}\\
A_\xi
\end{pmatrix}\xi.
\]

Thus the raw reduced Hessian is

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

Under the regularity assumptions

\[
X\ne0,\qquad Y\ne0,\qquad F_\xi'(c)\ne0,
\]

the bordered matrix is invertible.  Hence \(G_{\rm br}\) is a well-defined
symmetric bilinear form on the actual density tangent space

\[
\mathcal X_\Pi=\{\xi:\delta\Pi(\xi)=0\}.
\]

Symmetry follows from the symmetry of the second Frechet derivative
\(D^2\Phi_{\rm br}\), and the formula above agrees with the bordered Schur
expression because \(T\xi=-A_y^{-1}A_\xi\xi\) is the unique solution of the
linearized branch state equations.

The compact \(g=2\) second-variation condition is not \(G_0\succeq0\) on all
density directions.  It is

\[
\boxed{
\xi^TG_0\xi\ge0
\quad\text{for all actual admissible }\xi
\text{ satisfying }\delta\Pi(\xi)=0
\text{ and the sign-linearized constraints.}
}
\]

Only after this state-lift and period-splitting lemma is in place can the
finite six-row cokernel, endpoint-transfer lift, and curvature-clamp matrix
\(M\) be defined without overcounting.

### 10.17d Density-to-row projection obstruction

The reduced Hessian \(G_{\rm br}\) is now defined on actual density
perturbations, not on six free formal row coordinates.  Let

\[
\rho(\xi)=
(R_0,R_u,R_c,R_v,R_-,R_+,\Pi)(\xi),
\]

and

\[
\mathcal X_\Pi=\{\xi:\Pi(\xi)=0\}.
\]

The naive finite row matrix used in the compact \(g=2\) cokernel argument
would be proof-grade only if

\[
\boxed{
\ker(\rho|_{\mathcal X_\Pi})\subset \operatorname{Rad}(G_{\rm br}).
}
\]

Equivalently, whenever two actual perturbations have the same listed rows,

\[
\rho(\xi)=\rho(\xi'),
\]

one must have

\[
G_{\rm br}(\xi,\zeta)=G_{\rm br}(\xi',\zeta)
\qquad
\forall \zeta\in\mathcal X_\Pi.
\]

Then \(G_{\rm br}\) descends to a unique bilinear form

\[
\bar G_{\rm br}:V\times V\to\mathbb R,
\qquad
V=\rho(\mathcal X_\Pi)\subset\mathbb R^7,
\]

such that

\[
G_{\rm br}(\xi,\zeta)=
\bar G_{\rm br}(\rho\xi,\rho\zeta).
\]

This quotient lemma is now judged false as stated.  The reason is the direct
log-energy term in \(G_{\rm br}\):

\[
\mathcal E_{\log}(\xi,\zeta)
=
\iint -\log|x-y|\,d\xi(x)d\zeta(y).
\]

The map \(\rho\) has finite rank, so
\(\ker(\rho|_{\mathcal X_\Pi})\) is still infinite-dimensional.  One can
choose nonzero smooth signed perturbations supported away from the endpoint
singularities with all seven listed rows zero.  Since \(R_0(\xi)=0\), such
perturbations have zero total mass, and logarithmic energy is positive on
nonzero zero-mass signed perturbations:

\[
\mathcal E_{\log}(\xi,\xi)>0.
\]

Thus these row-kernel perturbations are not in the radical of \(G_{\rm br}\).
A finite-rank edge or state-lift correction cannot make the full log-energy
depend only on finitely many row values.  Therefore the proof must not try to
descend \(G_{\rm br}\) by radical quotient.

The correct replacement is a Feshbach / energy-minimal lift.  Let

\[
W=\ker(\rho|_{\mathcal X_\Pi}).
\]

The next useful lemma is:

\[
\boxed{\textbf{Lemma Log-Energy Positive Kernel and Minimal Row Lift.}}
\]

The sign convention is correct.  For compactly supported finite-energy
zero-mass signed measures,

\[
\widehat{-\log|x|}(t)=\frac{\pi}{|t|}+c\delta_0,
\]

and the \(\delta_0\) term disappears because \(\widehat\mu(0)=0\).  Hence

\[
\mathcal E_{\log}(\mu,\mu)
=\frac12\int_{\mathbb R}\frac{|\widehat\mu(t)|^2}{|t|}\,dt.
\]

Therefore

\[
\mathcal E_{\log}(w,w)>0
\qquad (0\ne w\in W),
\]

provided \(w\) has zero total mass and finite logarithmic energy.

The row map used for the non-log part must be enlarged.  The current rows
\(R_-,R_+\) are differences:

\[
R_-=\delta W(c)-\delta W(u),\qquad
R_+=\delta W(v)-\delta W(c).
\]

The state lift needs \(\delta W(u)\) and \(\delta W(v)\).  These are determined
only after adding the common anchor

\[
R_{\log c}(\xi)=\delta W_\xi(c)
=\int_J\log\frac1{|c-x|}\,d\xi(x).
\]

Therefore replace \(\rho\) by

\[
\boxed{
\rho^\sharp=(R_0,R_u,R_c,R_v,R_-,R_+,R_{\log c},\Pi).
}
\]

Then

\[
\delta E_-=R_{\log c}-R_-,
\qquad
\delta E_+=R_{\log c}+R_+,
\]

\[
\delta M=R_0,\qquad
\delta F(c)=-R_c,\qquad
\delta S=aR_u+bR_v.
\]

No higher derivative rows are needed in the fixed-chart branch-parametrized
Schur calculation.

Let

\[
W^\sharp=\ker(\rho^\sharp|_{\mathcal X_\Pi}).
\]

For every actual row vector

\[
r\in V^\sharp=\rho^\sharp(\mathcal X_\Pi),
\]

construct an \(\mathcal E_{\log}\)-minimal lift \(Sr\) in the energy
completion of \(\mathcal X_\Pi\), satisfying

\[
\rho^\sharp(Sr)=r,\qquad
\mathcal E_{\log}(Sr,w)=0\quad\forall w\in W^\sharp.
\]

This is a Hilbert-space projection statement in the energy completion

\[
H_\Pi=\overline{\mathcal T_\Pi}^{\|\cdot\|_E},
\qquad
\|h\|_E^2=\mathcal E_{\log}(h,h).
\]

There is one important normalization caveat.  The logarithmic energy is a
positive Hilbert norm only on zero-mass directions, or after quotienting the
constant/mass radical.  Therefore the minimal-lift theorem must be formulated
on

\[
H_{0,\Pi}=\{h\in H_\Pi:R_0(h)=0\},
\]

or else \(R_0\) must be split off as a separate finite-dimensional external
coordinate.  In the first formulation the active row map is the restriction of
\(\rho^\sharp\) to the slice \(R_0=0\); its image contains only row vectors
with \(R_0=0\).  Statements about arbitrary \(r\in V^\sharp\) are valid only
after this zero-mass restriction or external-mass split has been made.

Assume the admissible tangent is closed in \(H_\Pi\), \(\rho^\sharp\) extends
continuously to \(H_\Pi\), the target row vector is feasible, and the
functional \(h\mapsto\mathcal E_{\log}(S_0,h)\) is continuous.  Then
Riesz/Lax-Milgram on \(\ker\rho^\sharp\) gives a unique energy-minimizing
completed lift.  The lift need not be a smooth density unless a separate
regularity theorem is proved.

The continuity assumption is valid in the separated fixed-chart regime.  If

\[
J\Subset\mathbb R\setminus\{u,c,v\},
\]

then zero-mass log-energy is equivalent to the \(H^{-1/2}(J)\) norm, and a row

\[
\xi\mapsto \int_J k(x)\,d\xi(x)
\]

is continuous whenever \(k|_J\in H^{1/2}(J)\) modulo constants.  Hence

\[
1,\ (x-u)^{-1},\ (x-c)^{-1},\ (x-v)^{-1},\
L_-,\ L_+,\ \log\frac1{|c-x|}
\]

are continuous rows when \(J\) stays a positive distance from \(u,c,v\).  Here

\[
L_-(x)=\log|x-u|-\log|x-c|,
\qquad
L_+(x)=\log|x-c|-\log|x-v|
\]

is the proof-grade interpretation of the split kernels.  The period kernel
\(\pi_0\) is continuous only if its jumps lie in gaps away from \(J\); a
genuine step jump inside a connected support interval is not \(H^{1/2}\).

Thus this minimal-lift theorem is a separated-chart result.  It fails, or
needs a different chart, when \(J\) reaches \(u,c,v\), when the log anchor is
singular on the support, or when the period row is a topological coordinate
not represented by an \(H^{1/2}\) kernel.

If the non-log part factors through the row map,

\[
G_{\rm br}=\mathcal E_{\log}+B_{\rho^\sharp},\qquad
B_{\rho^\sharp}(\xi,\zeta)=b(\rho^\sharp\xi,\rho^\sharp\zeta),
\]

then every perturbation decomposes as

\[
\xi=Sr+w,\qquad r=\rho^\sharp(\xi),\quad w\in W^\sharp,
\]

and

\[
G_{\rm br}(\xi,\xi)
=\mathcal E_{\log}(w,w)
+\left(\mathcal E_{\log}(Sr,Sr)+b(r,r)\right).
\]

The finite object is therefore the effective form

\[
Q_{\rm eff}(r)=\mathcal E_{\log}(Sr,Sr)+b(r,r)
\qquad (r\in V^\sharp),
\]

not a naive quotient of \(G_{\rm br}\) by \(\ker\rho\).

If this minimal-lift reduction is not proved, the compact proof must keep
\(G_{\rm br}\) on actual densities and make every cokernel vector act through
the functional

\[
\xi\mapsto \lambda\cdot\rho^\sharp(\xi)
=\int K_\lambda(x)\,d\xi(x).
\]

In that formulation \(\lambda\) is meaningful only modulo
\((V^\sharp)^\perp\).  A nonzero ambient row vector that vanishes on
\(V^\sharp\) is not a real obstruction.

There is still a separate finite-row realization lemma, which is useful for
first-variation and Chebyshev tests but does not replace the minimal-lift
lemma.  For kernels

\[
k_0=1,\quad k_u=(x-u)^{-1},\quad k_c=(x-c)^{-1},\quad
k_v=(x-v)^{-1},\quad k_-=L_-,\quad k_+=L_+,\quad
k_{\log c}=\log\frac1{|c-x|},\quad k_\Pi=\pi_0,
\]

define

\[
\operatorname{Rel}
=\left\{\lambda:
\sum_i\lambda_i k_i=0\text{ on }J\right\}.
\]

Then smooth compactly supported density perturbations realize exactly
\(\operatorname{Rel}^\perp\).  If the enlarged kernels are independent, every
period-zero enlarged row vector is realizable.  This follows by choosing bump
functions near points where the kernel evaluation matrix has full rank.

More precisely, if

\[
T:C_c^\infty(J_{\rm reg})\to\mathbb R^8,\qquad
T\eta=\left(\int k_i\,d\eta\right)_i,
\]

then

\[
\operatorname{Im}T=\operatorname{Rel}^{\perp}.
\]

The proof is distributional: \(\lambda\) annihilates \(\operatorname{Im}T\)
iff \(\sum_i\lambda_i k_i=0\) on \(J_{\rm reg}\).  Full row surjectivity is an
extra condition, equivalent to existence of regular points

\[
x_1,\ldots,x_8\in J_{\rm reg}
\]

with

\[
\det(k_i(x_j))_{i,j=1}^8\ne0.
\]

If this determinant is not proved nonzero, keep the actual row space as
\(\operatorname{Rel}^{\perp}\cap\{r_\Pi=0\}\) rather than pretending the
ambient period-zero space is available.

But realization alone does not make \(G_{\rm br}\) finite-dimensional.  It only
guarantees that row test directions are actual density directions.

This is the next hard mouth.  One may not treat

\[
(R_0,R_u,R_c,R_v,R_-,R_+,R_{\log c})
\]

as arbitrary free coordinates until a realization theorem proves the needed
directions are actually in \(V^\sharp\).  The hidden constraints include
period, Cauchy boundary relations, endpoint-difference anchoring, and the fact
that \(R_-,R_+\) are differences rather than absolute endpoint values.

### 10.17e Curvature-clamp Hessian identity package

Once \(Q_{\rm eff}\) has been constructed, the next target is not the curvature
clamp itself but the effective endpoint Hessian identity.  The log-minimal
lift contributes a real nonlocal term

\[
K_{\log}(r,s)=\mathcal E_{\log}(Sr,Ss),
\]

so

\[
Q_{\rm eff}(r,s)=K_{\log}(r,s)+b(r,s).
\]

The old five local entries are therefore not automatic for the finite row
Schur term \(b\).  They must be proved for

\[
P^TQ_{\rm eff}P.
\]

The desired effective identities are the following, with one common positive
scale \(\lambda>0\):

\[
\boxed{
e_u^TMe_u=\lambda a,\qquad
e_v^TMe_v=\lambda b,\qquad
e_\zeta^TMe_\zeta=\lambda Q_c.
}
\]

and

\[
\boxed{
e_u^TMe_\zeta=-\frac{\lambda}{2}\Gamma(c-u),\qquad
e_v^TMe_\zeta=\frac{\lambda}{2}\Gamma(v-c).
}
\]

No \(e_u^TMe_v\) identity is needed for the curvature clamp itself.

For \(x\in(u,c)\), set

\[
A=x-u,\qquad B=c-x,\qquad d_-=c-u,
\]

and test

\[
h_-(x)=Be_u+Ae_\zeta.
\]

Then \(M\succeq0\) gives

\[
0\le h_-^TMh_-
=\lambda\left(aB^2-\Gamma d_-AB+Q_cA^2\right).
\]

Thus

\[
\Gamma d_-AB\le aB^2+Q_cA^2,
\]

which is exactly the left-side curvature-clamp inequality.

For \(x\in(c,v)\), set

\[
A=x-c,\qquad B=v-x,\qquad d_+=v-c,
\]

and test

\[
h_+(x)=Be_\zeta+Ae_v.
\]

Then \(M\succeq0\) gives

\[
0\le h_+^TMh_+
=\lambda\left(Q_cB^2+\Gamma d_+AB+bA^2\right),
\]

equivalently

\[
-\Gamma d_+AB\le Q_cB^2+bA^2.
\]

This is the right-side curvature-clamp inequality.

Status:

These five identities are target identities for the true reduced Hessian after
the branch-parametrized Phi-Euler-Hessian lemma, fixed-chart state-lift,
minimal-lift/Feshbach reduction, and row realization.  If the log-minimal
contribution does not collapse to these entries, the curvature clamp must be
rewritten with the actual effective entries
\[
m_{uu},m_{vv},m_{\zeta\zeta},m_{u\zeta},m_{v\zeta}.
\]

### 10.17f Retired free-\(F(c)\) derivative convention

If \(F\) is held as a fixed dual Cauchy transform

\[
F(z)=\int\frac{d\lambda(t)}{z-t},
\]

then with respect to \(y=(q,a,b,c)\),

\[
\nabla_yF(c)=(0,0,0,F'(c)),
\]

and

\[
\nabla_y^2F(c)=
\begin{pmatrix}
0&0&0&0\\
0&0&0&0\\
0&0&0&0\\
0&0&0&F''(c)
\end{pmatrix},
\]

where

\[
F'(c)=-\int\frac{d\lambda(t)}{(c-t)^2}<0,
\qquad
F''(c)=2\int\frac{d\lambda(t)}{(c-t)^3}.
\]

If \(F\) varies with \(y\) through the finite-gap parameters, this is not
enough.  The proof must specify the map

\[
(q,a,b,c,W\text{-data})
\longmapsto
\lambda
\quad\text{or}\quad
(P,Q,R),
\]

otherwise \(F_q,F_a,F_b,F_{zy_i}\), and \(F_{y_iy_j}\) are undefined.

This convention was useful because it exposed the obstruction, but it is not
the proof-grade Hessian convention anymore.  The calculation gives, if one
uses the free row

\[
R_F(y,\xi)=F_\xi(c),
\]

then at fixed \(\xi\),

\[
\nabla_yR_F=(0,0,0,F_\xi'(c)).
\]

This is exactly why the free multiplier \(\lambda_F\) contaminates the
\(c\)-Euler row.  The active convention from §10.17b removes
\(\lambda_FF_\xi(c)\) from \(\Phi_{\rm br}\) and keeps only the branch tangent
condition

\[
\delta F_\xi(c)=0.
\]

Retired calculation retained for audit:

\[
y=(q,a,b,c)
\]

moves only the local primal neck.  The dual transform varies through
\(\xi\), not through hidden \(y\)-dependence.  Thus the row is

\[
R_F(y,\xi)=F_\xi(c).
\]

At fixed \(\xi\),

\[
\nabla_yR_F=(0,0,0,F_\xi'(c)),
\]

\[
\nabla_y^2R_F=
\begin{pmatrix}
0&0&0&0\\
0&0&0&0\\
0&0&0&0\\
0&0&0&F_\xi''(c)
\end{pmatrix}.
\]

Therefore

\[
H_{yy}^{(F)}=\lambda_FF_\xi''(c)e_ce_c^T.
\]

If the density coordinate changes \(F_\xi\) by

\[
f_i(z)=\partial_{\xi_i}F_\xi(z),
\]

and the \(\xi\)-coordinates are affine, then

\[
\partial_{c\xi_i}^2R_F=f_i'(c),
\qquad
\partial_{\xi_i\xi_j}^2R_F=0.
\]

So

\[
H_{c\xi_i}^{(F)}=\lambda_Ff_i'(c),
\qquad
H_{\xi_i\xi_j}^{(F)}=0
\]

for the \(F\)-row contribution.

### 10.17g Updated blocker for Schur complement

The hard mouth is now narrower than the old "finite row quotient" target.
The naive radical quotient is retired.  The active target is the separated
fixed-chart Feshbach reduction:

\[
\boxed{
\text{prove the separated-chart minimal-lift theorem for }Q_{\rm eff}.
}
\]

The old target

\[
d_y\Phi=0
\Longleftrightarrow
E_-=E_+=S=F(c)=0
\]

with \(F(c)\) included as a free multiplier row is false as stated.  The
correct target is:

\[
\boxed{
d_y\Phi_{\rm br}=0
\Longleftrightarrow
E_-=E_+=S=0
\text{ plus mass and period rows, while }F(c)=0\text{ supplies the branch
state-lift row.}
}
\]

Only then define the Hessian blocks

\[
H_{yy},\qquad H_{\xi y},\qquad H_{\xi\xi}.
\]

Until this lemma is proved, the expression

\[
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
\end{pmatrix}
\]

on \(\delta\Pi=0\) is only a formal target, not a theorem.

After this turn, the state-lift and fixed-chart Hessian well-definedness
statements are recorded.  The remaining obstruction is not to prove that
\(G_{\rm br}\) descends by radical quotient.  That route is false because the
row kernel still has positive log energy.  The replacement is the following
theorem queue.

1.  Separated-chart Feshbach minimal lift.  In the Hilbert completion
    \(H_{0,\Pi}\), or after splitting the mass coordinate away from the
    energy space, with continuous \(\rho^\sharp\) and closed
    \(W^\sharp=\ker\rho^\sharp\), every feasible row vector
    \(r\in V^\sharp\) has a unique lift

    \[
    Sr\in (W^\sharp)^{\perp_{\mathcal E}}\cap(\rho^\sharp)^{-1}(r).
    \]

    If

    \[
    G_{\rm br}=\mathcal E_{\log}
    +b\circ(\rho^\sharp,\rho^\sharp),
    \]

    then

    \[
    G_{\rm br}(Sr+w,Ss+w')
    =
    Q_{\rm eff}(r,s)+\mathcal E_{\log}(w,w'),
    \]

    where

    \[
    Q_{\rm eff}(r,s)=\mathcal E_{\log}(Sr,Ss)+b(r,s).
    \]

    This is the first theorem to prove.  It legitimizes \(Q_{\rm eff}\); it
    does not compute the endpoint Hessian entries.

    Abstract proof.  Let \(H\) be a real Hilbert space with inner product
    \(E\), and let

    \[
    \rho^\sharp:H\to\mathbb R^m
    \]

    be continuous linear.  Put

    \[
    W=\ker\rho^\sharp,\qquad V=\rho^\sharp(H).
    \]

    Then \(W\) is closed and

    \[
    H=W\oplus W^{\perp_E}.
    \]

    For \(r\in V\), choose any \(\xi_0\) with \(\rho^\sharp(\xi_0)=r\), write
    \(\xi_0=w_0+u_0\) in the above decomposition, and define

    \[
    Sr=u_0.
    \]

    Since \(w_0\in W\), \(\rho^\sharp(Sr)=r\).  If two such lifts existed,
    their difference would lie in \(W\cap W^{\perp_E}=\{0\}\), so the lift is
    unique.  Hence every \(\xi\in H\) has the unique decomposition

    \[
    \xi=S\rho^\sharp(\xi)+w,\qquad w\in W.
    \]

    If

    \[
    G(\xi,\eta)=E(\xi,\eta)+b(\rho^\sharp\xi,\rho^\sharp\eta),
    \]

    then for \(\xi=Sr+w\) and \(\eta=Ss+w'\),

    \[
    G(\xi,\eta)
    =
    E(Sr,Ss)+E(w,w')+b(r,s)
    =
    Q_{\rm eff}(r,s)+E(w,w').
    \]

    Thus, if \(G\ge0\) on the relevant closed feasible tangent space, then
    \(Q_{\rm eff}\ge0\) on its feasible row image by testing \(\xi=Sr\).

    Failure modes.  This abstract proof fails if the log energy has not been
    turned into a positive Hilbert norm, if \(\rho^\sharp\) is not continuous
    in the energy topology, if \(r\) is a formal row vector outside
    \(\rho^\sharp(H)\), if the non-log Hessian does not factor through
    \(\rho^\sharp\), or if second-variation nonnegativity is known only on a
    cone that does not contain the minimal lifts as two-sided feasible
    directions.

2.  Endpoint-transfer realization.  One must prove that the three columns of
    the endpoint-transfer map

    \[
    P:\operatorname{span}\{e_u,e_v,e_\zeta\}\to V^\sharp
    \]

    are actual feasible row directions.  Full row surjectivity is stronger
    than needed.  It is enough to realize these three columns, with the period
    row fixed and inside \(\operatorname{Rel}^{\perp}\).

    The proof target is the following narrow theorem.

    \[
    \boxed{
    \textbf{EndpointTransferRealization3:}\quad
    P e_u,\ P e_v,\ P e_\zeta
    \in \rho^\sharp(\mathcal X_{\Pi,\mathrm{lin}}).
    }
    \]

    Equivalently, in the regular separated compact \(g=2\) chart, construct
    actual perturbations

    \[
    \xi_u,\xi_v,\xi_\zeta\in\mathcal X_{\Pi,\mathrm{lin}}
    \]

    such that

    \[
    \rho^\sharp(\xi_j)=P e_j,\qquad j\in\{u,v,\zeta\}.
    \]

    Here \(\mathcal X_{\Pi,\mathrm{lin}}\) means the two-sided linearized
    critical tangent in the fixed-period chart.  If the admissible object is
    only a cone, each direction used in \(P^TQ_{\rm eff}P\) must lie in the
    lineality of that cone, or the PSD matrix argument must be replaced by a
    second-order cone KKT argument.

    The three geometric columns are:

    \[
    e_u:\text{ move the lower endpoint }u
    \text{ of }L_-=\int_u^c\frac{ds}{x-s},
    \]

    \[
    e_v:\text{ move the upper endpoint }v
    \text{ of }L_+=\int_c^v\frac{ds}{x-s},
    \]

    and

    \[
    e_\zeta=-e_{c^-}+e_{c^+},
    \]

    the central split transfer across the neck.  This is not a free
    \(F(c)\)-multiplier direction and not a translation of the whole chart.

    For

    \[
    p_j=P e_j
    =(r_{0j},r_{uj},r_{cj},r_{vj},r_{-j},r_{+j},r_{\log j},r_{\Pi j}),
    \]

    proof-grade realization requires

    \[
    r_{0j}=0,\qquad r_{\Pi j}=0
    \]

    in the zero-mass fixed-period formulation.  If an endpoint convention
    produces \(\delta q_j\ne0\), then the proof is no longer on \(H_{0,\Pi}\)
    and \(R_0\) must be split off as an external finite coordinate.

    The branch-state row equations for each column are

    \[
    \ell_-\,\delta q_j-X\,\delta a_j+A\,\delta c_j
    +r_{\log j}-r_{-j}=0,
    \]

    \[
    \ell_+\,\delta q_j+Y\,\delta b_j+B\,\delta c_j
    +r_{\log j}+r_{+j}=0,
    \]

    \[
    \delta q_j+r_{0j}=0,\qquad
    F_c\,\delta c_j-r_{cj}=0,
    \]

    where

    \[
    \ell_-=\log(1/a),\qquad \ell_+=\log(1/b),\qquad
    A=W'(u),\qquad B=W'(v),\qquad F_c=F_\xi'(c).
    \]

    These equations do not solve the period row.  Period-zero is a separate
    realizability condition:

    \[
    \Pi(\xi_j)=0.
    \]

    The relation constraints must also be checked.  For every

    \[
    \lambda\in\operatorname{Rel},
    \qquad
    \sum_i\lambda_i k_i=0\text{ on }J_{\rm reg},
    \]

    one needs

    \[
    \lambda\cdot p_j=0.
    \]

    Thus a formal endpoint column is not proof-grade unless it lies in
    \(\operatorname{Rel}^{\perp}\cap\{r_\Pi=0\}\), with the correct
    zero-mass or external-mass convention, and is represented by an actual
    two-sided feasible density perturbation.

    Stop conditions for this line:

    - some \(P e_j\) is only an ambient endpoint row and not an actual row
      image;
    - some \(P e_j\notin\operatorname{Rel}^{\perp}\) or has nonzero period;
    - the mass convention is inconsistent with the zero-mass Hilbert space;
    - the minimal lift exists only in the completion and cannot be
      approximated by positivity-preserving density perturbations;
    - the realized directions are one-sided cone directions, not lineality
      directions usable in a PSD matrix argument.

    If this three-column theorem fails, the finite matrix route using
    \(P^TQ_{\rm eff}P\) must stop.  The only replacements are an
    actual-density proof using \(G_{\rm br}\) directly, or a cone formulation
    that proves the specific combinations \(Be_u+Ae_\zeta\) and
    \(Be_\zeta+Ae_v\) are two-sided feasible.

    Audit after trying to determine the three columns:

    The branch-state equations do not by themselves define \(P\).  They only
    give compatibility equations for a chosen endpoint convention and a chosen
    actual density perturbation.  Therefore the next missing definition is the
    explicit endpoint-transfer map

    \[
    P:\operatorname{span}\{e_u,e_v,e_\zeta\}\to\mathbb R^8.
    \]

    Until \(P\) is fixed, \(P e_j\in V^\sharp\) cannot be proved or refuted.

    For any column \(j\), write

    \[
    p_j=(r_{0j},r_{uj},r_{cj},r_{vj},r_{-j},r_{+j},
    r_{\log j},r_{\Pi j}).
    \]

    Given a state displacement
    \((\delta q_j,\delta a_j,\delta b_j,\delta c_j)\), the branch-state rows
    only force

    \[
    r_{0j}=-\delta q_j,\qquad r_{cj}=F_c\delta c_j,
    \]

    \[
    r_{-j}=\ell_-\,\delta q_j-X\,\delta a_j
    +A\,\delta c_j+r_{\log j},
    \]

    and

    \[
    r_{+j}=-\ell_+\,\delta q_j-Y\,\delta b_j
    -B\,\delta c_j-r_{\log j}.
    \]

    They do not determine \(r_{uj}\), \(r_{vj}\), \(r_{\log j}\), period
    realization, or the actual density perturbation.

    Natural formal conventions give useful candidates, but not proofs.

    For \(e_u\), if it means \(\delta u=1\) with \(c,v,q\) fixed, then

    \[
    \delta q_u=0,\qquad \delta a_u=-1,\qquad
    \delta b_u=0,\qquad \delta c_u=0,
    \]

    and the candidate family is

    \[
    p_u=(0,r_{uu},0,r_{vu},r_{\log u}+X,-r_{\log u},r_{\log u},0).
    \]

    If instead \(e_u\) means increasing the length \(a\), the \(X\)-term
    changes sign:

    \[
    p_u=(0,r_{uu},0,r_{vu},r_{\log u}-X,-r_{\log u},r_{\log u},0).
    \]

    For \(e_v\), if it means \(\delta v=1\) with \(c,u,q\) fixed, then

    \[
    \delta q_v=0,\qquad \delta a_v=0,\qquad
    \delta b_v=1,\qquad \delta c_v=0,
    \]

    and the candidate family is

    \[
    p_v=(0,r_{uv},0,r_{vv},r_{\log v},-Y-r_{\log v},r_{\log v},0).
    \]

    With the extra normalization \(\partial_vL_+=k_v\) and
    \(r_{\log v}=0\), this becomes the simple formal candidate

    \[
    p_v^0=(0,0,0,1,0,-Y,0,0).
    \]

    For \(e_\zeta\), if it means moving the center \(c\) while \(u,v,q\) are
    fixed, then

    \[
    \delta q_\zeta=0,\qquad \delta a_\zeta=1,\qquad
    \delta b_\zeta=-1,\qquad \delta c_\zeta=1,
    \]

    and

    \[
    r_{c\zeta}=F_c.
    \]

    The candidate family is

    \[
    p_\zeta(\eta,r_u,r_v)
    =
    \left(0,r_u,F_c,r_v,\eta-\frac qa,
    -\eta-\frac qb,\eta,0\right).
    \]

    The normalized formal candidate \(\eta=r_u=r_v=0\) is

    \[
    p_\zeta^0=
    \left(0,0,F_c,0,-\frac qa,-\frac qb,0,0\right).
    \]

    These candidates are only branch-compatible ambient row vectors.  To become
    proof-grade columns they must satisfy

    \[
    p_j\in\operatorname{Rel}^{\perp},\qquad r_{\Pi j}=0,
    \]

    with the correct zero-mass or external-mass convention, and must be
    realized by actual two-sided feasible perturbations

    \[
    \xi_j\in\mathcal X_{\Pi,\mathrm{lin}},
    \qquad \rho^\sharp(\xi_j)=p_j.
    \]

    The immediate next task is therefore not yet to compute
    \(P^TQ_{\rm eff}P\), but to define the endpoint convention for \(P\) and
    then test the three candidate columns against \(\operatorname{Rel}\),
    period-zero, and actual-density realizability.

    Formal \(P^0\) convention.  Use endpoint-length orientation, not raw
    left-endpoint position orientation:

    \[
    e_u^0=\partial_a=-\partial_u,\qquad
    e_v^0=\partial_b=\partial_v,
    \qquad
    e_\zeta^0=\partial_c\text{ with }u,v,q\text{ fixed}.
    \]

    Thus

    \[
    (\delta q_u,\delta a_u,\delta b_u,\delta c_u)=(0,1,0,0),
    \]

    \[
    (\delta q_v,\delta a_v,\delta b_v,\delta c_v)=(0,0,1,0),
    \]

    and

    \[
    (\delta q_\zeta,\delta a_\zeta,\delta b_\zeta,\delta c_\zeta)
    =(0,1,-1,1).
    \]

    Normalize the endpoint-kernel rows by

    \[
    \partial_aL_-=k_u,\qquad \partial_bL_+=k_v,
    \]

    and set the free ambient anchor choices

    \[
    r_{\log u}=r_{\log v}=\eta=0,\qquad
    r_{vu}=r_{uv}=r_u=r_v=0.
    \]

    This gives the formal branch-compatible convention

    \[
    p_u^0=(0,1,0,0,-X,0,0,0),
    \]

    \[
    p_v^0=(0,0,0,1,0,-Y,0,0),
    \]

    and

    \[
    p_\zeta^0=\left(0,0,F_c,0,-\frac qa,-\frac qb,0,0\right).
    \]

    These columns have period coordinate \(0\).  They are still not known to
    be actual row images.  With

    \[
    \lambda=(\lambda_0,\lambda_u,\lambda_c,\lambda_v,
    \lambda_-,\lambda_+,\lambda_{\log},\lambda_\Pi)
    \in\operatorname{Rel},
    \]

    the necessary and sufficient row-level annihilation conditions for the
    three columns are

    \[
    \lambda_u-X\lambda_-=0,
    \]

    \[
    \lambda_v-Y\lambda_+=0,
    \]

    and

    \[
    F_c\lambda_c-\frac qa\,\lambda_- -\frac qb\,\lambda_+=0.
    \]

    If the stronger determinant condition

    \[
    \det(k_i(x_j))_{i,j=1}^8\ne0
    \]

    is proved for some regular points \(x_1,\ldots,x_8\in J_{\rm reg}\), then
    \(\operatorname{Rel}=0\) and these annihilation checks are automatic.
    Without that determinant, the three displayed identities must be proved for
    all \(\lambda\in\operatorname{Rel}\).

    If those identities hold, the existing bump realization lemma gives
    signed smooth density perturbations with these rows, supported in the
    regular interior.  This is only row-level realization.  To use the PSD
    matrix \(P^{0T}Q_{\rm eff}P^0\), one still has to prove the bumps are
    two-sided feasible critical directions, or approximate such directions
    while preserving positivity.  If only one-sided feasibility is available,
    the proof must switch to the actual-density cone formulation.

3.  Effective endpoint Hessian identity.  Only after the previous two steps
    can one define

    \[
    M=P^TQ_{\rm eff}P.
    \]

    The desired five local entries must be proved for this \(M\), not for the
    finite Schur term \(b\) alone.  The nonlocal contribution
    \(K_{\log}(r,s)=\mathcal E_{\log}(Sr,Ss)\) may change the entries.

4.  Effective clamp.  If the five old entries hold, the existing curvature
    clamp follows.  If they do not hold, the compact proof must use the actual
    entries

    \[
    m_{uu},m_{vv},m_{\zeta\zeta},m_{u\zeta},m_{v\zeta}.
    \]

    The available inequalities are then only

    \[
    m_{uu}B^2+2m_{u\zeta}AB+m_{\zeta\zeta}A^2\ge0
    \quad (u<x<c),
    \]

    and

    \[
    m_{\zeta\zeta}B^2+2m_{v\zeta}AB+m_{vv}A^2\ge0
    \quad (c<x<v).
    \]

5.  Wronskian/sign-pattern obstruction.  Even after a clamp is obtained, one
    still has to prove that it forces the two-dimensional KKT cokernel
    Wronskian to have the sign pattern needed to contradict admissibility.
    This step is not automatic from the six-kernel Chebyshev determinant.

Stop/go judgment:

\[
\boxed{\text{GO, but conditional and narrow.}}
\]

Continue this route only through the \(Q_{\rm eff}\) theorem queue above.  If
the actual effective entries cannot imply the Wronskian sign contradiction,
stop the compact \(g=2\) Hessian-clamp line; do not revive the retired
free-\(F(c)\) row, the naive row quotient, or a standalone six-kernel
determinant closure.

Relation to the full theorem:

\[
\boxed{
Q_{\rm eff}\text{ is only the compact non-pinched }g=2\text{ hard mouth.}
}
\]

Closing it would not by itself prove \(L_-=M_*\).  The full exact proof still
needs the one-cut upper construction, the corrected \(g=1\) branch, the
pinching/degeneration lemma, the high-genus local-neck reduction, the
regularity-removal interface, and the standard normalized minimizer reduction.
