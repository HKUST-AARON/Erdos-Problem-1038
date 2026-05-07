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

For the infimum side, the current one-cut candidate / provisional upper
candidate is

\[
M_{\rm oc}=x_R-x_L=1.8344304757626617\ldots,
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

The gate chain below gives a conditional proof skeleton whose target conclusion is

\[
L_- = M_{\rm oc}
\]

in the normalization used throughout this ledger.

Thus the current exact-route status is not an unconditional equality.  The
honest status is:

\[
\boxed{
\text{conditional skeleton: if the remaining sign/compactness/regularity
lemmas are closed, then }L_- = M_{\rm oc}.
}
\]

The decimal \(1.8344304757626617\ldots\) is only the numerical evaluation of
the current one-cut candidate / provisional upper candidate.  It must not be
presented as a completed proof of the original problem until the open gates
below are upgraded to proof-grade lemmas.

### 0.1 Frozen Exact-Route Statements

These are the statements targeted by the gate chain below.  They should not
be blurred with the older finite-atom progress bound.

**Theorem U: one-cut upper construction.**

\[
\boxed{L_-\le M_{\rm oc}}
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
|E_{\mu_{a_*}}|=x_R-x_L=M_{\rm oc}.
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
|E_\mu|<M_{\rm oc}.
\]

This is the hard theorem.  It requires global finite-gap classification, not
more local slab tuning.

**Final exact statement.**

If Theorem U and Theorem L are proved in the same normalization, then

\[
\boxed{L_- = M_{\rm oc}=1.8344304757626617\ldots}.
\]

Current audit: the ledger contains a route skeleton, but Gate 1
\(\text{SchurBlockTotalPositivityLemma}\), Gate 3 boundary compactness,
Gate 4 high-genus Schur complement/global-capacity control, and Gate 5/Lemma R
still need expansion into stand-alone proof-grade lemmas before this final
boxed equality can be treated as an unconditional proof.  Gate 6 is the current
proof-grade upper construction.

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
not the route that can prove \(L_-\ge M_{\rm oc}\).

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
- it is not close to the conjectural \(M_{\rm oc}\).

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

It is not a proof of the exact value \(M_{\rm oc}\), and it is not a full
unconditional proof of the original polynomial problem.

## 3. Corrected Two-Interval Exact Route

The exact route is the corrected endpoint-atom two-interval finite-gap route.
This is the route that could plausibly lead to the exact value \(M_{\rm oc}\).

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
- not a global proof of \(L_- = M_{\rm oc}\).

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
L_-\le M_{\rm oc}.
\]

This still needs a clean written proof in the same normalization as the lower
bound.  It is conceptually the easier side.

### 5.2 Lower bound

To prove

\[
L_-\ge M_{\rm oc},
\]

one must show that every regular counterexample with

\[
|E|<M_{\rm oc}
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

The compact \(g=2\) hard mouth is now narrower than the earlier KKT/Hessian
ledger suggested.  The regular free-period chamber is excluded, and the
rank-defect chamber has been reduced to the raw augmented circuit obstruction.
The active Gate 1 target is therefore:

1. use the repaired moving Schiffer columns
   \(H_\gamma^{\rm rep}=QD\,\Delta_\gamma P-PD\,\Delta_\gamma Q
   -\frac12PQD_\gamma\);
2. solve the finite cone-envelope problem on \(Z_0\) through majorants
   \(G_\theta=\theta\cdot V_S-V_\Pi\);
3. prove the strict affine and homogeneous margin inequalities for
   \(P_\theta=\kappa Q^2-\sum_\gamma\theta_\gamma H_\gamma^{\rm rep}\);
4. or replace the first-order route with genuine second-variation data.

The endpoint-period quotient obstruction below shows that rank,
Schur-complement form, or endpoint interpolation quotient data alone cannot
produce the required strict lifted margin.  The next live first-order route
must use the actual \(Z_0\) contact/alternation structure, not only quotient
linear algebra.

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

### 9.1 One-cut upper construction at \(M_{\rm oc}\)

Target theorem:

\[
\boxed{L_-\le M_{\rm oc}}.
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
   |E_{\mu_{a_*}}|=x_R-x_L=M_{\rm oc}.
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

2026-05-06 one-cut audit.

The candidate shape and the mass computation are solid.  With

\[
s=\sqrt{2(1+a)},\qquad c=A(a)s,
\]

the identity

\[
\frac1\pi\int_a^1
\frac{dx}{(x+1)\sqrt{(1-x)(x-a)}}=\frac1s
\]

gives continuous mass \(1-A(a)\), so the total mass is one after adding
\(A(a)\delta_{-1}\).  The displayed derivative has the correct probability
normalization at infinity:

\[
U'_a(z)\sim-\frac1z.
\]

The upper construction is nevertheless not yet a proof-grade theorem.  The
next write-up must define \(a_*,x_L,x_R\) by exact equations, not by decimal
values.  A minimal acceptable definition is:

\[
A(a)=
\frac{\log(4/(1-a))}
{\log 2+sJ(a)},
\]

with \(J(a)\) as above, or equivalently after proving the closed form

\[
\log 2+sJ(a)=\log\frac{1+y}{1-y},
\qquad y=\sqrt{\frac{1+a}{2}}.
\]

Then \(a_*,x_L,x_R\) should be defined by the exterior zero equations

\[
U_{a_*}(x_L)=0,\qquad U_{a_*}(x_R)=0,
\]

together with the extremality or normalization equation that selects the
candidate branch.  The proof must also give an exterior potential formula, for
example by integrating \(U'_a\) with the convention \(U_a(z)+\log|z|\to0\) at
infinity, and then prove a sign/monotonicity table on

\[
(-\infty,-1),\qquad (-1,c-1),\qquad (c-1,a),\qquad [a,1].
\]

Only after that table is written can one conclude that

\[
E_{\mu_{a_*}}=(x_L,x_R)
\]

up to endpoints and hence \(|E_{\mu_{a_*}}|=x_R-x_L=M_{\rm oc}\).  The branch
convention should be fixed explicitly:

\[
R_a(z)\sim z,\qquad R_a(z)<0\quad(z<a),
\]

with the boundary value on \((a,1)\) chosen so that \(U_a\) is constant on the
cut.

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
|E|<M_{\rm oc}
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
|E|=(R_0-L_0)+(v-u)\ge M_{\rm oc}.
}
\]

The compact branch is closed if one proves that no positive non-pinched
finite-gap point with \(|E|<M_{\rm oc}\) satisfies the KKT equations, positivity, and
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

2026-05-06 first-order cokernel audit.

There is a second compact \(g=2\) exit besides
EffectiveNeckSchurPositive: use the first-order KKT cokernel directly.  The
calculation above is valid, but it is only a reduction, not a closure of the
compact chamber.

In the compact neck notation

\[
a=c-u,\qquad b=v-c,\qquad
p=\log(1/a),\qquad r=\log(1/b),
\]

write

\[
X=U'(u)>0,\qquad Y=U'(v)<0,\qquad F_c=F'(c)<0,
\]

and

\[
A=W'(u),\qquad B=W'(v),\qquad A_2=W''(u),\qquad B_2=W''(v).
\]

With rows ordered as

\[
(\mathcal L,M,F_c,\widetilde E_-,\widetilde E_+,S)
\]

and variables ordered as \((q,a,b,c)\), the local block is

\[
A_{\rm loc}=
\begin{pmatrix}
0&1&1&0\\
1&0&0&0\\
0&0&0&F_c\\
p&-X&0&A\\
r&0&Y&B\\
0&A-aA_2&B+bB_2&aA_2+bB_2
\end{pmatrix}.
\]

For density jets

\[
(\xi_0,\xi_u,\xi_c,\xi_v,\xi_-,\xi_+),
\]

the corresponding block is

\[
B_{\rm dens}=
\begin{pmatrix}
0&0&0&0&0&0\\
1&0&0&0&0&0\\
0&0&-1&0&0&0\\
0&0&0&0&-1&0\\
0&0&0&0&0&1\\
0&a&0&b&0&0
\end{pmatrix}.
\]

Direct multiplication gives a left-null basis

\[
\nu_1=
\left(
-Y,\
-r+\frac{Yp}{X},\
\frac{AY}{F_cX}-\frac BF_c,\
-\frac YX,\
1,\
0
\right),
\]

\[
\nu_2=
\left(
-B-bB_2,\
\frac{p(-A+aA_2+B+bB_2)}{X},\
-\frac{
A^2-AaA_2-AB-AbB_2+aA_2X+bB_2X
}{F_cX},\
\frac{A-aA_2-B-bB_2}{X},\
0,\
1
\right).
\]

Pushing this basis through \(B_{\rm dens}\) recovers the two explicit
cokernel rows already recorded in 9.9.  Under the stationarity equation

\[
aA+bB=0
\]

one has

\[
B=-\frac abA,\qquad Y=-\frac abX,\qquad AY-BX=0.
\]

Thus the two adjoint kernels simplify to

\[
\boxed{
K_1(x)=
-r-\frac abp-\frac ab L_-(x)+L_+(x).
}
\]

Define

\[
\Gamma=\frac{-A+aA_2+B+bB_2}{X},
\qquad
Q_c=
\frac{
A^2-AaA_2-AB-AbB_2+aA_2X+bB_2X
}{F_cX}.
\]

Then

\[
\boxed{
K_2(x)=
p\Gamma+\frac a{x-u}+\frac{Q_c}{x-c}
+\frac b{x-v}+\Gamma L_-(x).
}
\]

The local sign lemma gives \(\Gamma>0\) and \(Q_c<0\), but these signs alone
do not prove that \(\operatorname{span}\{K_1,K_2\}\) contains no admissible
oriented compact sign-pattern kernel.  The first-order route therefore has
the following honest target:

\[
\boxed{
\text{prove no nonzero }\theta_1K_1+\theta_2K_2
\text{ has the admissible oriented compact sign pattern.}
}
\]

This is sharper than the old six-moment wording.  The six-kernel Chebyshev
determinant remains useful, but by itself it only controls zeros in the
ambient six-dimensional span; it does not automatically rule out the above
two-dimensional subspace.

The naked Wronskian closure also does not follow from \(Q_c<0\) and
\(\Gamma>0\).  Put \(y=x-c\).  Then

\[
x-u=y+a,\qquad x-c=y,\qquad x-v=y-b,
\]

\[
L_-'(x)=-\frac{a}{y(y+a)},\qquad
L_+'(x)=-\frac{b}{y(y-b)}.
\]

Writing

\[
K_1=R_1-\frac abL_-+L_+,\qquad
R_1=-r-\frac abp,
\]

and

\[
K_2=R_2+\Gamma L_-,
\qquad
R_2=p\Gamma+\frac a{y+a}+\frac{Q_c}{y}+\frac b{y-b},
\]

the Wronskian \(W=K_1K_2'-K_1'K_2\) has

\[
\boxed{
C_+(y)=
-\frac a{(y+a)^2}
-\frac{Q_c}{y^2}
-\frac b{(y-b)^2}
-\frac{\Gamma a}{y(y+a)}.
}
\]

and

\[
\boxed{
C_-(y)=
\frac ab
\left(
\frac a{(y+a)^2}
+\frac{Q_c}{y^2}
+\frac b{(y-b)^2}
\right)
+\frac{\Gamma b}{y(y-b)}.
}
\]

Since \(Q_c<0\), the term \(-Q_c/y^2\) in \(C_+\) is positive while the other
terms can oppose it; in \(C_-\), the term \(Q_c/y^2\) is negative while the
other terms can oppose it.  Varying the allowed relative size of \(|Q_c|\)
already changes the sign balance in these coefficients.  Hence

\[
\boxed{
Q_c<0,\ \Gamma>0
\not\Rightarrow
W\text{ has a fixed oriented sign.}
}
\]

The first-order Wronskian route is therefore downgraded to a conditional
route.  It needs an additional global oval inequality controlling the active
ovals, coefficient sizes, and endpoint signs.  Without such a theorem, the
main compact \(g=2\) route remains EffectiveNeckSchurPositive; if that fails,
the fallback is an actual-entry Wronskian theorem or direct density/cone KKT,
not a revival of the naked local-sign Wronskian argument.

### 9.12 Curvature clamp

Status note, 2026-05-06: this is the historical clamp formulation.  It should
not be read as a proved consequence of the current local \(Q_c<0\) sign lemma.
Under the Feshbach correction, any clamp must be rederived from the actual
entries of \(P^{0T}(B+C^{-1})P^0\), or replaced by
EffectiveNeckSchurPositive / cone KKT.

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

This was an earlier conditional Hessian hard mouth.  It is not the current
Gate 1 closure criterion.  The present rank-defect hard mouth is the raw
augmented circuit obstruction and the MovingSchifferMajorantSignTheorem
recorded in the later Gate 1 ledger.

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
finite-gap counterexamples without increasing }|E_\mu|\text{ past }M_{\rm oc}.
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
L_-\ge M_{\rm oc}.
\]

Status update:

- this was the earlier interface form of Lemma R;
- Gate 5 below records the regularity-removal route, but it still needs a
  proof-grade Lemma R before final assembly;
- the historical warning is kept only to explain why Lemma R had to be made
  explicit before claiming the exact infimum.

## 10. Active Global Finite-Gap Classification Attempt

This section starts the actual global route.  It should be updated before any
new computational work.  The target is not another local certificate; the
target is a regular finite-gap classification theorem.

### 10.1 Regular finite-gap classification theorem

Working theorem:

\[
\boxed{
\text{No admissible regular finite-gap minimizer has } |E_\mu|<M_{\rm oc}.
}
\]

The exact lower-bound proof is intended to be:

\[
\text{regular finite-gap classification}
+\text{Lemma R}
\Rightarrow
L_-\ge M_{\rm oc}.
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
\(M_{\rm oc}-|E|\), all Hessian signs must be flipped consistently.

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

    Rel audit.  The seven non-period kernels

    \[
    1,\quad (x-u)^{-1},\quad (x-c)^{-1},\quad (x-v)^{-1},
    \quad L_-,\quad L_+,\quad \log\frac1{|c-x|}
    \]

    are linearly independent on any nonempty regular interval separated from
    \(u,c,v\).  Indeed, writing

    \[
    L_-=\log|x-u|-\log|x-c|,\qquad
    L_+=\log|x-c|-\log|x-v|,
    \]

    differentiating a putative relation gives a rational function.  Comparing
    the singular parts at \(u,c,v\) first kills the logarithmic coefficients,
    then the simple-pole coefficients, and finally the constant coefficient.

    The eighth kernel \(k_\Pi=\pi_0\) is the only obstruction to automatic
    \(\operatorname{Rel}=0\).  If \(J_{\rm reg}\) lies entirely in one period
    region, then \(\pi_0\) is constant on \(J_{\rm reg}\), so \(k_\Pi\) is
    proportional to \(k_0\) there and \(\operatorname{Rel}\ne0\).  If
    \(J_{\rm reg}\) contains regular pieces on which \(\pi_0\) takes two
    distinct values, for example \(1\) and \(-\theta_{\rm per}\), then the
    remaining relation

    \[
    \lambda_0+\lambda_\Pi\pi_0=0
    \]

    forces \(\lambda_0=\lambda_\Pi=0\).  In that multi-piece case
    \(\operatorname{Rel}=0\), and the three \(P^0\) row-level checks are
    automatic.

    Proof detail for the two-period \(\operatorname{Rel}=0\) shortcut.
    Suppose a relation holds on a regular support

    \[
    J_{\rm reg}=J_1\cup J_2,
    \]

    where \(J_1,J_2\) contain genuine open regular intervals, are separated
    from \(u,c,v\), have fixed real log branches, and the period row takes two
    different constant values, say

    \[
    \pi_0|_{J_1}=1,\qquad \pi_0|_{J_2}=-\theta_{\rm per},\qquad
    \theta_{\rm per}>0.
    \]

    Write

    \[
    H(x)=
    \lambda_u k_u(x)+\lambda_c k_c(x)+\lambda_v k_v(x)
    +\lambda_-L_-(x)+\lambda_+L_+(x)
    +\lambda_{\log}\log\frac1{|c-x|}.
    \]

    The relation says

    \[
    H(x)+\lambda_0+\lambda_\Pi\pi_0(x)=0
    \]

    on \(J_1\cup J_2\).  Hence \(H\) is constant on each \(J_i\), so
    \(H'(x)=0\) on two open intervals.  But \(H'\) is a rational function with
    possible poles only at \(u,c,v\).  Therefore \(H'\equiv0\) on the connected
    real domain separated from those poles.  Comparing singular parts at
    \(u,c,v\) kills \(\lambda_-,\lambda_+,\lambda_{\log}\), then
    \(\lambda_u,\lambda_c,\lambda_v\), so \(H\equiv0\).  The original relation
    reduces to

    \[
    \lambda_0+\lambda_\Pi=0,\qquad
    \lambda_0-\theta_{\rm per}\lambda_\Pi=0,
    \]

    whence \(\lambda_\Pi=0\) and \(\lambda_0=0\).  Thus all coefficients
    vanish and \(\operatorname{Rel}=0\).

    Thus the determinant shortcut is not a single-interval theorem.  It is
    available only if the chosen realization support sees at least two
    different period values.  Otherwise the \(\pi_0\)-constant relation must
    remain in \(\operatorname{Rel}\).

    Direct singularity comparison does not prove the three annihilation
    conditions in a nontrivial \(\operatorname{Rel}\) case.  It either proves
    the stronger independence statement above, or leaves a relation in which
    the desired identities

    \[
    \lambda_u=X\lambda_-,\qquad
    \lambda_v=Y\lambda_+,\qquad
    F_c\lambda_c=\frac qa\,\lambda_-+\frac qb\,\lambda_+
    \]

    become extra branch-parameter constraints.  The constants
    \(X,Y,F_c,q/a,q/b\) are branch-state data, not singular coefficients of
    \(K_\lambda(x)\).  Therefore these identities should not be treated as
    automatic consequences of \(\lambda\in\operatorname{Rel}\).

    Stop/go for this subroute:

    - Do not make the eight-kernel determinant the primary route.  It is a
      useful shortcut only when the realization support crosses two period
      values.
    - Do one bounded \(P^0\) audit: either show \(\operatorname{Rel}=0\) in the
      chosen support, or verify the three annihilation identities directly.
    - If that audit fails, stop the finite-row \(P^{0T}Q_{\rm eff}P^0\) route
      and switch to the actual-density/cone formulation for the endpoint test
      combinations \(Be_u+Ae_\zeta\) and \(Be_\zeta+Ae_v\).

    2026-05-06 bounded-audit decision.

    The best available way to make \(P^0\) proof-grade is not to prove the
    three annihilation identities directly.  Those identities contain the
    branch-state constants \(X,Y,F_c,q/a,q/b\), and there is no current
    singularity argument forcing them from a relation among the kernels.  The
    direct row-identity route is therefore a low-probability fallback unless a
    new structural equation is found.

    The primary audit should instead try to choose the realization support
    \(J_{\rm reg}\) so that it sees two period values.  In that case the seven
    non-period kernels are independent on each separated regular piece, and
    the period row is not proportional to the constant row across the chosen
    support.  Hence

    \[
    \operatorname{Rel}=0,
    \]

    and the three formal columns

    \[
    p_u^0=(0,1,0,0,-X,0,0,0),
    \]

    \[
    p_v^0=(0,0,0,1,0,-Y,0,0),
    \]

    \[
    p_\zeta^0=\left(0,0,F_c,0,-\frac qa,-\frac qb,0,0\right)
    \]

    pass the row-level obstruction automatically.

    This still does not finish the compact \(g=2\) proof.  After
    \(\operatorname{Rel}=0\), one must still prove that the bump
    realizations are actual two-sided critical directions in the fixed-period,
    zero-mass chart.  If they are only one-sided cone directions, the ordinary
    PSD matrix argument for \(P^{0T}Q_{\rm eff}P^0\) is invalid and must be
    replaced by a cone KKT argument.

    Therefore the next mathematical task is now sharpened to:

    \[
    \boxed{
    \text{Choose a two-period realization support and prove }
    \operatorname{Rel}=0,\text{ then prove two-sided realization of }
    p_u^0,p_v^0,p_\zeta^0.
    }
    \]

    Stop condition: if no admissible two-period support can be used, and the
    three annihilation identities cannot be derived from the branch equations,
    retire the finite-row \(P^0\) clamp route and switch to the
    actual-density/cone endpoint formulation.

    Next lineality target after \(\operatorname{Rel}=0\).

    Row realization is not the same as two-sided feasibility.  The missing
    upgrade should be stated as a local implicit-function lemma.

    Work in a compact non-pinched regular chamber and choose
    \(J_{\rm reg}=J_1\cup J_2\) away from all endpoints, poles, and active
    zero-boundaries.  Assume:

    1. the background density on \(J_{\rm reg}\) is bounded below by a positive
       constant;
    2. all inactive inequalities have positive slack on the compact chart;
    3. the active equality map
       \[
       \mathcal F(\rho,y)=(\text{mass},\text{period},E_-,E_+,F(c),S,\ldots)
       \]
       has regular linearization in the chosen finite-gap chart;
    4. the signed bump \(\eta_j\) and local state displacement \(\delta y_j\)
       realize \(p_j^0\) and solve the linearized active equations:
       \[
       D\mathcal F(\eta_j,\delta y_j)=0.
       \]

    Then \((\eta_j,\delta y_j)\) lies in the lineality of the critical cone:
    both \(+t(\eta_j,\delta y_j)\) and \(-t(\eta_j,\delta y_j)\) can be
    corrected by \(O(t^2)\) terms to actual admissible nearby configurations.
    The proof is the standard finite-codimension implicit-function theorem:
    regularity solves the active equalities to second order, while the density
    lower bound and strict inactive slack keep all inequalities valid for
    sufficiently small \(|t|\).

    Therefore, under these regular-chamber assumptions, the three columns
    \(p_u^0,p_v^0,p_\zeta^0\) are legitimate directions for a PSD matrix test.
    If any of these assumptions fails, especially strict slack or regular
    equality rank, the lineality argument fails and the proof must switch to a
    one-sided cone KKT formulation.

    The next proof-grade task is to verify assumptions 1--4 for the compact
    \(g=2\) chamber, not to recompute the finite matrix yet.

    2026-05-06 lineality decision.

    Under the compact non-pinched hypotheses, this should close as ordinary
    lineality, not as a cone-only direction, provided the two-period support
    can be chosen inside positive-density regular interiors.  Signed compactly
    supported bumps are two-sided there: for sufficiently small \(|t|\),
    \[
    \rho_{\rm base}(x)+t\eta_j(x)\ge0
    \]
    for both signs of \(t\).  The strict chamber inequalities
    \[
    a>0,\qquad b>0,\qquad q>0,\qquad F_c<0,
    \]
    together with strict interlacing and positive inactive slack, are open
    conditions, so they survive small \(\pm t\) perturbations after the
    active equations are corrected by the implicit-function theorem.

    Thus the next lemma to write is:

    \[
    \boxed{
    \operatorname{Rel}=0
    +\text{ positive regular two-period support}
    \Longrightarrow
    p_u^0,p_v^0,p_\zeta^0
    \in \rho^\sharp(\operatorname{Lin} C_{\rm crit}).
    }
    \]

    Do not switch to cone KKT unless one of the following happens:

    1. the two-period support must touch a zero-density boundary or active
       residue constraint;
    2. the required row data can only be realized by one-sided nonnegative
       variations;
    3. the minimal-lift direction \(Sp_j^0\) cannot be approximated in the
       energy topology by such two-sided feasible bumps.

    If the lineality lemma is accepted, the next blocker becomes the effective
    endpoint Hessian identity for

    \[
    M=P^{0T}Q_{\rm eff}P^0,
    \]

    including the nonlocal \(K_{\log}\) contribution.

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

    2026-05-06 effective-entry audit.

    After the lineality lemma, PSD gives only the actual quadratic tests.  Set

    \[
    m_{ij}=Q_{\rm eff}(p_i^0,p_j^0),
    \qquad i,j\in\{u,v,\zeta\}.
    \]

    For \(x\in(u,c)\), with

    \[
    A=x-u,\qquad B=c-x,\qquad d_-=c-u,
    \]

    the test vector \(h_-=Be_u+Ae_\zeta\) gives

    \[
    \boxed{
    m_{uu}B^2+2m_{u\zeta}AB+m_{\zeta\zeta}A^2\ge0.
    }
    \]

    For \(x\in(c,v)\), with

    \[
    A=x-c,\qquad B=v-x,\qquad d_+=v-c,
    \]

    the test vector \(h_+=Be_\zeta+Ae_v\) gives

    \[
    \boxed{
    m_{\zeta\zeta}B^2+2m_{v\zeta}AB+m_{vv}A^2\ge0.
    }
    \]

    These two inequalities are automatic consequences of \(M\succeq0\).  They
    are not yet the old curvature clamp.  To recover the old clamp, one needs
    a stronger effective-entry theorem:

    \[
    m_{uu}=\lambda a,\qquad
    m_{vv}=\lambda b,\qquad
    m_{\zeta\zeta}=\lambda Q_c,
    \]

    and, crucially, a common off-diagonal coefficient

    \[
    -\frac{2m_{u\zeta}}{d_-}
    =
    \frac{2m_{v\zeta}}{d_+}
    =
    \lambda\Gamma.
    \]

    Without this common-coefficient identity, the Hessian cross terms do not
    necessarily couple to the same \(\Gamma\) that appears in the Wronskian
    reduction.  Then the old Wronskian contradiction cannot be invoked.

    Therefore the next theorem is not merely positivity of the actual entries.
    It is the common-coefficient effective Hessian theorem:

    \[
    \boxed{
    P^{0T}Q_{\rm eff}P^0
    \text{ has the old five entries, or else its actual entries still imply
    the same Wronskian sign obstruction.}
    }
    \]

    Stop condition: if \(K_{\log}\) changes the two off-diagonal entries so
    that

    \[
    -2m_{u\zeta}/d_-\ne 2m_{v\zeta}/d_+
    \]

    and no replacement Wronskian argument uses the two unequal coefficients,
    then the compact \(g=2\) Hessian-clamp route must stop.

    The old five entries should not be assumed to survive by default.  The
    nonlocal Gram term

    \[
    K_{\log}(p_i^0,p_j^0)=\mathcal E_{\log}(Sp_i^0,Sp_j^0)
    \]

    is a real contribution from the energy-minimal row lifts.  A new
    orthogonality or renormalization identity would be needed to show that it
    vanishes on the five relevant entries, or that it is absorbed into one
    common scale \(\lambda\).  Without such an identity, the old finite Schur
    entries are only a model, not a proof.

    The next derivation is therefore:

    \[
    \boxed{
    m_{ij}
    =
    b(p_i^0,p_j^0)
    +\mathcal E_{\log}(Sp_i^0,Sp_j^0),
    \qquad i,j\in\{u,v,\zeta\},
    }
    \]

    where \(S\) is the Riesz/minimal-lift operator on the zero-mass,
    fixed-period Hilbert space.  One must compute or characterize the induced
    Schur/Feshbach Gram matrix of the row representers.  This is now the
    controlling calculation for compact \(g=2\).

    The Feshbach Gram has a concrete finite-dimensional form once the
    two-period support gives \(\operatorname{Rel}=0\).  Let

    \[
    \ell_i(\xi)=R_i(\xi)
    \]

    denote the chosen row functionals on the zero-mass, fixed-period Hilbert
    space \(H_{0,\Pi}\).  Let \(g_i\in H_{0,\Pi}\) be their Riesz
    representers:

    \[
    \mathcal E_{\log}(g_i,h)=\ell_i(h)
    \qquad(h\in H_{0,\Pi}).
    \]

    Define the row Gram matrix

    \[
    C_{ij}=\ell_i(g_j)=\mathcal E_{\log}(g_i,g_j).
    \]

    When the rows are independent on the feasible row image, \(C\) is positive
    definite on that image.  For a row vector \(r\), the minimal lift has the
    form

    \[
    Sr=\sum_i\alpha_i g_i,\qquad C\alpha=r.
    \]

    Hence

    \[
    \boxed{
    K_{\log}(r,s)=\mathcal E_{\log}(Sr,Ss)=r^T C^{-1}s.
    }
    \]

    Therefore, for the three endpoint columns,

    \[
    \boxed{
    M=P^{0T}\left(B+C^{-1}\right)P^0,
    }
    \]

    where \(B\) is the finite non-log Schur/Hessian matrix \(b\) in the same
    row coordinates.  This is the actual matrix whose five entries must be
    analyzed.  The old local matrix \(P^{0T}BP^0\) is insufficient unless
    \(P^{0T}C^{-1}P^0\) has the same five-entry pattern or can be absorbed
    into the same common scale.

    Algebraic reduction of this test.  Suppose the finite non-log block already
    has the old five-entry structure:

    \[
    P^{0T}BP^0
    =
    \lambda_B
    \begin{pmatrix}
    a&*&-\Gamma d_-/2\\
    *&b&\Gamma d_+/2\\
    -\Gamma d_-/2&\Gamma d_+/2&Q_c
    \end{pmatrix},
    \]

    where the row/column order is \(u,v,\zeta\), \(d_-=c-u\), and
    \(d_+=v-c\).  The entry \((u,v)\) is irrelevant for the elementary
    two-side curvature clamp because the test vectors use only
    \((u,\zeta)\) and \((v,\zeta)\).

    Put

    \[
    N=P^{0T}C^{-1}P^0.
    \]

    The old five-entry clamp survives with a new scale
    \(\lambda=\lambda_B+\delta\) only if the five relevant entries of \(N\)
    lie in the same one-dimensional template:

    \[
    \boxed{
    N_{uu}=\delta a,\qquad
    N_{vv}=\delta b,\qquad
    N_{\zeta\zeta}=\delta Q_c,
    }
    \]

    and

    \[
    \boxed{
    -\frac{2N_{u\zeta}}{d_-}
    =
    \frac{2N_{v\zeta}}{d_+}
    =
    \delta\Gamma.
    }
    \]

    In the degenerate subcase \(\Gamma=0\), this condition should be read as

    \[
    N_{u\zeta}=N_{v\zeta}=0
    \]

    rather than by dividing by \(\Gamma\).  The resulting scale

    \[
    \lambda=\lambda_B+\delta
    \]

    must also remain positive for the old clamp interpretation.

    Equivalently, the five ratios

    \[
    \frac{N_{uu}}a,\quad
    \frac{N_{vv}}b,\quad
    \frac{N_{\zeta\zeta}}{Q_c},\quad
    -\frac{2N_{u\zeta}}{\Gamma d_-},\quad
    \frac{2N_{v\zeta}}{\Gamma d_+}
    \]

    must all agree, ignoring terms whose denominators vanish in a degenerate
    chamber.  This is a strong codimension-four condition on the five relevant
    entries of the Gram correction;
    a generic positive definite \(N\) will not satisfy it.  Therefore the old
    five-entry pattern can only be expected if the Riesz Gram has an additional
    symmetry, orthogonality, or variational identity tied to the finite-gap
    Euler equations.

    If this one-dimensional template test fails, the proof must immediately
    switch from the old clamp to the actual-entry clamp and then prove a new
    Wronskian obstruction using the two possibly different cross coefficients.

    2026-05-06 review update: local neck sign and common-template obstruction.

    The local algebra gives a useful sign lemma, but it must not be confused
    with the effective Hessian diagonal until the identity
    \(m_{\zeta\zeta}=\lambda Q_c\) or a direct negativity statement for
    \(m_{\zeta\zeta}\) has been proved.

    In the compact neck, write

    \[
    A=W'(u),\qquad B=W'(v),\qquad
    A_2=W''(u),\qquad B_2=W''(v),
    \]

    and

    \[
    X=U'(u)=\frac qa+A,\qquad Y=U'(v)=B-\frac qb.
    \]

    From the branch Euler equation

    \[
    S=aA+bB=0
    \]

    and strict convexity of \(W\) on \((u,v)\), one has

    \[
    A<0<B,\qquad B=-\frac ab A,
    \]

    and therefore

    \[
    Y=-\frac ab X.
    \]

    The local cokernel algebra then gives

    \[
    P_c=-\frac{AY-BX}{F_cX}=0.
    \]

    It also gives

    \[
    \Gamma=\frac{-A+aA_2+B+bB_2}{X}>0,
    \]

    using \(X>0\), \(A<0<B\), and \(A_2,B_2>0\).  For the local quantity

    \[
    Q_c=
    \frac{
    A^2-AaA_2-AB-AbB_2+aA_2X+bB_2X
    }{F_cX},
    \]

    the numerator becomes

    \[
    A^2+\frac abA^2+aA_2(X-A)+bB_2(X-A),
    \]

    where \(X-A=q/a>0\).  Hence the numerator is positive, while
    \(F_c<0\) and \(X>0\), so

    \[
    \boxed{Q_c<0.}
    \]

    This is only a local sign lemma until the effective Hessian identification
    is proved.  It does, however, strongly constrict the old common-template
    route.  Since \(C^{-1}\) is positive definite on the feasible row image,
    the Gram correction

    \[
    N=P^{0T}C^{-1}P^0
    \]

    is positive semidefinite, and \(N_{\zeta\zeta}>0\) if \(p_\zeta^0\) is a
    nonzero feasible row vector.  If \(N\) were to preserve the old
    one-dimensional template, then

    \[
    N_{uu}=\delta a,\qquad
    N_{vv}=\delta b,\qquad
    N_{\zeta\zeta}=\delta Q_c.
    \]

    Because \(a,b>0\) and \(N\succeq0\), the first two diagonal equations force
    \(\delta\ge0\).  But \(Q_c<0\), so the third equation gives
    \(N_{\zeta\zeta}\le0\), contradicting positive definiteness on the
    nonzero \(p_\zeta^0\) direction.  The only formal escape is the trivial
    \(\delta=0\) case, which would force the relevant Gram rows to vanish and
    is incompatible with nonzero endpoint-transfer rows in a positive Gram
    space.

    Therefore the old five-entry common-template route is not just unproved;
    it is structurally incompatible with a nontrivial positive Feshbach Gram
    correction, assuming the local \(Q_c\) above is the same coefficient that
    appears in the old template.  The proof should no longer try to preserve
    the old template as the main route.

    The sharpened compact \(g=2\) target is now:

    \[
    \boxed{\textbf{EffectiveNeckNegativity:}\quad
    Q_{\rm eff}(p_\zeta^0,p_\zeta^0)<0.}
    \]

    In finite terms this is

    \[
    b(p_\zeta^0,p_\zeta^0)
    +(p_\zeta^0)^TC^{-1}p_\zeta^0<0.
    \]

    If the non-log term has the local form

    \[
    b(p_\zeta^0,p_\zeta^0)=\lambda_B Q_c,\qquad \lambda_B>0,
    \]

    then the required estimate is the capacity-type bound

    \[
    (p_\zeta^0)^TC^{-1}p_\zeta^0<-\lambda_BQ_c.
    \]

    If this effective-neck negativity holds, compact non-pinched \(g=2\) is
    excluded directly by second-variation negativity in the \(e_\zeta\)
    direction.  If it fails, the diagonal shortcut is dead and the proof must
    use the actual-entry Wronskian route or switch to direct density/cone KKT.

    2026-05-06 capacity-reduction record.

    The proof-grade compact \(g=2\) reduction is now:

    \[
    \boxed{
    \text{BranchEulerStateLift}
    +\text{FeshbachMinimalLift}
    +\text{RowRealization3/lineality}
    +\text{EffectiveNeckNegativity}
    \Longrightarrow
    \text{no compact non-pinched }g=2.
    }
    \]

    More explicitly, assume a separated regular compact \(g=2\) chamber, the
    corrected branch functional \(\Phi_{\rm br}\), the fixed-period zero-mass
    Hilbert space, and actual two-sided realization of \(p_\zeta^0\).  If

    \[
    Q_{\rm eff}(p_\zeta^0,p_\zeta^0)<0,
    \]

    then taking the minimal lift \(\xi_\zeta=Sp_\zeta^0\), or smooth feasible
    approximants to it, gives

    \[
    G_{\rm br}(\xi_\zeta,\xi_\zeta)
    =
    Q_{\rm eff}(p_\zeta^0,p_\zeta^0)<0,
    \]

    contradicting the second-order necessary condition for an interior compact
    minimizer.  Thus compact non-pinched \(g=2\) is reduced to one scalar
    inequality.

    In row coordinates,

    \[
    p_\zeta^0=\left(0,0,F_c,0,-\frac qa,-\frac qb,0,0\right),
    \]

    so the corresponding row functional is

    \[
    \ell_\zeta(\eta)
    =
    F_cR_c(\eta)-\frac qa R_-(\eta)-\frac qb R_+(\eta),
    \]

    equivalently, at the kernel level,

    \[
    \phi_\zeta(x)
    =
    \frac{F_c}{x-c}
    -\frac qa L_-(x)-\frac qb L_+(x).
    \]

    Define the nonlocal capacity term

    \[
    K_\zeta=(p_\zeta^0)^TC^{-1}p_\zeta^0
    =
    \inf\left\{
    \mathcal E_{\log}(\eta,\eta):
    \eta\in H_{0,\Pi},\ \rho^\sharp(\eta)=p_\zeta^0
    \right\}.
    \]

    The effective-neck inequality is therefore the explicit capacity estimate

    \[
    \boxed{
    K_\zeta<-b(p_\zeta^0,p_\zeta^0).
    }
    \]

    If the finite non-log part is identified as

    \[
    b(p_\zeta^0,p_\zeta^0)=\lambda_BQ_c,\qquad \lambda_B>0,
    \]

    this becomes

    \[
    \boxed{
    K_\zeta<-\lambda_BQ_c.
    }
    \]

    This is the exact route's current hard mouth.  It is a logarithmic
    capacity/Riesz-minimal-lift estimate, not a local algebra identity.

    The Euler-Lagrange equation for the minimizer \(\eta_\zeta\) of
    \(K_\zeta\), modulo harmless sign and factor normalizations in the
    Lagrange multipliers, has the form

    \[
    U_{\eta_\zeta}(x)=
    \sum_i\alpha_i\phi_i(x)+\alpha_0+\alpha_\Pi\pi_0(x)
    \qquad (x\in J_1\cup J_2),
    \]

    and after differentiating,

    \[
    \operatorname{p.v.}\int_{J_1\cup J_2}
    \frac{d\eta_\zeta(t)}{x-t}
    =
    -\sum_i\alpha_i\phi_i'(x).
    \]

    This is a two-cut finite Hilbert-transform / Cauchy-transform problem.
    Solving or estimating it is the next genuine calculation.  Abstract signs
    alone do not imply the needed negativity: a one-dimensional model with
    \(b(p,p)=-1\) and \(p^TC^{-1}p=2\) already gives
    \(Q_{\rm eff}(p,p)=1>0\).  Therefore the proof must use the specific
    finite-gap geometry of this \(p_\zeta^0\), not only \(Q_c<0\) and
    \(C^{-1}\succeq0\).

    2026-05-06 Schur-positive reformulation.

    Let

    \[
    r=p_\zeta^0,\qquad T=-b(r,r).
    \]

    In the expected local identification

    \[
    b(r,r)=\lambda_BQ_c,\qquad \lambda_B>0,
    \]

    this is

    \[
    T=-\lambda_BQ_c>0.
    \]

    Since \(C\succ0\) on the feasible row image, the capacity inequality

    \[
    r^TC^{-1}r<T
    \]

    is equivalent by Schur complement to the augmented Gram positivity

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

    Equivalently, in Rayleigh quotient form,

    \[
    \boxed{
    (\alpha^Tr)^2
    <
    T\,\alpha^TC\alpha
    \qquad(\alpha\ne0).
    }
    \]

    Thus the sharp compact \(g=2\) diagonal shortcut should now be stated as

    \[
    \boxed{\textbf{EffectiveNeckSchurPositive:}\quad
    \mathcal S_\zeta\succ0.}
    \]

    This is exactly equivalent to EffectiveNeckNegativity once \(T=-b(r,r)\)
    has been identified.  It is often a cleaner proof target because it avoids
    writing \(C^{-1}\) explicitly.

    The next calculation is to build \(C\) from the two-cut Riesz
    representers.  For a row kernel \(k_i\), the representer \(g_i\) satisfies

    \[
    \mathcal E_{\log}(g_i,h)=\ell_i(h)
    \]

    and, on \(J=J_1\cup J_2\), its potential has the form

    \[
    U_{g_i}(x)=k_i(x)+\text{constant}+\text{period multiplier}
    \]

    up to the chosen sign convention for rows and potentials.  Differentiating
    gives a finite Hilbert-transform equation

    \[
    \operatorname{p.v.}\int_J\frac{dg_i(t)}{x-t}
    =
    -k_i'(x)
    \]

    with the zero-mass and fixed-period normalizations determining the
    nullspace terms.  In two-cut notation, with

    \[
    R(z)=
    \sqrt{(z-\alpha_1)(z-\beta_1)(z-\alpha_2)(z-\beta_2)},
    \]

    the density of \(g_i\) should be obtained by the standard finite Hilbert
    transform inversion, with an added degree-one numerator divided by
    \(R_+\) to enforce the mass and period constraints.  The branch, sign, and
    \(\pi\)-normalizations must be fixed before this formula is used as a
    proof.  After that,

    \[
    C_{ij}=\ell_i(g_j)
    \]

    and the remaining hard theorem is the positive definiteness of
    \(\mathcal S_\zeta\).

    2026-05-06 Green/Gram-extension audit and downgrade.

    There is a tempting way to view \(\mathcal S_\zeta\) as an augmented Gram
    matrix.  The neck row

    \[
    r=p_\zeta^0
    =
    \left(0,0,F_c,0,-\frac qa,-\frac qb,0,0\right)
    \]

    has row kernel

    \[
    \phi_\zeta(x)=
    \frac{F_c}{x-c}
    -\frac qaL_-(x)-\frac qbL_+(x).
    \]

    Formally,

    \[
    \frac1{x-c}
    =
    \mathcal E_{\log}(\partial_c\delta_c,\delta_x),
    \]

    while

    \[
    L_-(x)=\mathcal E_{\log}(\delta_c-\delta_u,\delta_x),
    \qquad
    L_+(x)=\mathcal E_{\log}(\delta_v-\delta_c,\delta_x).
    \]

    Hence the distribution

    \[
    \boxed{
    D_\zeta=
    F_c\partial_c\delta_c
    -\frac qa(\delta_c-\delta_u)
    -\frac qb(\delta_v-\delta_c)
    }
    \]

    reproduces the neck row on smooth external perturbations:

    \[
    \mathcal E_{\log}(D_\zeta,\eta)=p_\zeta^0(\eta).
    \]

    If \(D_\zeta\) were a vector in a larger positive Hilbert energy space with
    self-energy

    \[
    \langle D_\zeta,D_\zeta\rangle=-b(p_\zeta^0,p_\zeta^0)=T
    \]

    and \(D_\zeta\) were not in the closed span of the external row
    representers \(g_i\), then

    \[
    \begin{pmatrix}
    C&r\\
    r^T&T
    \end{pmatrix}
    \]

    would be the Gram matrix of \(\{g_i,D_\zeta\}\) and
    EffectiveNeckSchurPositive would follow immediately.

    This is not a proof.  The distribution \(D_\zeta\) contains point masses
    and a dipole:

    \[
    D_\zeta=
    F_c\partial_c\delta_c
    +\frac qa\delta_u
    +\left(\frac qb-\frac qa\right)\delta_c
    -\frac qb\delta_v.
    \]

    These objects do not lie in the zero-mass, fixed-period logarithmic energy
    Hilbert space.  In particular,

    \[
    \mathcal E_{\log}(\delta_c,\delta_c)=+\infty
    \]

    and

    \[
    \mathcal E_{\log}(\partial_c\delta_c,\partial_c\delta_c)
    \]

    is more singular.  A Hadamard finite part or renormalized self-energy is
    scheme-dependent unless it is tied to exactly the same local
    Schur/Hessian subtraction convention used to define \(b\).  Moreover,
    finite-part pairings are not automatically positive definite.  Therefore
    the proposed identity

    \[
    \mathcal E_{\rm ren}(D_\zeta,D_\zeta)
    =
    -b(p_\zeta^0,p_\zeta^0)
    \]

    may be useful bookkeeping, but it cannot replace
    EffectiveNeckSchurPositive unless one first constructs a genuine positive
    extension Hilbert space and proves the identity in that space.  This
    extension is currently not available.  Do not use
    RenormalizedNeckEnergyIdentity as the main compact \(g=2\) proof route.

    The reliable formulation is still the Schur-positive / capacity
    inequality:

    \[
    \boxed{
    r^TC^{-1}r<T.
    }
    \]

    Equivalently, it is the single-RHS constrained minimization

    \[
    \boxed{
    K_\zeta=
    \inf\left\{
    \mathcal E_{\log}(\eta,\eta):
    \eta\in H_{0,\Pi},\quad
    \rho^\sharp(\eta)=p_\zeta^0
    \right\}<T.
    }
    \]

    This is often sharper than computing the entire matrix \(C^{-1}\).  The
    Euler equation is: find multipliers \(\alpha_i\) and a density
    \(\eta\in H_{0,\Pi}\) such that

    \[
    U_\eta(x)=\sum_i\alpha_i k_i(x)+\alpha_0+\alpha_\Pi\pi_0(x),
    \qquad x\in J_1\cup J_2,
    \]

    with row constraints

    \[
    \int_J k_i\,d\eta=r_i.
    \]

    After differentiating,

    \[
    \operatorname{p.v.}\int_J\frac{d\eta(t)}{x-t}
    =
    -\sum_i\alpha_i k_i'(x).
    \]

    Solving this single RHS problem gives \(C\alpha=r\), and the minimum
    energy is

    \[
    \boxed{
    K_\zeta=\alpha^Tr.
    }
    \]

    Thus the exact compact \(g=2\) hard mouth can be stated as

    \[
    \boxed{
    \alpha^Tr<T,\qquad C\alpha=p_\zeta^0.
    }
    \]

    In Rayleigh form this is the sharp trace inequality

    \[
    \boxed{
    \left(
    F_c\alpha_c-\frac qa\alpha_- -\frac qb\alpha_+
    \right)^2
    <
    T\,\alpha^TC\alpha
    \qquad(\alpha\ne0).
    }
    \]

    For reference,

    \[
    \phi_\zeta'(x)=
    -\frac{F_c}{(x-c)^2}
    -\frac qa\left(\frac1{x-u}-\frac1{x-c}\right)
    -\frac qb\left(\frac1{x-c}-\frac1{x-v}\right).
    \]

    The finite-Hilbert inversion with

    \[
    f_\alpha(x)=-\sum_i\alpha_i k_i'(x)
    \]

    should produce

    \[
    d\eta(x)=
    \left[
    \frac{1}{\pi^2|R(x)|}
    \operatorname{p.v.}\int_J
    \frac{|R(t)|f_\alpha(t)}{t-x}\,dt
    +\frac{A_\alpha+B_\alpha x}{|R(x)|}
    \right]dx,
    \]

    where \(A_\alpha,B_\alpha\) enforce zero mass and fixed period.  The next
    real calculation is to turn the constraints into the single linear system
    for \(\alpha\) and prove \(\alpha^Tr<T\), ideally by converting
    \(T-\alpha^Tr\) into a manifestly positive period or square integral.

    2026-05-06 constrained balayage / residue-form queue.

    The safe way to use the formal distribution \(D_\zeta\) is not to give it
    a self-energy.  Since \(u,c,v\) lie off the two-cut support \(J\), the
    kernel \(\phi_\zeta\) defines a continuous row functional on the separated
    zero-mass, fixed-period energy space:

    \[
    \ell_{D_\zeta}(\eta)=p_\zeta^0(\eta).
    \]

    By Riesz representation there is a unique constrained balayage

    \[
    \mathsf B_\Pi D_\zeta\in H_{0,\Pi}
    \]

    such that

    \[
    \mathcal E_{\log}(\mathsf B_\Pi D_\zeta,\eta)
    =
    p_\zeta^0(\eta)
    \qquad(\eta\in H_{0,\Pi}).
    \]

    Its squared norm is exactly the capacity term

    \[
    \boxed{
    \|\mathsf B_\Pi D_\zeta\|_{\mathcal E}^2
    =
    K_\zeta
    =
    (p_\zeta^0)^TC^{-1}p_\zeta^0.
    }
    \]

    Thus the compact \(g=2\) diagonal shortcut is equivalently

    \[
    \boxed{\textbf{BalayageGapPositive:}\quad T-K_\zeta>0.}
    \]

    This formulation is proof-grade as a reduction.  It still does not prove
    positivity; it only states the exact gap-energy estimate that must be
    shown.

    The single-RHS problem can be written more explicitly as a Cauchy-transform
    ansatz.  Let

    \[
    J=[\alpha_1,\beta_1]\cup[\alpha_2,\beta_2],
    \qquad
    R(z)=
    \sqrt{(z-\alpha_1)(z-\beta_1)(z-\alpha_2)(z-\beta_2)},
    \]

    with \(R(z)\sim z^2\) at infinity.  For multipliers \(\alpha_i\), put

    \[
    f_\alpha(z)=-\sum_i\alpha_i k_i'(z).
    \]

    If

    \[
    G_\alpha(z)=\int_J\frac{d\eta_\alpha(t)}{z-t},
    \]

    then the Euler equation gives

    \[
    \frac{G_{\alpha,+}(x)+G_{\alpha,-}(x)}2=f_\alpha(x),
    \qquad x\in J.
    \]

    Hence

    \[
    \boxed{
    G_\alpha(z)=f_\alpha(z)+\frac{A_\alpha(z)}{R(z)}.
    }
    \]

    The rational numerator \(A_\alpha\) is determined by cancelling the polar
    parts of \(R f_\alpha\) at \(u,c,v\), plus an affine freedom
    \(\lambda_0+\lambda_1z\) fixed by the zero-mass and fixed-period
    normalizations.

    The row constraints can be written directly in terms of \(G_\alpha\).  With
    \(r=p_\zeta^0\),

    \[
    \int_J\frac{d\eta(x)}{x-s}=-G_\alpha(s)
    \qquad(s\in\{u,c,v\}),
    \]

    and

    \[
    \int_JL_-(x)\,d\eta(x)=-\int_u^cG_\alpha(s)\,ds,\qquad
    \int_JL_+(x)\,d\eta(x)=-\int_c^vG_\alpha(s)\,ds.
    \]

    Therefore, for

    \[
    p_\zeta^0=\left(0,0,F_c,0,-\frac qa,-\frac qb,0,0\right),
    \]

    the sign convention gives

    \[
    G_\alpha(u)=0,\qquad
    G_\alpha(c)=-F_c,\qquad
    G_\alpha(v)=0,
    \]

    and

    \[
    \int_u^cG_\alpha(s)\,ds=\frac qa,\qquad
    \int_c^vG_\alpha(s)\,ds=\frac qb,
    \]

    together with the zero-mass / fixed-period conditions.  These equations
    are the concrete single-RHS linear system for \(\alpha\) and the two
    normalization constants.  Once \(C\alpha=r\) is solved,

    \[
    \boxed{
    K_\zeta=\alpha^Tr
    =
    F_c\alpha_c-\frac qa\alpha_- -\frac qb\alpha_+.
    }
    \]

    The next possible positivity mechanism is a square-residue identity.  A
    conditional target is

    \[
    \boxed{\textbf{SquareResidueIdentity}_\zeta}
    \]

    asserting that

    \[
    T-\alpha^Tr
    =
    \frac{1}{2\pi i}
    \int_{\partial J}\frac{A_\alpha(z)^2}{R(z)}\,dz
    +
    \mathcal P_{\rm per}(A_\alpha),
    \]

    where \(\mathcal P_{\rm per}\ge0\) is the positive period correction
    forced by the fixed-period normalization.  Equivalently, with the correct
    branch conventions this should become a positive expression of the form

    \[
    \int_J\frac{|A_{\alpha,+}(x)|^2}{|R_+(x)|}\,dx
    +
    \mathcal P_{\rm per}(A_\alpha).
    \]

    If such an identity is proved, the right side is strictly positive unless
    \(A_\alpha\equiv0\) and the period term vanishes.  That would make
    \(G_\alpha=f_\alpha\) have no cut jump, hence \(\eta_\alpha=0\), contrary
    to \(p_\zeta^0\ne0\).  Therefore SquareResidueIdentity would imply
    \(K_\zeta<T\) and kill compact non-pinched \(g=2\).

    The remaining unproved alignment is more specific:

    \[
    \boxed{\textbf{LocalSchurTraceIdentity}_\zeta.}
    \]

    It must identify the finite local branch-Hessian trace

    \[
    T=-b(p_\zeta^0,p_\zeta^0)
    \]

    with the polar residue trace of the quadratic differential

    \[
    \Omega_\alpha(z)=\frac{A_\alpha(z)^2}{R(z)}\,dz
    \]

    at \(u,c,v,\infty\), using exactly the same endpoint anchors, branch
    state-lift, and period normalization as the corrected Hessian.  Without
    this identity, the square-residue expression is not tied to the actual
    finite block \(b\).  The current proof queue is therefore:

    \[
    \boxed{
    \text{LocalSchurTraceIdentity}
    \Rightarrow
    \text{SquareResidueIdentity}
    \Rightarrow
    K_\zeta<T
    \Rightarrow
    \text{no compact non-pinched }g=2.
    }
    \]

    This is a sharper version of EffectiveNeckSchurPositive, not a proof of it
    yet.  The next calculation is to compute
    \(b(p_\zeta^0,p_\zeta^0)\) from the corrected branch state response and
    compare it term-by-term with the polar residue trace of \(A_\alpha^2/R\).

    2026-05-06 diagonal shortcut audit.

    The first literal computation of the corrected branch Hessian in the
    \(p_\zeta^0\) direction does not support the desired diagonal negativity.
    This is a stop signal for the diagonal shortcut unless an additional
    explicitly defined finite non-log edge/mixed term is added and proved.

    Recall the branch-compatible row

    \[
    p_\zeta^0=
    \left(0,0,F_c,0,-\frac qa,-\frac qb,0,0\right).
    \]

    With the sign convention

    \[
    F_c\,\delta c+\delta_\xi F(c)=0,
    \]

    this row corresponds to \(\delta_\xi F(c)=-F_c\), hence
    \(\delta c=1\).  The endpoint rows give, with the log-at-\(c\) anchor
    fixed,

    \[
    \delta E_-=\frac qa,\qquad
    \delta E_+=-\frac qb.
    \]

    Substituting in the corrected branch state response gives

    \[
    \boxed{
    \delta y_\zeta
    =
    (\delta q,\delta a,\delta b,\delta c)
    =
    (0,1,-1,1).
    }
    \]

    Equivalently,

    \[
    \delta u=\delta c-\delta a=0,\qquad
    \delta v=\delta c+\delta b=0,
    \]

    so this is the formal direction that moves the center \(c\) while keeping
    \(u,v,q\) fixed.

    For the proof-grade branch functional currently recorded in the ledger,
    there is no independent \(\lambda_SS\) Hessian term and no free
    \(\lambda_FF(c)\) Hessian term.  Thus the endpoint contribution uses only

    \[
    \lambda_-\nabla_y^2E_-+\lambda_+\nabla_y^2E_+,
    \qquad
    \lambda_-=\frac1X,\quad \lambda_+=-\frac1Y.
    \]

    With \(v_\zeta=(0,1,-1,1)\),

    \[
    v_\zeta^T\nabla_y^2E_-v_\zeta=\frac q{a^2},
    \qquad
    v_\zeta^T\nabla_y^2E_+v_\zeta=\frac q{b^2}.
    \]

    Therefore the endpoint finite Hessian contribution is

    \[
    H_{\rm ep}(p_\zeta^0,p_\zeta^0)
    =
    \frac{q}{a^2X}-\frac{q}{b^2Y}.
    \]

    Using stationarity \(aA+bB=0\), equivalently

    \[
    Y=-\frac abX,
    \]

    this becomes

    \[
    \boxed{
    H_{\rm ep}(p_\zeta^0,p_\zeta^0)
    =
    \frac{q(a+b)}{a^2bX}>0.
    }
    \]

    The endpoint mixed \(y\)-density terms also vanish for this state lift:

    \[
    D^2_{y\xi}E_-[(\delta y_\zeta),\eta]
    =
    (\delta c-\delta a)\,\delta W_\eta'(u)=0,
    \]

    and

    \[
    D^2_{y\xi}E_+[(\delta y_\zeta),\eta]
    =
    (\delta c+\delta b)\,\delta W_\eta'(v)=0.
    \]

    Consequently, under the current corrected fixed-chart branch functional and
    with no additional finite non-log term, the branch finite contribution in
    the \(p_\zeta^0\) diagonal is positive:

    \[
    \boxed{
    b_{\rm br}(p_\zeta^0,p_\zeta^0)
    =
    \frac{q(a+b)}{a^2bX}>0.
    }
    \]

    This is incompatible with the earlier hoped-for identification

    \[
    b(p_\zeta^0,p_\zeta^0)=\lambda_BQ_c,\qquad
    \lambda_B>0,\quad Q_c<0.
    \]

    Therefore, in the current convention,

    \[
    Q_{\rm eff}(p_\zeta^0,p_\zeta^0)
    =
    b_{\rm br}(p_\zeta^0,p_\zeta^0)+K_\zeta>0
    \]

    because \(K_\zeta\ge0\).  The \(p_\zeta^0\) diagonal direction does not
    give the desired negative second variation.  EffectiveNeckSchurPositive is
    no longer the main route unless a new, explicit, non-endpoint/non-branch
    finite term is defined and shown to replace the positive endpoint trace by
    the required polar trace.

    The working stop theorem is:

    \[
    \boxed{\textbf{DiagonalShortcutFails}_\zeta.}
    \]

    Under the corrected branch-parametrized functional currently recorded,
    the \(p_\zeta^0\) diagonal Hessian shortcut does not exclude compact
    non-pinched \(g=2\).  The route should switch to a first-order KKT
    separation / cone formulation, unless a fully specified mixed Schur trace
    is introduced and proved.

    A possible replacement target is:

    \[
    \boxed{\textbf{MixedSchurTraceIdentity}_\zeta.}
    \]

    It would need to prove that some explicitly defined full finite Schur
    trace, including density-state and finite-density terms not present in the
    endpoint-only branch calculation above, converts
    \(H_{\rm ep}=q(a+b)/(a^2bX)\) into the polar residue trace of
    \(A_\alpha^2/R\).  This is currently not proved and not defined in the
    ledger.

    The active non-diagonal alternative is the first-order cone target:

    \[
    \boxed{
    \text{no nonzero }\theta_1K_1+\theta_2K_2
    \text{ has the admissible oriented compact sign pattern.}
    }
    \]

    With

    \[
    \widetilde K_i(x)=\sigma(x)K_i(x),
    \qquad \sigma(x)=\operatorname{sgn}(x-c),
    \]

    this can be stated as the convex-hull condition

    \[
    \boxed{
    0\in\operatorname{int}\operatorname{conv}
    \{(\widetilde K_1(x),\widetilde K_2(x)):
    x\in J_1\cup J_2\}.
    }
    \]

    If this OvalConvexityLemma is proved, no separating \(\theta\ne0\) can
    make \(\theta_1K_1+\theta_2K_2\) have the admissible oriented sign pattern,
    and compact non-pinched \(g=2\) is excluded by first-order KKT separation.

    2026-05-06 period quotient / free-period audit.

    The convex-hull route needs a period-space audit before it can be used as a
    proof.  In the fixed-period chart the admissible density directions satisfy

    \[
    \Pi(G)=\int_J\pi_0(x)G(x)\omega(x)\,dx=0,
    \qquad
    \pi_0|_{J_1}=1,\quad
    \pi_0|_{J_2}=-\theta_{\rm per}.
    \]

    A positive oriented period-transfer density of the form

    \[
    G_\Pi(x)=\sigma(x)h_\Pi(x),\qquad h_\Pi(x)>0,
    \]

    is not fixed-period.  Indeed,

    \[
    \pi_0\sigma=-1\quad\text{on }J_1,
    \qquad
    \pi_0\sigma=-\theta_{\rm per}<0\quad\text{on }J_2,
    \]

    hence

    \[
    \Pi(G_\Pi)<0.
    \]

    Therefore the earlier positive-quadrature argument cannot be interpreted as
    a fixed-period tangent argument.  If the first-order KKT normal cone is
    formed after imposing \(\Pi(G)=0\), the separating kernel may include a
    period multiplier:

    \[
    \theta_1K_1+\theta_2K_2+\lambda\pi_0.
    \]

    Thus proving only that \(\operatorname{span}\{K_1,K_2\}\) has no oriented
    sign pattern is not enough unless the period row has already been
    correctly quotiented out.

    The next required lemma is:

    \[
    \boxed{\textbf{PeriodQuotientLemma}.}
    \]

    It must prove one of the following precise statements.

    Version A: \(K_1,K_2\) are already the full fixed-period quotient cokernel,
    so the admissible sign-pattern obstruction is represented by
    \(\theta_1K_1+\theta_2K_2\) with no additional \(\lambda\pi_0\).

    Version B: if the period multiplier remains present, prove the stronger
    sign-pattern exclusion

    \[
    \boxed{
    \text{no nonzero }
    \theta_1K_1+\theta_2K_2+\lambda\pi_0
    \text{ has the admissible oriented compact sign pattern.}
    }
    \]

    Without this period quotient step, OvalConvexityLemma is only a six-row
    local-cokernel statement, not yet a fixed-period cone theorem.

    The positive period-transfer density can still be useful after moving to a
    free-period lift.  Introduce a period/filling variable \(\tau\) with

    \[
    \dot\tau+\Pi(G)=0.
    \]

    Then \(G_\Pi=\sigma h_\Pi\) can be compensated in the period row by
    \(\dot\tau=-\Pi(G_\Pi)>0\).  The nontrivial part is the six local rows:

    \[
    \boxed{
    A\dot y_\Pi+B G_\Pi=0.
    }
    \]

    Equivalently,

    \[
    \int_JK_i(x)G_\Pi(x)\omega(x)\,dx=0,
    \qquad i=1,2.
    \]

    In signed Cauchy notation,

    \[
    C_\Pi(s)=\int_J\frac{G_\Pi(x)\omega(x)}{x-s}\,dx,
    \qquad
    M_\Pi=\int_JG_\Pi(x)\omega(x)\,dx,
    \]

    this is the pair of balance equations

    \[
    \boxed{
    \left(-r-\frac abp\right)M_\Pi
    -\frac ab\int_u^cC_\Pi(s)\,ds
    +\int_c^vC_\Pi(s)\,ds=0,
    }
    \tag{P1}
    \]

    and

    \[
    \boxed{
    p\Gamma M_\Pi
    +aC_\Pi(u)
    +Q_cC_\Pi(c)
    +bC_\Pi(v)
    +\Gamma\int_u^cC_\Pi(s)\,ds=0.
    }
    \tag{P2}
    \]

    The corresponding sufficient proof target is:

    \[
    \boxed{\textbf{FreePeriodResidueAnnihilation}.}
    \]

    It should construct the normalized real period-transfer differential

    \[
    d\Omega_\Pi(z)=\frac{H_\Pi(z)}{Q(z)^2R(z)}\,dz
    \]

    or the equivalent finite-gap form in the chosen convention, prove its
    boundary density has sign

    \[
    d\Omega_\Pi|_J=G_\Pi(x)\omega(x)\,dx,
    \qquad
    G_\Pi=\sigma h_\Pi,\quad h_\Pi>0,
    \]

    and verify (P1),(P2) by residue/period calculation.

    This target is stronger than is needed for the regular free-period case.
    In a free-period chart the quotient part can already be checked by linear
    algebra.  Extend the local system by a period/filling variable \(\tau\):

    \[
    \begin{pmatrix}A&0\\0&1\end{pmatrix}
    \begin{pmatrix}\dot y\\\dot\tau\end{pmatrix}
    +
    \begin{pmatrix}B\\\Pi\end{pmatrix}G=0.
    \]

    If \((\kappa,\kappa_\Pi)\) is an extended left-cokernel, then

    \[
    (\kappa,\kappa_\Pi)^T
    \begin{pmatrix}A&0\\0&1\end{pmatrix}=0
    \]

    gives

    \[
    \kappa^TA=0,\qquad \kappa_\Pi=0.
    \]

    Thus the period row is absorbed by \(\tau\); it does not create an
    additional pointwise sign-shifter \(\lambda\pi_0\).  The relevant
    free-period normal space is still

    \[
    \operatorname{span}\{K_1,K_2\}.
    \]

    Moreover, in a regular free-period chamber one does not need (P1),(P2)
    separately.  Let the actual KKT normal be

    \[
    K_\theta=\theta_1K_1+\theta_2K_2,\qquad \theta\ne0,
    \]

    with the admissible oriented sign pattern

    \[
    \sigma K_\theta\ge0\quad\text{on }J_1\cup J_2.
    \]

    If the chamber has a two-sided free-period lineality

    \[
    G_\Pi=\sigma h_\Pi,\qquad h_\Pi>0,
    \]

    then normal-lineality orthogonality gives only the scalar identity

    \[
    0=\int_JK_\theta(x)G_\Pi(x)\omega(x)\,dx
    =\int_J\sigma(x)K_\theta(x)h_\Pi(x)\omega(x)\,dx.
    \]

    The last integrand is nonnegative and is not identically zero unless
    \(K_\theta\equiv0\).  Strict Chebyshev independence of the six-kernel span
    rules out such a nonzero cokernel combination vanishing on an open
    interval.  Therefore a regular free-period compact non-pinched \(g=2\)
    chamber is excluded.  This is a weaker and cleaner regular-case argument
    than proving (P1),(P2) for both basis vectors separately.

    Conditional chain for the stronger quadrature route:

    \[
    \boxed{
    \text{PeriodQuotientLemma}
    +\text{FreePeriodResidueAnnihilation}
    \Rightarrow
    \text{PositiveQuadrature}
    \Rightarrow
    \text{OvalConvexity}
    \Rightarrow
    \text{no compact non-pinched }g=2.
    }
    \]

    The free-period quotient part is now a linear-algebra check as above.
    FreePeriodResidueAnnihilation is not currently proved in the ledger; it
    remains a sufficient positive-quadrature certificate, not a necessary step
    for the regular case.  The remaining compact \(g=2\) hard case is
    rank-defect: the positive period-transfer density exists, but cannot be
    corrected to a two-sided local-row lineality.

    In that case set

    \[
    r_\Pi=
    \left(
    \int_JK_1G_\Pi\omega,\,
    \int_JK_2G_\Pi\omega
    \right)\in\mathbb R^2.
    \]

    A KKT normal with oriented sign pattern satisfies

    \[
    \theta\cdot r_\Pi
    =\int_JK_\theta G_\Pi\omega
    =\int_J\sigma K_\theta h_\Pi\omega>0.
    \]

    To exclude rank-defect compact \(g=2\), one must prove that \(r_\Pi\) is
    the projection of an admissible one-sided cone direction, so every KKT
    normal should satisfy \(\theta\cdot r_\Pi\le0\).  This is the current
    Schiffer/cone-descent hard mouth.  It requires an active-row orientation
    table for

    \[
    R_0,\ R_u,\ R_c,\ R_v,\ R_-,\ R_+.
    \]

    Without that cone-orientation table, rank-defect compact \(g=2\) is not
    excluded.

    Current compact \(g=2\) trichotomy.

    1. Regular free-period non-pinched chambers are excluded by the
       lineality/sign contradiction above.
    2. Pinching or positivity-boundary limits should be routed through the
       boundary reduction: the genus-two radical loses a pair of branch points,
       possible pole/zero collisions create only nonnegative endpoint atoms,
       and the limit is a corrected lower-genus candidate rather than a new
       compact non-pinched \(g=2\) chamber.
    3. The remaining unclosed case is a rank-defect non-pinched interior point.
       It requires a Schiffer/cone-descent argument, concretely the
       ConeOrientationTable for \(R_0,R_u,R_c,R_v,R_-,R_+\).

    Thus the current status is not "compact \(g=2\) fully killed"; it is
    "regular free-period killed, boundary routed to lower genus, rank-defect
    still open pending cone orientation."

    2026-05-06 anchored Schiffer first-variation target.

    The rank-defect cone target should now be stated as one lemma, not as a
    proliferation of new names:

    \[
    \boxed{\textbf{Anchored RankDefectSchifferConeLemma}.}
    \]

    The important correction is that the six local rows

    \[
    R_0,\ R_u,\ R_c,\ R_v,\ R_-,\ R_+
    \]

    do not by themselves determine the boundary values required by
    Proposition 4.1.  The rows \(R_-,R_+\) are endpoint potential differences:

    \[
    R_-=\delta W(c)-\delta W(u),\qquad
    R_+=\delta W(v)-\delta W(c),
    \]

    not absolute endpoint values.  Therefore the Schiffer/first-variation
    table must include an anchor row

    \[
    \boxed{
    R_{\ell c}(G)=\delta W(c)=
    \int_J\log\frac1{|c-x|}G(x)\omega(x)\,dx.
    }
    \]

    Then

    \[
    \delta W(u)=R_{\ell c}-R_-,\qquad
    \delta W(v)=R_{\ell c}+R_+.
    \]

    For the neck interval \((u,v)\), Proposition 4.1 gives the boundary
    contribution

    \[
    \delta L_{uv}
    =
    \frac{V(u)}{|U'(u)|}
    +
    \frac{V(v)}{|U'(v)|}.
    \]

    Since

    \[
    U'(u)=X>0,\qquad U'(v)=Y<0,\qquad Y=-\frac abX,
    \]

    and

    \[
    V(u)=R_{\ell c}-R_-,\qquad
    V(v)=R_{\ell c}+R_+,
    \]

    one obtains the checked formula

    \[
    \boxed{
    aX\,\delta L_{uv}
    =(a+b)R_{\ell c}-aR_-+bR_+.
    }
    \tag{ND}
    \]

    Thus a Schiffer rank-defect descent must produce, after equality-row
    corrections, at least the anchored neck descent inequality

    \[
    \boxed{
    (a+b)R_{\ell c}-aR_-+bR_+<0.
    }
    \]

    The proposed perturbation should have the regularized form

    \[
    V_{\rm Sch}^{(\rho)}
    =
    U_{\nu_\Pi}
    +\sum_m s_m V_{{\rm Schiffer},m}^{(\rho)}
    +\sum_\ell t_\ell V_{{\rm local},\ell},
    \]

    where the Schiffer terms are cutoff-regularized before applying
    Proposition 4.1.  The lemma must verify four concrete items:

    1. \(V_{\rm Sch}^{(\rho)}\) satisfies Proposition 4.1 regularity and
       admissibility: \(C^1\) near moving boundaries, continuous near \(Z_0\),
       bounded below on compact subsets of \(E\), and compatible with the
       one-sided perturbation class.
    2. Interior-zero protection:
       \[
       V_{\rm Sch}^{(\rho)}<0\quad\text{on }Z_0.
       \]
    3. Boundary descent, including (ND) and all other superlevel endpoints:
       \[
       \sum_j
       \left(
       \frac{V_{\rm Sch}^{(\rho)}(a_j)}{|U'(a_j)|}
       +
       \frac{V_{\rm Sch}^{(\rho)}(b_j)}{|U'(b_j)|}
       \right)<0.
       \]
    4. Row/cokernel projection: the projected one-sided row direction is
       \(r_\Pi+o_\rho(1)\), or at least pairs positively with every oriented
       sign-pattern normal \(K_\theta\), while the feasible cone orientation
       forces the opposite KKT sign.

    Equivalently, after local equality corrections, the next construction is
    the anchored semi-infinite linear feasibility problem

    \[
    \boxed{
    R_0=0,\qquad
    R_c=0,\qquad
    (a+b)R_{\ell c}-aR_-+bR_+<0,\qquad
    V|_{Z_0}<0.
    }
    \tag{LP}
    \]

    If this LP has a solution satisfying the projection condition, rank-defect
    compact \(g=2\) is excluded.  If it fails, the Hahn-Banach/Farkas dual
    produces an additional boundary/\(Z_0\) multiplier; that dual object must
    then be shown to fall back into the already excluded regular KKT normal,
    or to force pinching/lower-genus degeneration.  This is now the concrete
    rank-defect hard mouth.

    2026-05-07 review update: safe LP versus state-lifted LP.

    The LP above is the conservative regularity-safe version.  It imposes

    \[
    R_0=0,\qquad R_c=0
    \]

    before measuring the length derivative.  This avoids formal atom-weight
    and atom-center perturbations, whose first-order potentials may contain
    singular terms at \(c\) and therefore cannot be inserted into Proposition
    4.1 without a separate regularity check.

    If one first applies the branch state-lift, the length derivative changes
    by the local state response.  Using the current branch convention

    \[
    \delta M=R_0,\qquad \delta F=-R_c,
    \]

    and the state-lift rows

    \[
    \delta a=
    \frac{R_{\ell c}-R_- -pR_0+\frac{A}{F_c}R_c}{X},
    \]

    \[
    \delta b=
    \frac{rR_0-(R_{\ell c}+R_+)-\frac{B}{F_c}R_c}{Y},
    \]

    where \(F_c=F_\xi'(c)\), \(X>0\), \(Y<0\), and \(Y=-aX/b\), one obtains

    \[
    aX(\delta a+\delta b)
    =
    (a+b)R_{\ell c}-aR_-+bR_+
    -(ap+br)R_0
    +\frac{aA+bB}{F_c}R_c.
    \]

    The stationarity relation \(aA+bB=0\) cancels the \(R_c\)-term, hence the
    state-lifted neck derivative is

    \[
    \boxed{
    aX\,\delta L_{uv}^{\rm lift}
    =
    (a+b)R_{\ell c}-aR_-+bR_+-(ap+br)R_0.
    }
    \tag{SL-ND}
    \]

    Thus the documented LP is a sufficient slice of the weaker state-lifted
    inequality

    \[
    (a+b)R_{\ell c}-aR_-+bR_+-(ap+br)R_0<0.
    \tag{SL-LP}
    \]

    The weaker version may be useful if the safe LP is infeasible, but it
    requires a new atom-state regularity check: the finite-\(\varepsilon\)
    variation of the atom weight and center must satisfy the regularity and
    admissibility hypotheses behind Proposition 4.1.  Without that check,
    (SL-LP) is only a formal state-lift calculation.

    Farkas fallback must also be stated with two safeguards.  First, failure
    of the safe LP can occur because the equality rows \(R_0=R_c=0\) are not
    reachable inside the chosen regularized Schiffer/local class; that is an
    equality-feasibility failure, not yet a boundary/\(Z_0\) descent
    obstruction.  Second, the separation theorem must be applied in a fixed
    topological vector space where endpoint evaluation, the anchor row, and
    restriction to \(Z_0\) are continuous, and with the relevant cone closures
    specified.  Only after these two points are fixed does LP infeasibility
    produce a dual functional of the form

    \[
    \lambda_0R_0+\lambda_cR_c
    +\eta\bigl((a+b)R_{\ell c}-aR_-+bR_+\bigr)
    +\int_{Z_0}(\cdot)\,d\zeta,
    \]

    with \(\eta\ge0\) and \(\zeta\ge0\).  The next required computation is to
    write the local-correction table, the regularized Schiffer endpoint table,
    and the \(Z_0\)-pairing table for this dual fallback, then prove that the
    fallback either returns to the already excluded regular KKT normal or
    forces pinching/lower-genus degeneration.

    2026-05-07 reduced anchored LP and conditional Hilbert fallback.

    The equality-row reachability issue can be removed without using
    atom-weight or atom-center state variations.  Choose two smooth signed
    density bumps \(\psi_1,\psi_2\) supported in positive-density regular
    interiors of \(J_1\cup J_2\), away from \(u,c,v\), branch endpoints, and
    the \(Z_0\)-boundary.  Normalize them so that

    \[
    R_0(\psi_i)=\int_J\psi_i(x)\omega(x)\,dx=1.
    \]

    If the bump supports shrink to two distinct points \(x_1,x_2\ne c\), then

    \[
    R_c(\psi_i)=
    \int_J\frac{\psi_i(x)\omega(x)}{x-c}\,dx
    \longrightarrow \frac1{x_i-c}.
    \]

    Hence

    \[
    M=
    \begin{pmatrix}
    R_0(\psi_1)&R_0(\psi_2)\\
    R_c(\psi_1)&R_c(\psi_2)
    \end{pmatrix}
    \]

    is invertible for sufficiently small supports, since its limiting
    determinant is

    \[
    \frac1{x_2-c}-\frac1{x_1-c}
    =
    \frac{x_1-x_2}{(x_1-c)(x_2-c)}\ne0.
    \]

    For a density seed \(G\), write

    \[
    E(G)=
    \binom{R_0(G)}{R_c(G)},\qquad
    t(G)=-M^{-1}E(G),
    \]

    and define the equality-corrected density and potential by

    \[
    \widehat G=G+\sum_{j=1}^2t_j(G)\psi_j,\qquad
    \widehat V=V_G+\sum_{j=1}^2t_j(G)U_{\psi_j}.
    \]

    Then

    \[
    R_0(\widehat G)=R_c(\widehat G)=0.
    \]

    This is a genuine regularity-safe correction: the bumps are smooth and
    supported where the background density is strictly positive, so for small
    amplitudes they remain two-sided density corrections and their potentials
    are \(C^1\) near the moving boundary and continuous near \(Z_0\).

    Define

    \[
    B_{\rm safe}(G)
    =(a+b)R_{\ell c}(G)-aR_-(G)+bR_+(G),
    \]

    and

    \[
    \beta=
    \binom{B_{\rm safe}(\psi_1)}
          {B_{\rm safe}(\psi_2)}.
    \]

    The reduced boundary functional is

    \[
    \boxed{
    B_{\rm red}(G)
    :=
    B_{\rm safe}(\widehat G)
    =
    B_{\rm safe}(G)-\beta^TM^{-1}E(G).
    }
    \tag{Bred}
    \]

    Thus the safe anchored LP is equivalent to the reduced problem

    \[
    \boxed{
    B_{\rm red}(G)<0,\qquad
    \widehat V<0\quad\text{on }Z_0,
    }
    \tag{RLP}
    \]

    together with the already stated Proposition 4.1 regularity and
    admissibility checks.  If (RLP) is feasible for a regularized
    period/Schiffer seed, then the compact \(g=2\) rank-defect chamber is ruled
    out by the same one-sided length-decrease argument as before.

    If the reduced LP is infeasible, the cleaner Farkas fallback has no
    independent equality multipliers.  In a fixed topology where endpoint
    values, \(R_{\ell c}\), \(R_0\), \(R_c\), and restriction to \(Z_0\) are
    continuous, separation gives \(\eta\ge0\) and a positive measure
    \(\zeta\) on \(Z_0\), not both zero, such that

    \[
    \eta B_{\rm red}(G)+\int_{Z_0}\widehat V\,d\zeta\ge0
    \tag{FD}
    \]

    for every allowed regularized seed \(G\).  Expanding the equality
    correction gives

    \[
    \mathcal D_{\eta,\zeta}(G)
    =
    \eta B_{\rm safe}(G)
    +\int_{Z_0}V_G\,d\zeta
    -
    (\eta\beta+\gamma)^TM^{-1}E(G),
    \tag{D}
    \]

    where

    \[
    \gamma=
    \binom{\int_{Z_0}U_{\psi_1}\,d\zeta}
          {\int_{Z_0}U_{\psi_2}\,d\zeta}.
    \]

    This is the precise reduced dual.  It is equivalent to the unreduced form
    with equality multipliers

    \[
    \binom{\lambda_0}{\lambda_c}
    =
    -M^{-T}(\eta\beta+\gamma).
    \]

    The reduced Farkas statement must now be interpreted on the actual
    allowed seed space.  If the allowed rank-defect seeds are only

    \[
    \mathcal I=\{\Pi,\alpha_1,\beta_1,\alpha_2,\beta_2\},
    \]

    where \(\Pi\) is the period-transfer seed and the other four seeds are
    regularized Schiffer endpoint seeds, then the seed space is finite
    dimensional.  In that case the Farkas dual gives only finitely many
    endpoint-seed equations.  It does not imply a pointwise kernel identity on
    \(J\).

    For each seed \(j\in\mathcal I\), define

    \[
    b_j=B_{\rm red}(G_j),\qquad
    f_j=\widehat V_{G_j}|_{Z_0}.
    \]

    Fix the period-seed coefficient to be one and vary only the four endpoint
    Schiffer coefficients:

    \[
    G=G_\Pi+\sum_{\gamma}s_\gamma G_\gamma^{(\rho)},
    \qquad
    \gamma\in\{\alpha_1,\beta_1,\alpha_2,\beta_2\}.
    \]

    The reduced rank-defect LP is the affine semi-infinite system

    \[
    \boxed{
    b_\Pi+\sum_\gamma s_\gamma b_\gamma<0,
    }
    \tag{L0}
    \]

    \[
    \boxed{
    f_\Pi(x)+\sum_\gamma s_\gamma f_\gamma(x)<0
    \quad (x\in Z_0).
    }
    \tag{LZ}
    \]

    If this affine LP is infeasible, finite-dimensional Farkas gives
    \(\eta\ge0\) and a positive measure \(\zeta\) on \(Z_0\), not both zero,
    such that

    \[
    \boxed{
    \eta b_\gamma+\int_{Z_0}f_\gamma\,d\zeta=0
    \quad
    \text{for each }
    \gamma\in\{\alpha_1,\beta_1,\alpha_2,\beta_2\},
    }
    \tag{D1}
    \]

    and

    \[
    \boxed{
    \eta b_\Pi+\int_{Z_0}f_\Pi\,d\zeta\ge0.
    }
    \tag{D2}
    \]

    This is the correct fallback for the finite Schiffer seed span.  No
    principal-value equation follows from (D1),(D2) alone.

    Moreover, \(\zeta\) can be made finite atomic.  The measure enters only
    through the five numbers

    \[
    \int_{Z_0}
    \begin{pmatrix}
    f_{\alpha_1}\\
    f_{\beta_1}\\
    f_{\alpha_2}\\
    f_{\beta_2}\\
    f_\Pi
    \end{pmatrix}
    d\zeta.
    \]

    By conic Carathéodory in \(\mathbb R^5\), the same five moments are
    realized by an atomic measure

    \[
    \zeta_*=\sum_{k=1}^{N}w_k\delta_{x_k},
    \qquad
    1\le N\le5,\quad w_k>0,\quad x_k\in Z_0.
    \]

    Therefore infeasibility of the affine reduced LP yields the finite atomic
    obstruction

    \[
    \boxed{
    \eta b_\gamma+\sum_{k=1}^{N}w_k f_\gamma(x_k)=0
    \quad
    \text{for every endpoint seed }\gamma,
    }
    \tag{Egamma}
    \]

    and

    \[
    \boxed{
    \eta b_\Pi+\sum_{k=1}^{N}w_k f_\Pi(x_k)\ge0.
    }
    \tag{Epi}
    \]

    The remaining finite obstruction is:

    \[
    \boxed{\textbf{AtomicFallbackExclusion}.}
    \]

    Prove that no \(\eta\ge0\), \(1\le N\le5\), \(w_k>0\), and
    \(x_k\in Z_0\) satisfy \((\mathrm{Egamma})\), \((\mathrm{Epi})\), unless
    the candidate lies on a pinching, positivity-boundary, or lower-genus
    degeneration.  If this atomic fallback is excluded, the affine reduced LP
    is feasible and rank-defect compact non-pinched \(g=2\) is ruled out.

    The entries needed for this finite problem are the reduced Schiffer table:

    \[
    b_j
    =
    B_{\rm safe}(G_j)-\beta^TM^{-1}E(G_j),
    \]

    \[
    f_j(x)
    =
    V_{G_j}(x)-
    (U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}E(G_j),
    \qquad x\in Z_0.
    \]

    For an endpoint Schiffer seed \(\gamma\), this means

    \[
    b_\gamma=
    (a+b)R_{\ell c}^\gamma-aR_-^\gamma+bR_+^\gamma
    -\beta^TM^{-1}
    \binom{R_0^\gamma}{R_c^\gamma},
    \]

    \[
    f_\gamma(x)=
    V_\gamma(x)-
    (U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}
    \binom{R_0^\gamma}{R_c^\gamma}.
    \]

    Thus the next mandatory computation is the reduced Schiffer endpoint
    table

    \[
    R_0^\gamma,\quad R_c^\gamma,\quad R_{\ell c}^\gamma,\quad
    R_-^\gamma,\quad R_+^\gamma,\quad V_\gamma|_{Z_0},
    \]

    for \(\gamma=\alpha_1,\beta_1,\alpha_2,\beta_2\), plus the corresponding
    period-seed entries.

    2026-05-07 boundary-neutral correctors and circuit test.

    The equality-correction bumps can be chosen so that they do not alter the
    boundary descent functional.  Write

    \[
    B_{\rm safe}(G)=aV_G(u)+bV_G(v),
    \]

    which is the same as

    \[
    (a+b)R_{\ell c}(G)-aR_-(G)+bR_+(G)
    \]

    by the anchor identities.  Choose three regular interior points
    \(x_1,x_2,x_3\) in \(J_1\cup J_2\), away from \(u,c,v\), branch endpoints,
    and the \(Z_0\)-boundary.  A unit bump at \(x\) has limiting rows

    \[
    (R_0,R_c,B_{\rm safe})
    =
    \left(
    1,\frac1{x-c},
    a\log\frac1{|u-x|}+b\log\frac1{|v-x|}
    \right).
    \]

    Let

    \[
    k(x)=\frac1{x-c},\qquad
    \ell(x)=a\log\frac1{|u-x|}+b\log\frac1{|v-x|}.
    \]

    The function \(\ell\) is not an affine function of \(k\) on any regular
    interval.  Otherwise \(\ell(x)=A+B(x-c)^{-1}\) on an interval, and after
    differentiation the logarithmic side has simple poles at \(u,v\), while
    the right side has only the pole structure at \(c\).  Hence one can choose
    \(x_1,x_2,x_3\) so that

    \[
    (1,k(x_i),\ell(x_i)),\qquad i=1,2,3,
    \]

    are linearly independent.  In the span of the three corresponding smooth
    local bumps, the condition \(B_{\rm safe}=0\) has a two-dimensional kernel.
    On this kernel, the map \(G\mapsto(R_0(G),R_c(G))\) is injective; otherwise
    the same signed combination would annihilate the three independent rows
    \((1,k,\ell)\).  Thus we may choose two smooth signed bumps
    \(\psi_1,\psi_2\) such that

    \[
    B_{\rm safe}(\psi_1)=B_{\rm safe}(\psi_2)=0,
    \]

    and

    \[
    M=
    \begin{pmatrix}
    R_0(\psi_1)&R_0(\psi_2)\\
    R_c(\psi_1)&R_c(\psi_2)
    \end{pmatrix}
    \]

    is invertible.  These are signed smooth correctors, not positive bumps;
    this is harmless because they are supported in strict positive-density
    interiors and are used only with small amplitudes.  If such a regular
    triple of points cannot be chosen, that is already a degeneration of the
    regular compact chamber rather than a new interior rank-defect case.

    With these boundary-neutral correctors, \(\beta=0\), so

    \[
    \boxed{
    B_{\rm red}(G)=B_{\rm safe}(G)=aV_G(u)+bV_G(v).
    }
    \tag{Bneutral}
    \]

    The \(Z_0\)-functions still require equality correction:

    \[
    \boxed{
    f_j(x)=
    V_{G_j}(x)-
    (U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}E(G_j),
    \qquad x\in Z_0.
    }
    \]

    Hence the reduced Schiffer table may be simplified to the entries

    \[
    b_j=aV_{G_j}(u)+bV_{G_j}(v),
    \qquad
    f_j=\widehat V_{G_j}|_{Z_0}.
    \]

    For the finite-dimensional LP, set

    \[
    F(x)=
    \begin{pmatrix}
    f_{\alpha_1}(x)\\
    f_{\beta_1}(x)\\
    f_{\alpha_2}(x)\\
    f_{\beta_2}(x)
    \end{pmatrix},
    \qquad
    b=
    \begin{pmatrix}
    b_{\alpha_1}\\
    b_{\beta_1}\\
    b_{\alpha_2}\\
    b_{\beta_2}
    \end{pmatrix},
    \]

    and

    \[
    \tau(x)=f_\Pi(x),\qquad \tau_*=b_\Pi.
    \]

    The reduced LP is

    \[
    b\cdot s+\tau_*<0,\qquad
    F(x)\cdot s+\tau(x)<0\quad(x\in Z_0).
    \]

    Under the fixed topology/closure assumptions stated above, finite
    Farkas and conic Carathéodory give the following equivalent obstruction:
    LP infeasibility produces a positive relation

    \[
    \eta b+\sum_k w_kF(x_k)=0,
    \qquad
    \eta\ge0,\quad w_k>0,\quad x_k\in Z_0,
    \]

    with

    \[
    \eta\tau_*+\sum_k w_k\tau(x_k)\ge0.
    \]

    Conversely, if there is \(s\) satisfying the reduced LP, every such
    positive relation has strictly negative lifted value, because

    \[
    \eta\tau_*+\sum_k w_k\tau(x_k)
    =
    \eta(b\cdot s+\tau_*)+
    \sum_k w_k(F(x_k)\cdot s+\tau(x_k))<0.
    \]

    Thus `AtomicFallbackExclusion` can be checked as positive-circuit
    negativity: every positive circuit in the first four coordinates must have
    negative lifted value.  In determinant form:

    - If \(\eta>0\), normalize \(\eta=1\).  For four points \(x_1,\ldots,x_4\)
      with \(F_X=[F(x_1)\ \cdots\ F(x_4)]\) invertible, the weights are
      \(w=-F_X^{-1}b\).  Whenever \(w_i>0\), one must prove
      \[
      \tau_*+\sum_{i=1}^4w_i\tau(x_i)
      =
      \tau_*-\tau_X^TF_X^{-1}b<0.
      \tag{C4}
      \]
    - If \(\eta=0\), a five-point positive circuit
      \(\sum_{i=1}^5w_iF(x_i)=0\), \(w_i>0\), must satisfy
      \[
      \sum_{i=1}^5w_i\tau(x_i)<0.
      \tag{C5}
      \]

    Degenerate determinants reduce to smaller support circuits or to the
    pinching/positivity-boundary routing.  The determinant signs (C4),(C5)
    cannot be checked until the explicit reduced Schiffer seed functions
    \(V_\Pi,V_{\alpha_1},V_{\beta_1},V_{\alpha_2},V_{\beta_2}\) and their
    equality-row values are written down.

    2026-05-07 Schiffer seed normalization checkpoint.

    Attempting the next computation exposes a genuine missing definition.  The
    ledger currently uses symbols

    \[
    G_\gamma^{(\rho)},\qquad V_\gamma^{(\rho)},
    \qquad \gamma\in\{\alpha_1,\beta_1,\alpha_2,\beta_2\},
    \]

    but it has not yet defined which endpoint Schiffer seed these symbols mean.
    Hence the reduced table

    \[
    V_j(u),\quad V_j(v),\quad
    E(G_j)=
    \binom{R_0(G_j)}{R_c(G_j)},\quad V_j|_{Z_0}
    \]

    is not determined from the present text.  One cannot honestly verify
    (C4),(C5) before this convention is fixed.

    The ambiguity is not cosmetic.  With

    \[
    F(z)=\frac{P(z)}{Q(z)}R(z),\qquad
    R(z)^2=\prod_{\delta\in\{\alpha_1,\beta_1,\alpha_2,\beta_2\}}(z-\delta),
    \]

    the raw coordinate derivative of the branch factor is

    \[
    \partial_\gamma R(z)=-\frac{R(z)}{2(z-\gamma)}.
    \]

    If \(P,Q\) are held frozen, this gives the raw candidate

    \[
    \delta_\gamma F_{\rm raw}(z)
    =
    -\frac{P(z)R(z)}{2Q(z)(z-\gamma)}.
    \]

    But this raw object is not yet an admissible seed: it may change the
    infinity normalization, residues, period/filling row, pole data, and the
    branch row \(F(c)\).  Different ways of repairing these defects change
    \(E(G_\gamma)\), \(V_\gamma|_{Z_0}\), and therefore the circuit signs.

    The next calculation must therefore first fix the endpoint seed
    normalization.  In the current finite-gap notation the admissible endpoint
    variation should be written in the form

    \[
    \delta_\gamma F(z)
    =
    \frac{\Delta_\gamma P(z)}{Q(z)}R(z)
    -\frac{P(z)R(z)}{2Q(z)(z-\gamma)}
    -\frac{P(z)R(z)}{Q(z)^2}\Delta_\gamma Q(z),
    \tag{SchifferSeed}
    \]

    with the chosen convention specifying which of \(\Delta_\gamma P\) and
    \(\Delta_\gamma Q\) are allowed.  The unknown correction is then determined
    by the finite linear conditions required in the chosen chart:

    - cancellation of unwanted poles or residue changes;
    - the prescribed decay/total-mass normalization at infinity;
    - the fixed or free period/filling convention;
    - the branch row convention for \(F(c)\);
    - compatibility with the regularized Schiffer cutoff as \(\rho\to0\).

    Only after solving this finite normalization system can one set
    \(G_\gamma\omega\,dx\) to the boundary density associated with
    \(\delta_\gamma F\), define \(V_\gamma=U_{G_\gamma\omega dx}\), and compute

    \[
    b_\gamma=aV_\gamma(u)+bV_\gamma(v),
    \qquad
    f_\gamma(x)=
    V_\gamma(x)
    -(U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}E(G_\gamma).
    \]

    The convention used below fixes this missing object.  The determinant test
    is still not executed here, but the endpoint seeds are now defined.

    Work in the fixed-cut density chart.  Put

    \[
    D_\gamma(z)=\frac{D(z)}{z-\gamma}.
    \]

    The raw endpoint motion can be rewritten as a fixed-cut Cauchy-transform
    numerator:

    \[
    -\frac{P(z)R(z)}{2Q(z)(z-\gamma)}
    =
    \frac{H_\gamma^{\rm raw}(z)}{Q(z)^2R(z)},
    \qquad
    H_\gamma^{\rm raw}(z)=-\frac12P(z)Q(z)D_\gamma(z).
    \tag{RawH}
    \]

    Let \(\mathcal N\) denote the finite list of normalization functionals
    required in the chosen chart: unwanted principal parts at off-cut poles,
    the forbidden part of the Laurent expansion at infinity, and the selected
    fixed/free period convention.  The equality rows \(R_0\) and \(R_c\) are
    deliberately not included in \(\mathcal N\), because the boundary-neutral
    smooth bumps \(\psi_1,\psi_2\) correct them later.

    Let \(\mathcal P_{\rm corr}\) be the real vector space of polynomial
    numerators \(H\) for correction terms

    \[
    C_H(z)=\frac{H(z)}{Q(z)^2R(z)}.
    \]

    Remove redundant normalization rows and choose a finite-dimensional real
    subspace \(\mathcal H_{\rm norm}\subset\mathcal P_{\rm corr}\) such that

    \[
    \mathcal N:\mathcal H_{\rm norm}\longrightarrow \operatorname{im}\mathcal N
    \]

    is an isomorphism.  This choice is always possible after restricting to
    the image: pick correction numerators whose \(\mathcal N\)-values form a
    basis of \(\operatorname{im}\mathcal N\).  If an intended normalization row
    is not in this image, then that row is not controllable in the present
    finite-gap chart and the point is not in the regular Schiffer chart being
    treated here.

    Define \(H_\gamma^{\rm corr}\in\mathcal H_{\rm norm}\) uniquely by

    \[
    \mathcal N(H_\gamma^{\rm corr})
    =
    \mathcal N(H_\gamma^{\rm raw}),
    \]

    and set

    \[
    \boxed{
    H_\gamma=H_\gamma^{\rm raw}-H_\gamma^{\rm corr},
    \qquad
    \delta_\gamma F(z)=\frac{H_\gamma(z)}{Q(z)^2R(z)}.
    }
    \tag{NormSchiffer}
    \]

    Then \(\mathcal N(\delta_\gamma F)=0\), so \(\delta_\gamma F\) has exactly
    the chart normalizations imposed above.

    The proof of well-definedness is finite-dimensional linear algebra.  The
    raw numerator \(H_\gamma^{\rm raw}\) is explicit by (RawH).  Since
    \(\mathcal N|\mathcal H_{\rm norm}\) is an isomorphism onto its image,
    there is a unique \(H_\gamma^{\rm corr}\) with the required normalization
    data.  Subtracting it kills the forbidden normalization components and
    leaves a real-symmetric meromorphic variation of the fixed-cut form
    \(H/(Q^2R)\).

    Because all forbidden off-cut principal parts and forbidden infinity terms
    have been killed, \(\delta_\gamma F\) is analytic on
    \(\mathbb C\setminus J\), has the prescribed \(O(1/z)\)-type Cauchy
    behavior at infinity, and has only the square-root jump across \(J\).  By
    the Plemelj formula it is the Cauchy transform of a finite signed density
    on \(J\):

    \[
    \delta_\gamma F(z)
    =
    \int_J\frac{G_\gamma(x)\omega(x)}{z-x}\,dx,
    \qquad z\notin J.
    \tag{SeedCauchy}
    \]

    This equation defines \(G_\gamma\).  Near the moved endpoint
    \(\gamma\), the density has at worst the integrable behavior
    \(O(|x-\gamma|^{-1/2})\,dx\), because \(R(x)\) has a square-root zero.
    Therefore the logarithmic potential

    \[
    V_\gamma(s)=
    \int_J\log\frac1{|s-x|}G_\gamma(x)\omega(x)\,dx
    \tag{SeedPotential}
    \]

    is finite at \(s=u,v\) and on \(Z_0\).

    For the regularized Schiffer seed, choose a smooth cutoff
    \(\chi_{\gamma,\rho}\) that vanishes on \(|x-\gamma|<\rho\), equals \(1\)
    on \(|x-\gamma|>2\rho\), and is supported in the same cut component.  Let

    \[
    d\nu_{\gamma,\rho}(x)
    =
    \chi_{\gamma,\rho}(x)G_\gamma(x)\omega(x)\,dx,
    \qquad
    V_\gamma^{(\rho)}=U_{\nu_{\gamma,\rho}}.
    \]

    Since

    \[
    \int_0^{2\rho}t^{-1/2}|\log t|\,dt
    =
    O(\sqrt\rho\,|\log\rho|),
    \]

    the cutoff error tends to zero in all rows whose kernels are smooth at
    \(\gamma\), and in the logarithmic potential uniformly on \(Z_0\).  In
    particular

    \[
    V_\gamma^{(\rho)}(u)\to V_\gamma(u),\qquad
    V_\gamma^{(\rho)}(v)\to V_\gamma(v),
    \qquad
    E(G_{\gamma,\rho})\to E(G_\gamma),
    \]

    and

    \[
    V_\gamma^{(\rho)}|_{Z_0}\to V_\gamma|_{Z_0}.
    \]

    Thus the reduced Schiffer table is now well-defined by

    \[
    b_\gamma=aV_\gamma(u)+bV_\gamma(v),
    \qquad
    f_\gamma(x)=
    V_\gamma(x)
    -(U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}E(G_\gamma).
    \tag{SchifferTableEntry}
    \]

    The equality rows in \(E(G_\gamma)\) are read directly from
    \(\delta_\gamma F\):

    \[
    R_0(G_\gamma)=[z^{-1}]_\infty\,\delta_\gamma F(z),
    \qquad
    R_c(G_\gamma)=-\delta_\gamma F(c),
    \tag{SeedRows}
    \]

    using the existing convention \(\delta F(c)=-R_c(G)\).  Potential
    differences off \(J\) are also determined by

    \[
    V_\gamma(t)-V_\gamma(s)
    =
    -\int_s^t\delta_\gamma F(y)\,dy,
    \qquad s,t\notin J,
    \]

    while the absolute values \(V_\gamma(u),V_\gamma(v)\) are fixed by the
    logarithmic integral in (SeedPotential).  Thus the table is computable from
    the single normalized rational function \(\delta_\gamma F\).

    Therefore the reduced Schiffer seed table is:

    \[
    C_j(z):=\int_J\frac{G_j(x)\omega(x)}{z-x}\,dx,
    \qquad
    E_j:=
    \binom{R_0(G_j)}{R_c(G_j)}.
    \]

    \[
    \boxed{
    \begin{array}{c|c|c|c|c}
    j & C_j(z) & E_j & b_j & f_j(x)\\ \hline
    \Pi
    &
    \displaystyle C_\Pi(z)=\frac{H_\Pi(z)}{Q(z)^2R(z)}
    &
    \displaystyle
    \binom{[z^{-1}]_\infty C_\Pi}{-C_\Pi(c)}
    &
    \displaystyle aV_\Pi(u)+bV_\Pi(v)
    &
    \displaystyle
    V_\Pi(x)-(U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}E_\Pi
    \\[1.2em]
    \gamma\in\{\alpha_1,\beta_1,\alpha_2,\beta_2\}
    &
    \displaystyle
    C_\gamma(z)=\frac{H_\gamma(z)}{Q(z)^2R(z)}
    &
    \displaystyle
    \binom{[z^{-1}]_\infty C_\gamma}{-C_\gamma(c)}
    &
    \displaystyle aV_\gamma(u)+bV_\gamma(v)
    &
    \displaystyle
    V_\gamma(x)-(U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}E_\gamma
    \end{array}
    }
    \tag{ReducedSchifferTable}
    \]

    Here

    \[
    H_\gamma
    =
    -\frac12PQD_\gamma
    -
    H_\gamma^{\rm corr},
    \qquad
    \mathcal N(H_\gamma^{\rm corr})
    =
    \mathcal N\!\left(-\frac12PQD_\gamma\right),
    \]

    and \(H_\Pi\) is the already chosen period-transfer numerator in the same
    fixed-cut chart.  The potentials in the table are

    \[
    V_j(s)=\int_J\log\frac1{|s-x|}G_j(x)\omega(x)\,dx,
    \qquad j\in\{\Pi,\alpha_1,\beta_1,\alpha_2,\beta_2\}.
    \]

    This is the complete reduced seed table used by the finite-dimensional LP.
    Substituting it gives

    \[
    F(x)=
    \begin{pmatrix}
    f_{\alpha_1}(x)\\
    f_{\beta_1}(x)\\
    f_{\alpha_2}(x)\\
    f_{\beta_2}(x)
    \end{pmatrix},
    \qquad
    b=
    \begin{pmatrix}
    b_{\alpha_1}\\
    b_{\beta_1}\\
    b_{\alpha_2}\\
    b_{\beta_2}
    \end{pmatrix},
    \qquad
    \tau=f_\Pi,\quad \tau_*=b_\Pi.
    \]

    Matrix expansion of the endpoint rows.

    Choose a basis \(B_1,\ldots,B_r\) of \(\mathcal H_{\rm norm}\), and write
    the independent normalization functionals as
    \(\mathcal N_1,\ldots,\mathcal N_r\).  Put

    \[
    A_{im}:=\mathcal N_i(B_m).
    \]

    By construction \(A\) is invertible.  For

    \[
    H_\gamma^{\rm raw}=-\frac12PQD_\gamma
    \]

    set

    \[
    n_\gamma:=
    \bigl(\mathcal N_i(H_\gamma^{\rm raw})\bigr)_{i=1}^r,
    \qquad
    h_\gamma:=A^{-1}n_\gamma.
    \]

    Then

    \[
    \boxed{
    H_\gamma
    =
    H_\gamma^{\rm raw}
    -
    \sum_{m=1}^r(h_\gamma)_mB_m.
    }
    \tag{MatrixSchiffer}
    \]

    Define, for any numerator \(H\),

    \[
    C_H(z)=\frac{H(z)}{Q(z)^2R(z)},
    \qquad
    E(H)=
    \binom{[z^{-1}]_\infty C_H}{-C_H(c)},
    \]

    \[
    V_H(s)=
    \int_J\log\frac1{|s-x|}G_H(x)\omega(x)\,dx,
    \qquad
    C_H(z)=\int_J\frac{G_H(x)\omega(x)}{z-x}\,dx,
    \]

    and the reduced row maps

    \[
    b(H)=aV_H(u)+bV_H(v),
    \]

    \[
    f_H(x)=
    V_H(x)
    -(U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}E(H).
    \]

    These maps are linear in \(H\).  Therefore the endpoint seed table entries
    have the explicit matrix form

    \[
    \boxed{
    E_\gamma
    =
    E(H_\gamma^{\rm raw})
    -
    \sum_{m=1}^r(h_\gamma)_mE(B_m),
    }
    \tag{EndpointE}
    \]

    \[
    \boxed{
    b_\gamma
    =
    b(H_\gamma^{\rm raw})
    -
    \sum_{m=1}^r(h_\gamma)_mb(B_m),
    }
    \tag{EndpointB}
    \]

    and

    \[
    \boxed{
    f_\gamma(x)
    =
    f_{H_\gamma^{\rm raw}}(x)
    -
    \sum_{m=1}^r(h_\gamma)_mf_{B_m}(x).
    }
    \tag{EndpointF}
    \]

    Equivalently, the four endpoint columns are obtained by multiplying the raw
    normalization matrix

    \[
    N_\Gamma=
    \bigl[n_{\alpha_1}\ n_{\beta_1}\ n_{\alpha_2}\ n_{\beta_2}\bigr]
    \]

    by \(A^{-1}\), then subtracting the corresponding correction columns from
    the raw rows.  This is the reduced Schiffer seed table in computable
    finite-dimensional form.  No density-closure or PV step is used.

    In the free-period fixed-\(Q\) chart this matrix has a concrete Hermite
    form.  Assume the regular non-pinched case in which

    \[
    Q(z)=\prod_{k=1}^d(z-p_k),
    \qquad p_k\notin J\cup\{u,c,v\},
    \qquad Q'(p_k)\ne0.
    \]

    Pole collisions or multiple \(Q\)-zeros are boundary cases and are routed
    to the pinching/lower-genus part of the proof.  The normalization rows are
    only the off-cut pole-cancellation rows

    \[
    \mathcal N_{k,0}(H)=H(p_k),\qquad
    \mathcal N_{k,1}(H)=H'(p_k),
    \qquad k=1,\ldots,d.
    \tag{FixedQN}
    \]

    There is no period row in this free-period chart, and \(R_0,R_c\) are not
    included because they are corrected by \(\psi_1,\psi_2\).  The forbidden
    Laurent terms at infinity are absent if the correction numerators are
    chosen in \(\mathbb R[z]_{\le 2d-1}\): then
    \(H/(Q^2R)=O(z^{-3})\) for \(g=2\), hence certainly has Cauchy-transform
    decay.

    Let \(L_k(z)\) be the Lagrange polynomials for \(p_1,\ldots,p_d\):

    \[
    L_k(z)=\prod_{\ell\ne k}\frac{z-p_\ell}{p_k-p_\ell}.
    \]

    The Hermite basis of \(\mathbb R[z]_{\le 2d-1}\) is

    \[
    B_{k,0}(z)=\bigl(1-2L_k'(p_k)(z-p_k)\bigr)L_k(z)^2,
    \]

    \[
    B_{k,1}(z)=(z-p_k)L_k(z)^2.
    \]

    It satisfies

    \[
    B_{k,0}(p_\ell)=\delta_{k\ell},\qquad
    B'_{k,0}(p_\ell)=0,
    \]

    \[
    B_{k,1}(p_\ell)=0,\qquad
    B'_{k,1}(p_\ell)=\delta_{k\ell}.
    \]

    Hence the normalization matrix for the ordered rows
    \((\mathcal N_{1,0},\mathcal N_{1,1},\ldots,\mathcal N_{d,0},\mathcal N_{d,1})\)
    and ordered basis
    \((B_{1,0},B_{1,1},\ldots,B_{d,0},B_{d,1})\) is the identity.

    For

    \[
    H_\gamma^{\rm raw}=-\frac12P QD_\gamma,
    \]

    one has

    \[
    H_\gamma^{\rm raw}(p_k)=0,
    \]

    and

    \[
    (H_\gamma^{\rm raw})'(p_k)
    =
    -\frac12P(p_k)Q'(p_k)D_\gamma(p_k).
    \]

    Therefore in this concrete chart

    \[
    \boxed{
    H_\gamma^{\rm corr}(z)
    =
    -\frac12
    \sum_{k=1}^d
    P(p_k)Q'(p_k)D_\gamma(p_k)\,B_{k,1}(z),
    }
    \tag{FixedQCorr}
    \]

    and

    \[
    \boxed{
    H_\gamma(z)
    =
    -\frac12P(z)Q(z)D_\gamma(z)
    +
    \frac12
    \sum_{k=1}^d
    P(p_k)Q'(p_k)D_\gamma(p_k)\,B_{k,1}(z).
    }
    \tag{FixedQEndpointSeed}
    \]

    By construction \(H_\gamma(p_k)=H_\gamma'(p_k)=0\) for every \(k\), so
    \(C_\gamma=H_\gamma/(Q^2R)\) has no off-cut pole at any \(p_k\).  This is
    the explicit normalized endpoint seed used in the fixed-\(Q\) free-period
    rank-defect table.  If \(d=0\), the correction sum is empty and
    \(H_\gamma=-\frac12PQD_\gamma\).

    Endpoint-column simplification.

    The endpoint columns simplify further.  Since \(g=2\), the finite-gap
    decay condition gives

    \[
    \deg P\le d-3.
    \]

    Hence

    \[
    \deg H_\gamma^{\rm raw}
    =
    \deg(PQD_\gamma)\le (d-3)+d+3=2d,
    \]

    while \(Q^2R\) has degree \(2d+2\) at infinity.  Therefore

    \[
    \frac{H_\gamma^{\rm raw}}{Q^2R}=O(z^{-2}).
    \]

    The Hermite correction terms \(B_{k,1}\) have degree at most \(2d-1\), so

    \[
    \frac{B_{k,1}}{Q^2R}=O(z^{-3}).
    \]

    Thus

    \[
    \boxed{
    R_0(G_\gamma)=[z^{-1}]_\infty C_\gamma=0.
    }
    \tag{EndpointMassZero}
    \]

    The branch equality row is consequently

    \[
    \boxed{
    R_c(G_\gamma)=-C_\gamma(c)
    =
    -\frac{H_\gamma(c)}{Q(c)^2R(c)}.
    }
    \tag{EndpointRc}
    \]

    Since the endpoint seed has zero total mass, its logarithmic potential is
    normalized by \(V_\gamma(\infty)=0\).  For \(s\notin J\),

    \[
    V_\gamma'(s)=-C_\gamma(s),
    \]

    hence, along the real gap component not crossing \(J\),

    \[
    \boxed{
    V_\gamma(s)=\int_s^\infty C_\gamma(y)\,dy.
    }
    \tag{EndpointPotential}
    \]

    In particular,

    \[
    \boxed{
    b_\gamma
    =
    a\int_u^\infty C_\gamma(y)\,dy
    +
    b\int_v^\infty C_\gamma(y)\,dy.
    }
    \tag{EndpointBoundaryEntry}
    \]

    For the \(Z_0\)-function, write

    \[
    e_2=\binom01,\qquad
    A_c(x)=
    (U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}e_2.
    \]

    Since

    \[
    E_\gamma=\binom{0}{-C_\gamma(c)},
    \]

    the equality-corrected endpoint column is

    \[
    \boxed{
    f_\gamma(x)=V_\gamma(x)+C_\gamma(c)A_c(x),
    \qquad x\in Z_0.
    }
    \tag{EndpointZColumn}
    \]

    Therefore the endpoint part of the reduced Schiffer table is the closed
    formula

    \[
    \boxed{
    \begin{aligned}
    C_\gamma(z)&=\frac{H_\gamma(z)}{Q(z)^2R(z)},\\
    E_\gamma&=\binom{0}{-C_\gamma(c)},\\
    b_\gamma&=
    a\int_u^\infty C_\gamma(y)\,dy+
    b\int_v^\infty C_\gamma(y)\,dy,\\
    f_\gamma(x)&=V_\gamma(x)+C_\gamma(c)A_c(x).
    \end{aligned}
    }
    \tag{EndpointReducedColumn}
    \]

    The period column in the same free-period fixed-\(Q\) chart is chosen as

    \[
    \boxed{
    H_\Pi(z)=\kappa Q(z)^2,\qquad
    C_\Pi(z)=\frac{\kappa}{R(z)}.
    }
    \tag{PeriodTransferColumn}
    \]

    The real scalar \(\kappa\ne0\) is chosen with the sign convention that the
    associated boundary density has the oriented positive period-transfer form

    \[
    G_\Pi=\sigma h_\Pi,\qquad h_\Pi>0.
    \]

    If the branch convention reverses \(\sigma\), replace \(\kappa\) by
    \(-\kappa\).  Since \(R(z)\sim z^2\),

    \[
    C_\Pi(z)=O(z^{-2}),
    \]

    and hence

    \[
    \boxed{
    R_0(G_\Pi)=0,\qquad
    R_c(G_\Pi)=-C_\Pi(c)=-\frac{\kappa}{R(c)}.
    }
    \tag{PeriodRows}
    \]

    Normalize \(V_\Pi(\infty)=0\).  Then

    \[
    \boxed{
    V_\Pi(s)=\int_s^\infty C_\Pi(y)\,dy
    =
    \kappa\int_s^\infty\frac{dy}{R(y)}.
    }
    \tag{PeriodPotential}
    \]

    Therefore

    \[
    E_\Pi=\binom{0}{-C_\Pi(c)},
    \]

    \[
    b_\Pi=aV_\Pi(u)+bV_\Pi(v),
    \qquad
    f_\Pi(x)=V_\Pi(x)
    -(U_{\psi_1}(x),U_{\psi_2}(x))M^{-1}E_\Pi.
    \tag{PeriodReducedColumn}
    \]

    Thus both endpoint and period columns are explicit up to the single
    orientation scale \(\kappa\).  Multiplying \(\kappa\) by a positive scalar
    only rescales the fixed period-transfer seed column and does not change the
    sign test.

    Removing the bump potential from the circuit test.

    Define, for every seed \(j\in\{\Pi,\alpha_1,\beta_1,\alpha_2,\beta_2\}\),

    \[
    \rho_j:=R_c(G_j)=-C_j(c).
    \]

    Since all five seed columns above have zero mass row, the equality
    correction has the uniform form

    \[
    \boxed{
    f_j(x)=V_j(x)-\rho_jA_c(x).
    }
    \tag{UniformCorrectedColumn}
    \]

    Let

    \[
    V_S(x)=
    \begin{pmatrix}
    V_{\alpha_1}(x)\\
    V_{\beta_1}(x)\\
    V_{\alpha_2}(x)\\
    V_{\beta_2}(x)
    \end{pmatrix},
    \qquad
    \rho_S=
    \begin{pmatrix}
    \rho_{\alpha_1}\\
    \rho_{\beta_1}\\
    \rho_{\alpha_2}\\
    \rho_{\beta_2}
    \end{pmatrix}.
    \]

    If a corrected positive circuit exists, then for some
    \(\eta\ge0\), \(w_k>0\), and \(x_k\in Z_0\),

    \[
    \eta b+\sum_k w_k\bigl(V_S(x_k)-\rho_SA_c(x_k)\bigr)=0.
    \]

    With

    \[
    \lambda:=\sum_k w_kA_c(x_k),
    \]

    this is equivalent to the raw augmented relation

    \[
    \boxed{
    \eta b+\sum_k w_kV_S(x_k)-\lambda\rho_S=0.
    }
    \tag{RawCircuit}
    \]

    The corresponding lifted value is

    \[
    \boxed{
    \eta b_\Pi+\sum_k w_kV_\Pi(x_k)-\lambda\rho_\Pi.
    }
    \tag{RawLift}
    \]

    Hence it is sufficient, and independent of the auxiliary bumps
    \(\psi_1,\psi_2\), to prove the stronger raw test: every relation
    (RawCircuit), for arbitrary real \(\lambda\) and positive circuit weights,
    has raw lifted value (RawLift) strictly negative.  This stronger statement
    implies the corrected positive-circuit negativity because every corrected
    circuit supplies such a real \(\lambda\).

    In determinant form, the four-point case uses the \(4\times4\) matrix with
    columns \(V_S(x_i)-\rho_SA_c(x_i)\), or equivalently the augmented raw
    relation (RawCircuit).  The five-point case is the same with
    \(\eta=0\).  Degenerate determinants again reduce to smaller support
    circuits or to the pinching/positivity-boundary routing.

    Raw augmented circuit sign proof checkpoint.

    The determinant sign theorem needed here is the following statement.

    \[
    \boxed{\textbf{RawAugmentedCircuitSign}}
    \]

    For every finite family \(x_k\in Z_0\), weights \(w_k>0\),
    \(\eta\ge0\), and arbitrary real \(\lambda\), if

    \[
    \eta b+\sum_k w_kV_S(x_k)-\lambda\rho_S=0,
    \tag{RAC}
    \]

    then

    \[
    \boxed{
    \eta b_\Pi+\sum_k w_kV_\Pi(x_k)-\lambda\rho_\Pi<0.
    }
    \tag{RAS}
    \]

    This is stronger than the corrected circuit sign test because every
    corrected circuit produces a real number
    \(\lambda=\sum_k w_kA_c(x_k)\).  Hence
    `RawAugmentedCircuitSign` would remove the arbitrary equality-correction
    potential \(A_c\) from the proof.

    In raw variables the relevant extended family is

    \[
    \mathcal T
    =
    \left(
    V_{\alpha_1},V_{\beta_1},V_{\alpha_2},V_{\beta_2},-\rho
    \right),
    \qquad
    \text{lift }V_\Pi.
    \tag{Traw}
    \]

    Thus the desired sign theorem is an extended Chebyshev/oriented-circuit
    statement: every positive circuit in the first four coordinates of
    \(\mathcal T\), with the fifth direction \(-\rho\) allowed with arbitrary
    signed coefficient \(\lambda\), has negative \(V_\Pi\)-lift.

    The determinant forms are as follows.

    * If \(\eta>0\), normalize \(\eta=1\).  For a minimal support
      \(X=(x_1,\ldots,x_N)\subset Z_0\), the raw relation is

      \[
      [\,V_S(x_1)\ \cdots\ V_S(x_N)\ -\rho_S\,]
      \binom{w}{\lambda}
      =
      -b,
      \qquad
      w_i>0.
      \tag{RAC4}
      \]

      Since the signed \(\rho_S\)-column is present, the minimal-support
      determinant cases are not identical to the corrected four-point test:
      when \(N=3\) and the displayed \(4\times4\) matrix is invertible, the
      coefficients are forced; when \(N=4\), there is a one-dimensional affine
      family and only its positive circuit endpoints need be checked.  The
      required lifted sign is

      \[
      b_\Pi+\sum_{i=1}^{N}w_iV_\Pi(x_i)-\lambda\rho_\Pi<0.
      \tag{RAC4lift}
      \]

    * If \(\eta=0\), the raw relation is

      \[
      [\,V_S(x_1)\ \cdots\ V_S(x_N)\ -\rho_S\,]
      \binom{w}{\lambda}
      =
      0,
      \qquad
      w_i>0,
      \tag{RAC5}
      \]

      with minimal support \(N\le5\).  The required lifted sign is

      \[
      \sum_{i=1}^{N}w_iV_\Pi(x_i)-\lambda\rho_\Pi<0.
      \tag{RAC5lift}
      \]

      Degenerate determinants either reduce to smaller support circuits or
      route to pinching / positivity-boundary / lower-genus degeneration.

    Differentiating these determinants gives the correct analytic target.
    For every seed \(j\),

    \[
    V_j'(x)=-C_j(x),
    \qquad
    C_\Pi(x)=\frac{\kappa}{R(x)},\qquad
    C_\gamma(x)=\frac{H_\gamma(x)}{Q(x)^2R(x)}.
    \tag{Cseed}
    \]

    After multiplication by the common denominator \(Q(x)^2R(x)\), the
    differentiated endpoint columns are the fixed-\(Q\) Hermite-normalized
    numerators \(H_\gamma\), while the period column is \(\kappa Q^2\).  A
    successful sign proof must therefore establish a two-cut strict
    Chebyshev/variation-diminishing theorem for these integrated Schiffer
    potentials together with the constant equality row \(-\rho\).

    The existing six-kernel determinant in Section 9.10 does not prove this
    theorem.  It proves the oriented strict Chebyshev property for the local
    jet kernels

    \[
    1,\quad (x-u)^{-1},\quad (x-c)^{-1},\quad (x-v)^{-1},\quad L_-,\quad L_+,
    \]

    but the raw augmented family \(\mathcal T\) consists of integrated
    fixed-\(Q\) Schiffer potentials and the equality row \(\rho_j=-C_j(c)\).
    The differentiation step reduces the problem to rational/Cauchy columns,
    but no signed determinant identity has yet been proved for the
    Hermite-corrected numerators \(H_\gamma\) and the period numerator
    \(\kappa Q^2\).  Consequently the rank-defect proof remains incomplete until
    `RawAugmentedCircuitSign` is proved.

    Formal proof attempt for the missing sign.

    The natural lemma one would need is:

    \[
    \boxed{\textbf{AugmentedSchifferChebyshevLemma}}
    \]

    In the free-period fixed-\(Q\) regular non-pinched chart, with

    \[
    C_\Pi=\frac{\kappa}{R},\qquad
    C_\gamma=\frac{H_\gamma}{Q^2R},\qquad
    \rho_j=-C_j(c),
    \]

    the raw augmented family

    \[
    (V_{\alpha_1},V_{\beta_1},V_{\alpha_2},V_{\beta_2},-\rho)
    \]

    has the oriented circuit property (RAS) with lift \(V_\Pi\) on \(Z_0\).

    Differentiating any nondegenerate determinant in one moving point gives a
    row whose variable entries are

    \[
    -C_{\alpha_1}(x),\quad
    -C_{\beta_1}(x),\quad
    -C_{\alpha_2}(x),\quad
    -C_{\beta_2}(x),\quad 0,
    \qquad
    \text{lift derivative }-C_\Pi(x).
    \]

    After multiplying that row by the common denominator \(Q(x)^2R(x)\), the
    endpoint entries become

    \[
    -H_{\alpha_1}(x),\quad
    -H_{\beta_1}(x),\quad
    -H_{\alpha_2}(x),\quad
    -H_{\beta_2}(x),
    \]

    and the lifted derivative becomes

    \[
    -\kappa Q(x)^2.
    \]

    This is the exact Cauchy/rational determinant to sign.  The branch of
    \(R\) only contributes the oriented sign already fixed by the convention
    for \(G_\Pi=\sigma h_\Pi\), and \(Q\)-zeros do not cross
    \(J\cup\{u,c,v\}\) in the regular non-pinched chart.  Thus no hidden
    period-row or mass-row term remains: all seed columns have \(R_0=0\), and
    \(f_j=V_j-\rho_jA_c\) has already been converted to the raw augmented
    relation with arbitrary real \(\lambda\).

    The obstruction is now sharp.  To finish the proof, one must prove that the
    Hermite-normalized polynomial columns

    \[
    H_{\alpha_1},\ H_{\beta_1},\ H_{\alpha_2},\ H_{\beta_2},\ \kappa Q^2
    \]

    have the required two-cut oriented determinant sign after the fixed
    \(Q^2R\) denominator is removed.  This does not follow from the six-kernel
    Chebyshev determinant, because the six-kernel theorem signs the local jet
    span, while the present columns contain global Hermite pole-cancellation
    corrections

    \[
    \frac12\sum_kP(p_k)Q'(p_k)D_\gamma(p_k)B_{k,1}(z).
    \]

    Those correction terms are not a positive Cauchy average of the six local
    kernels in the earlier fixed-\(Q\) audit.  This was the old obstruction.
    The later Gate 1 audit replaces the collapsed fixed-\(Q\) endpoint table
    by repaired moving Schiffer columns, but the determinant-orientation route
    still fails; the proof-grade continuation is the \(Q_{\rm eff}\) and
    cone-envelope analysis below.

    Collapse audit of the fixed-\(Q\) endpoint columns.

    There is an even sharper obstruction in the current fixed-\(Q\) endpoint
    table.  Let \(d=\deg Q\).  In the \(g=2\) Cauchy-transform normalization
    used above,

    \[
    \deg P=d-3,\qquad \deg D_\gamma=3,
    \]

    hence

    \[
    \deg H_\gamma^{\rm raw}
    =
    \deg(PQD_\gamma)
    \le 2d.
    \]

    The Hermite correction terms \(B_{k,1}\) have degree at most \(2d-1\), so
    the normalized numerator also has

    \[
    \deg H_\gamma\le 2d.
    \]

    But the normalization imposes

    \[
    H_\gamma(p_k)=H_\gamma'(p_k)=0
    \qquad(k=1,\ldots,d).
    \]

    Since the \(p_k\) are simple zeros of \(Q\), this gives

    \[
    Q^2\mid H_\gamma.
    \]

    Therefore

    \[
    H_\gamma=q_\gamma Q^2
    \]

    with \(q_\gamma\) constant.  The leading coefficient of \(H_\gamma\) is the
    leading coefficient of \(H_\gamma^{\rm raw}\), because the Hermite
    correction has lower degree.  Since \(D_\gamma\) is monic for every branch
    endpoint \(\gamma\),

    \[
    q_\gamma=-\frac12\,\operatorname{lc}(P)\operatorname{lc}(Q)
    \]

    is independent of \(\gamma\).  With the monic convention
    \(Q(z)=\prod_k(z-p_k)\), this is

    \[
    \boxed{
    H_{\alpha_1}=H_{\beta_1}=H_{\alpha_2}=H_{\beta_2}
    =
    -\frac12\,\operatorname{lc}(P)\,Q^2.
    }
    \tag{EndpointCollapse}
    \]

    Thus the current fixed-\(Q\) Hermite-normalized endpoint columns satisfy

    \[
    C_{\alpha_1}=C_{\beta_1}=C_{\alpha_2}=C_{\beta_2}
    =
    -\frac12\,\operatorname{lc}(P)\frac1R,
    \]

    so they are all proportional to the period column \(C_\Pi=\kappa/R\).
    Consequently the four endpoint Schiffer columns in the present table do not
    form a four-dimensional correction space.  The raw augmented determinant
    test is therefore not merely unproved; with these columns it is degenerate.

    Repaired endpoint Schiffer table.

    The repair is to stop using the fixed-\(P\), fixed-\(Q\) pole-cancellation
    table as the endpoint seed table.  The endpoint seed must be defined from
    the full Schiffer variation

    \[
    \boxed{
    \delta_\gamma F(z)
    =
    \frac{\Delta_\gamma P(z)}{Q(z)}R(z)
    -\frac{P(z)R(z)}{2Q(z)(z-\gamma)}
    -\frac{P(z)R(z)}{Q(z)^2}\Delta_\gamma Q(z).
    }
    \tag{FullSchifferSeed}
    \]

    Equivalently, in the common denominator \(Q^2R\),

    \[
    \boxed{
    H_\gamma^{\rm rep}
    =
    QD\,\Delta_\gamma P
    -PD\,\Delta_\gamma Q
    -\frac12PQD_\gamma,
    \qquad
    C_\gamma^{\rm rep}
    =
    \frac{H_\gamma^{\rm rep}}{Q^2R}.
    }
    \tag{RepairedEndpointH}
    \]

    The unknown pair

    \[
    (\Delta_\gamma P,\Delta_\gamma Q)\in\mathcal X_{\rm Sch}
    \]

    is determined by a finite moving-chart normalization system

    \[
    \boxed{
    \mathcal L_{\rm Sch}(\Delta_\gamma P,\Delta_\gamma Q)
    =
    -\mathcal L_{\rm Sch}
    \left(0,0;-\frac12PQD_\gamma\right).
    }
    \tag{SchifferLinearSystem}
    \]

    Here \(\mathcal L_{\rm Sch}\) contains exactly the chart rows that must be
    fixed for a regular endpoint Schiffer direction: zero mass, the selected
    free-period/filling convention, the moving-pole gauge for \(Q\), the
    prescribed residue/pole-state convention, and the regularity rows needed to
    keep the finite-\(\varepsilon\) perturbation in the separated non-pinched
    chart.  It does not include \(R_c\), because \(R_c\) is still corrected by
    the boundary-neutral bump pair.  It also does not impose the collapsed
    fixed-\(Q\) conditions \(H(p_k)=H'(p_k)=0\) unless those rows are part of a
    larger moving-\(Q\) system with enough numerator/pole-state freedom to avoid
    (EndpointCollapse).

    With this repaired definition,

    \[
    R_0(G_\gamma)=0,
    \qquad
    \rho_\gamma=R_c(G_\gamma)=-C_\gamma^{\rm rep}(c),
    \]

    and

    \[
    V_\gamma(s)=\int_s^\infty C_\gamma^{\rm rep}(y)\,dy
    \qquad(s\notin J)
    \]

    with the usual continuous logarithmic boundary value on \(Z_0\).  The
    reduced endpoint column is therefore

    \[
    \boxed{
    b_\gamma=aV_\gamma(u)+bV_\gamma(v),
    \qquad
    f_\gamma(x)=V_\gamma(x)-\rho_\gamma A_c(x).
    }
    \tag{RepairedEndpointColumn}
    \]

    The noncollapse condition for the repaired table is now explicit:

    \[
    \boxed{
    \operatorname{rank}
    \left[
    C_{\alpha_1}^{\rm rep},\
    C_{\beta_1}^{\rm rep},\
    C_{\alpha_2}^{\rm rep},\
    C_{\beta_2}^{\rm rep}
    \right]
    \equiv 4
    \quad
    \text{modulo the period column }C_\Pi.
    }
    \tag{RepairedSchifferRank}
    \]

    This is the repaired endpoint table to use in Gate 1.  The old
    fixed-\(Q\) Hermite table is retained only as a failed audit showing why the
    numerator/pole-state part of the Schiffer variation is necessary.

    Repaired rank check.

    The rank condition (RepairedSchifferRank) is now part of the regular moving
    Schiffer chart.  More explicitly, let

    \[
    \mathcal J_{\rm Sch}:
    (\dot\alpha_1,\dot\beta_1,\dot\alpha_2,\dot\beta_2,\dot\tau)
    \longmapsto
    \sum_\gamma \dot\gamma\,C_\gamma^{\rm rep}
    +\dot\tau\,C_\Pi
    \]

    be the differential of the repaired finite-gap chart after the rows in
    \(\mathcal L_{\rm Sch}\) have been imposed.  A regular non-pinched
    endpoint chart means exactly that \(\mathcal J_{\rm Sch}\) is injective on
    these five coordinate directions.  Therefore

    \[
    \sum_\gamma a_\gamma C_\gamma^{\rm rep}\in \operatorname{span}\{C_\Pi\}
    \quad\Longrightarrow\quad
    a_{\alpha_1}=a_{\beta_1}=a_{\alpha_2}=a_{\beta_2}=0.
    \]

    Hence (RepairedSchifferRank) passes in the regular moving Schiffer chart.
    If this injectivity fails, the base point is not a regular non-pinched
    chart point: it is a chart-rank degeneration and is routed to the
    pinching/boundary/lower-genus branch rather than to the rank-defect
    interior case.

    Gate 1 subcheck status before the sign proof.

    \[
    \boxed{
    \textbf{Rank subcheck: PASS.}\quad
    \text{Endpoint columns do not collapse in the regular moving chart.}
    }
    \]

    The failure is not in the \(A_c\)-elimination, the period column, the
    zero-mass row, or the raw circuit algebra.  Those parts are fixed.  The
    repaired table removes the fixed-\(Q\) endpoint-column collapse and the
    rank subcheck passes by regular chart injectivity.  The remaining work in
    this subsection is to prove `AugmentedSchifferChebyshevLemma`, i.e. (RAS).

    Why the rank subcheck alone did not close Gate 1.

    The repaired rank check is necessary, but it is not the raw augmented
    circuit sign.  Rank is a linear independence statement; (RAS) is an
    oriented cone statement.  These are different assertions.

    A minimal finite-dimensional model shows the gap.  Take

    \[
    F(x_i)=e_i\in\mathbb R^4,\qquad
    b=-(1,1,1,1).
    \]

    Then the four endpoint columns are full rank and

    \[
    b+\sum_{i=1}^4F(x_i)=0
    \]

    is a positive circuit.  If the lifted values are

    \[
    \tau_*=1,\qquad \tau(x_i)=0,
    \]

    then the lifted circuit value is \(1\ge0\), so the reduced LP is blocked.
    If instead \(\tau_*=-1\), the same rank data gives a negative lifted value.
    Thus the rank condition alone contains no information about the sign of
    the positive circuit lift.

    Consequently the way to close Gate 1 is to prove an additional
    total-positivity / Chebyshev orientation statement for the actual repaired
    Schiffer columns.  In the present notation this means an explicit
    determinant identity for

    \[
    H_{\alpha_1}^{\rm rep},\ H_{\beta_1}^{\rm rep},\
    H_{\alpha_2}^{\rm rep},\ H_{\beta_2}^{\rm rep},\ \kappa Q^2,
    \]

    with the equality row \(\rho_j=-C_j^{\rm rep}(c)\).  The current document
    defines these repaired columns only through the abstract moving-chart
    system \(\mathcal L_{\rm Sch}\).  Until that system is written explicitly
    and its determinants are signed, (RAS) is not a consequence of the existing
    hypotheses.

    Explicit moving Schiffer chart for Gate 1.

    The fixed-\(Q\) Hermite endpoint table above is no longer a proof-grade
    table; it is only the failed audit that shows why endpoint columns
    collapse if the numerator and pole-state variables are frozen.  The
    proof-grade endpoint column is the moving-chart column

    \[
    H_\gamma^{\rm rep}
    =
    QD\,\Delta_\gamma P
    -PD\,\Delta_\gamma Q
    -\frac12PQD_\gamma.
    \]

    Choose real bases \(E_1,\ldots,E_m\) for the allowed
    \(\Delta P\)-space and \(F_1,\ldots,F_n\) for the allowed
    \(\Delta Q\)-space.  Write

    \[
    \Delta_\gamma P=\sum_{i=1}^m x_{\gamma,i}E_i,
    \qquad
    \Delta_\gamma Q=\sum_{j=1}^n y_{\gamma,j}F_j,
    \qquad
    X_\gamma=(x_{\gamma,1},\ldots,x_{\gamma,m},
    y_{\gamma,1},\ldots,y_{\gamma,n})^T.
    \]

    Let \(B\) be the linear map from coefficients \(X\) to the numerator

    \[
    B X
    =
    QD\,\Delta P_X-PD\,\Delta Q_X.
    \]

    Let \(\ell_1,\ldots,\ell_{m+n}\) be the independent moving-chart rows:
    zero mass, the selected free-period/filling convention, the moving-\(Q\)
    gauge, pole/residue-state rows, and the regular chart rows.  The branch row
    \(R_c\) is not included, because it is corrected by the boundary-neutral
    bump pair.  Put

    \[
    A_{ri}:=\ell_r(B e_i),
    \qquad
    (r_\gamma)_r:=\ell_r\!\left(-\frac12PQD_\gamma\right).
    \]

    The endpoint correction is therefore the explicit finite system

    \[
    \boxed{
    AX_\gamma=-r_\gamma.
    }
    \tag{Gate1MatrixSchiffer}
    \]

    If \(A\) is singular, the point is not a regular moving Schiffer chart
    point.  It is a chart-rank / pole-state degeneration and must be routed to
    pinching, boundary, or lower genus.  In the regular non-pinched interior
    case \(A\) is invertible and

    \[
    \boxed{
    H_\gamma^{\rm rep}
    =
    -\frac12PQD_\gamma
    -B A^{-1}r_\gamma.
    }
    \tag{Gate1RepColumn}
    \]

    This is the first point where the previous abstraction is removed: every
    repaired endpoint column is now a Schur-complement column built from
    explicit rows \(\ell_r\), not an unspecified \(\mathcal L_{\rm Sch}\).

    Block determinant identity.

    Let \(L_1,\ldots,L_q\) be any evaluation/differentiated Cauchy rows used in
    a raw augmented determinant: rows at moving points \(x_i\), the endpoint
    boundary row \(b\), and the equality row \(\rho_j=-C_j^{\rm rep}(c)\).
    Applying \(L_s\) to (Gate1RepColumn) gives

    \[
    L_s(H_\gamma^{\rm rep})
    =
    L_s\!\left(-\frac12PQD_\gamma\right)
    -
    L_sB\,A^{-1}r_\gamma.
    \]

    Hence every determinant whose endpoint columns are
    \(H_\gamma^{\rm rep}\) is a Schur complement.  In matrix form,

    \[
    \boxed{
    \det L(H_{\Gamma}^{\rm rep})
    =
    \frac{
    \det
    \begin{pmatrix}
    A & r_\Gamma\\
    LB & L(H_\Gamma^{\rm raw})
    \end{pmatrix}}
    {\det A},
    }
    \tag{Gate1BlockDet}
    \]

    up to the fixed sign determined by the chosen column order.  Here
    \(H_\Gamma^{\rm raw}=(-\frac12PQD_{\alpha_1},-\frac12PQD_{\beta_1},
    -\frac12PQD_{\alpha_2},-\frac12PQD_{\beta_2})\).  The period lift
    contributes the extra column \(\kappa Q^2\), and the equality row is the
    evaluation row \(H\mapsto -H(c)/(Q(c)^2R(c))\).  Thus any Gate 1 sign proof
    must sign the block determinant (Gate1BlockDet), not merely the endpoint
    rank matrix.

    Attempted AugmentedSchifferChebyshevLemma.

    Differentiating a nondegenerate raw augmented circuit determinant in a
    moving point uses

    \[
    V_j'(x)=-C_j(x).
    \]

    Multiplication of the differentiated row by \(Q(x)^2R(x)\) changes the
    endpoint entries into

    \[
    -H_{\alpha_1}^{\rm rep}(x),\quad
    -H_{\beta_1}^{\rm rep}(x),\quad
    -H_{\alpha_2}^{\rm rep}(x),\quad
    -H_{\beta_2}^{\rm rep}(x),
    \]

    while the period lift becomes \(-\kappa Q(x)^2\).  Substituting
    (Gate1BlockDet) would reduce the desired sign to a confluent Cauchy
    determinant involving the moving rows \(x_i\), the normalization rows
    \(\ell_r\), the branch endpoint rows, and the real pole/residue rows.

    The first of the two missing inputs can be closed.  Since the regular
    finite-gap transform is the Cauchy transform of a positive dual measure,
    every pole of \(F\) off the cuts is an atom of that positive measure.
    Therefore the \(Q\)-poles are real, simple in the regular chart, and have
    positive residues.  On each complementary real interval,

    \[
    F'(x)=-\int\frac{d\lambda(t)}{(x-t)^2}<0,
    \]

    so \(F\) is strictly decreasing between consecutive support points.
    Hence each complementary interval contains at most one zero, and the
    zeros, branch endpoints, and real poles interlace in the usual Stieltjes
    order.  If a pole is non-real, multiple, has zero/negative residue, or
    collides with a branch endpoint, the point is not a regular positive
    non-pinched chart point and is routed to boundary/lower genus.

    Thus

    \[
    \boxed{
    \text{real separated/interlaced }Q\text{-poles: PASS in the regular positive chart.}
    }
    \tag{Gate1QPoles}
    \]

    Schur-block orientation audit.

    The moving-chart construction above repairs the fixed-\(Q\) collapse and
    gives the necessary rank subcheck: the endpoint Schiffer columns need not
    be proportional to the period column in a regular moving chart.  This is
    not yet the same as the sign theorem needed for rank-defect exclusion.
    Full rank only says the endpoint columns span the required directions; it
    does not determine the lifted sign of every positive circuit.

    The missing proof-grade statement is the following independent lemma.

    \[
    \boxed{
    \textbf{SchurBlockTotalPositivityLemma.}
    }
    \]

    In a regular positive moving Schiffer chart, with repaired columns
    \(H_\gamma^{\rm rep}=H_\gamma^{\rm raw}+BA^{-1}r_\gamma\), one must prove
    that every raw augmented circuit

    \[
    \eta b+\sum_iw_iV_S(x_i)-\lambda\rho_S=0,\qquad
    \eta\ge0,\quad w_i>0,
    \]

    has the negative lifted orientation

    \[
    \eta b_\Pi+\sum_iw_iV_\Pi(x_i)-\lambda\rho_\Pi<0.
    \tag{RAS}
    \]

    The current ledger has the correct formal Schur-complement identity,

    \[
    \det L(H_\Gamma^{\rm rep})
    =
    \frac{
    \det
    \begin{pmatrix}
    A&r_\Gamma\\
    LB&L(H_\Gamma^{\rm raw})
    \end{pmatrix}}
    {\det A},
    \tag{Gate1BlockDet}
    \]

    but this is not yet a determinant sign proof.  To close Gate 1, the
    numerator must be expanded as

    \[
    \det
    \begin{pmatrix}
    A&r_\Gamma\\
    LB&L(H_\Gamma^{\rm raw})
    \end{pmatrix}
    =
    (\text{positive row/column factors})
    \cdot
    (\text{explicit ordered Cauchy/Vandermonde product}),
    \tag{NeededSchurProduct}
    \]

    and every factor must be signed.  In particular, the proof must verify:

    - the moving-chart rows \(\ell_r\) are actual ordered real Cauchy or
      confluent Cauchy rows up to positive factors;
    - the free-period/filling convention is either quotiented out or is a
      positive average of those same ordered rows;
    - moving-\(Q\) gauge rows and pole/residue-state rows do not change the
      oriented circuit sign;
    - \(\det A>0\) is only an orientation convention, not by itself a proof of
      all augmented Schur minors.

    Therefore the rigorous status is:

    \[
    \boxed{
    \textbf{Gate 1 status: BLOCKED at SchurBlockTotalPositivityLemma.}
    }
    \tag{Gate1Blocked}
    \]

    What is currently proved is the reduction

    \[
    \boxed{
    \text{rank-defect }g=2
    \text{ reduced to the raw augmented circuit obstruction.}
    }
    \tag{Gate1ReductionOnly}
    \]

    The conditional implication remains valid:

    \[
    \boxed{
    \text{SchurBlockTotalPositivityLemma}
    \Rightarrow
    \text{RawAugmentedCircuitSign}
    \Rightarrow
    \text{reduced LP feasible.}
    }
    \tag{Gate1Conditional}
    \]

    Gate 1 no-go at the current level of hypotheses.

    The current hypotheses cannot be massaged into a proof of
    SchurBlockTotalPositivityLemma.  This is not just a missing paragraph; it
    is an algebraic underdetermination.

    The data currently proved for the repaired moving chart are:

    1. the endpoint columns are not collapsed modulo the period column;
    2. the normalization matrix \(A\) is invertible in the regular chart;
    3. the repaired columns are Schur-complement columns
       \(H_\gamma^{\rm rep}=H_\gamma^{\rm raw}-BA^{-1}r_\gamma\);
    4. the real \(Q\)-poles are separated/interlaced in a positive regular
       chart.

    None of these data determines the sign of an augmented positive circuit.
    A finite-dimensional model already shows the gap.  Let

    \[
    F(x_i)=e_i\in\mathbb R^4,\qquad b=-(1,1,1,1),\qquad
    \rho=0.
    \]

    Then

    \[
    b+\sum_{i=1}^4F(x_i)=0
    \]

    is a positive circuit and the endpoint block has full rank.  If the lifted
    values are

    \[
    \tau_*=1,\qquad \tau(x_i)=0,
    \]

    the lifted value is \(+1\).  If instead \(\tau_*=-1\), the same endpoint
    rank data gives lifted value \(-1\).  Thus rank and Schur-complement
    invertibility do not determine the sign.

    The same issue appears in determinant language.  The identity
    (Gate1BlockDet) is valid for every invertible \(A\).  But unless the rows
    \(\ell_r\), the pole-state gauge, and the evaluation rows are proved to be
    an ordered total-positive Cauchy/confluent Cauchy system with positive
    transition factors, the numerator determinant in (Gate1BlockDet) can have
    either sign under orientation-preserving changes of the unreduced row
    model.  The convention \(\det A>0\) fixes a basis orientation; it does not
    sign all augmented Schur minors.

    Therefore Gate 1 cannot be completed from the present assumptions.  The
    exact theorem still needed is stronger and more concrete:

    \[
    \boxed{
    \begin{gathered}
    \det
    \begin{pmatrix}
    A&r_\Gamma\\
    LB&L(H_\Gamma^{\rm raw})
    \end{pmatrix}
    =
    (\text{positive factors})
    \cdot
    (\text{explicit ordered Cauchy/Vandermonde product}),\\
    \text{with the product sign fixed for every admissible raw augmented
    circuit.}
    \end{gathered}
    }
    \tag{Gate1NeededTheorem}
    \]

    Until (Gate1NeededTheorem) is proved from an explicit moving Schiffer chart,
    the strongest honest Gate 1 result is the reduction to the raw augmented
    circuit obstruction, not rank-defect exclusion.

    Gate 1 decomposition after the no-go.

    The obstruction above is now split into one proved algebraic step and one
    remaining row-realization step.

    \[
    \boxed{\textbf{Lemma: sign-regular Schur complement transfer.}}
    \]

    Let

    \[
    \mathcal M=
    \begin{pmatrix}
    A&R\\
    B&C
    \end{pmatrix},
    \qquad
    S=C-BA^{-1}R,
    \qquad
    \det A>0.
    \]

    Suppose the rows and columns have been oriented so that every minor of
    \(\mathcal M\) obtained by adjoining the same fixed \(A\)-rows and
    \(A\)-columns to a raw augmented circuit row/column set has the prescribed
    strict sign.  Then the corresponding Schur-complement minor has that same
    sign.

    Indeed, for any row set \(I\) and column set \(J\) of equal size, Sylvester's
    determinant identity gives

    \[
    \boxed{
    \det S[I,J]
    =
    \frac{
    \det
    \begin{pmatrix}
    A&R_{\*,J}\\
    B_{I,\*}&C_{I,J}
    \end{pmatrix}}
    {\det A}.
    }
    \tag{Gate1Sylvester}
    \]

    Since \(\det A>0\), the Schur-complement minor has exactly the sign of the
    corresponding full block minor.  Therefore Gate 1 would be closed by the
    following concrete row-realization lemma:

    \[
    \boxed{\textbf{TPRowRealizationLemma.}}
    \]

    The actual moving-chart rows \(\ell_r\), the raw circuit evaluation rows,
    the equality row \(H\mapsto-H(c)/(Q(c)^2R(c))\), and the period lift
    \(\kappa Q^2\) form one ordered sign-regular Cauchy/confluent Cauchy block
    after multiplication by positive row and column factors.

    If TPRowRealizationLemma is proved, then (Gate1Sylvester) gives
    SchurBlockTotalPositivityLemma, hence RawAugmentedCircuitSign, hence
    reduced LP feasibility.  Conversely, without TPRowRealizationLemma the
    Schur complement identity alone contains no sign information.

    Thus the remaining Gate 1 task is now sharply localized:

    \[
    \boxed{
    \text{write the rows }\ell_r\text{ explicitly and prove
    TPRowRealizationLemma.}
    }
    \tag{Gate1RemainingRowRealization}
    \]

    This is narrower than the previous obstruction.  The algebraic transfer
    from a total-positive full block to the repaired endpoint Schur complement
    is proved by (Gate1Sylvester); only the realization of the actual
    moving-chart rows as such a total-positive block remains.

    TP row toolbox.

    The row-realization step can now be attacked row by row.  The following
    elementary facts are the permitted primitives.

    1.  Ordered Cauchy rows.  If the target nodes \(t_i\) and source nodes
        \(s_j\) are strictly ordered and separated, then

        \[
        \det\left(\frac1{t_i-s_j}\right)
        =
        \frac{
        \prod_{i<i'}(t_{i'}-t_i)
        \prod_{j<j'}(s_j-s_{j'})
        }{
        \prod_{i,j}(t_i-s_j)
        }
        \tag{Gate1CauchyProduct}
        \]

        has a fixed nonzero sign after the row and column order is fixed.

    2.  Confluent rows.  Evaluation-derivative rows at a real pole are obtained
        by differentiating (Gate1CauchyProduct) and taking a limit as source
        nodes coalesce.  The extra factors are fixed powers of ordered
        spacings and factorials, hence have fixed sign once the confluent row
        order is fixed.

    3.  Positive-average rows.  If a row is

        \[
        R_\mu(H)=\int R_t(H)\,d\mu(t),
        \qquad \mu\ge0,
        \]

        where each \(R_t\) is an ordered Cauchy row from a source interval that
        does not cross the other source nodes, then multilinearity and
        Fubini/Cauchy-Binet write any determinant containing \(R_\mu\) as an
        integral of determinants with the same oriented sign.  It is strict
        unless the averaged row is dependent on the other rows.

    Therefore the following rows are already compatible with the total-positive
    block, up to fixed positive row factors and fixed orientation signs:

    - moving point evaluation rows \(H\mapsto H(x_i)\);
    - the equality row \(H\mapsto-H(c)/(Q(c)^2R(c))\), since \(c\) is a fixed
      ordered real evaluation node away from \(J\) and the poles;
    - pole-state rows \(H\mapsto H(p_k)\) and
      \(H\mapsto H'(p_k)\), provided the \(Q\)-poles are real, simple,
      separated, and ordered;
    - the zero-mass row, interpreted as the evaluation row at infinity after
      the \(w=1/z\) change of variables;
    - any retained period/filling row that is explicitly written as a positive
      average of ordered real Cauchy rows.

    This proves the row-realization lemma for the canonical subchart whose
    normalization rows consist only of the rows in the list above.  The
    remaining possible obstruction is no longer algebraic; it is whether the
    actual moving Schiffer chart uses any additional "regular chart rows" or
    sign-changing period rows outside this canonical TP row class.

    Thus the next and final Gate 1 checklist is:

    \[
    \boxed{
    \begin{array}{c|c}
    \text{row type} & \text{Gate 1 status}\\ \hline
    \text{zero mass} & \text{TP row: proved}\\
    \text{pole / residue state} & \text{TP confluent row if poles are real simple}\\
    \text{equality row } \rho & \text{TP evaluation row: proved}\\
    \text{moving point rows} & \text{TP evaluation rows: proved}\\
    \text{period / filling row} & \text{needs positive-average formula}\\
    \text{regular chart rows} & \text{must be replaced by canonical TP gauge or proved TP}
    \end{array}
    }
    \tag{Gate1RowChecklist}
    \]

    Once the period/filling row and any remaining regular chart rows are shown
    to be in the canonical TP class, TPRowRealizationLemma follows from the
    three primitives above, and Gate 1 passes by (Gate1Sylvester).

    Canonical free-period row realization.

    The two unresolved rows in (Gate1RowChecklist) are not independent rows in
    the canonical Gate 1 chart.

    First, the period/filling constraint is treated in the free-period quotient
    used throughout the regular compact \(g=2\) audit.  The filling variable
    \(\tau\) supplies the period column, so the period multiplier is forced to
    vanish in any left-cokernel calculation.  Equivalently, the endpoint
    Schiffer normalization matrix \(A\) is built on the quotient by the period
    row; the period direction appears as the separate lift column
    \(C_\Pi=\kappa/R\), not as a normalization row that must be included in
    \(A\).  Thus no sign-changing fixed-period row is present in the canonical
    Gate 1 block.

    Second, the "regular chart rows" are not equality rows.  Separation of
    branch endpoints, real simple \(Q\)-poles, positive residues, and strict
    density signs are open inequalities defining the regular non-pinched
    chamber.  They are checked before the linearized Schiffer calculation and
    routed to Gate 3 when they fail.  They do not contribute rows to the
    finite equality matrix \(A\).

    Therefore the canonical Gate 1 normalization rows are exactly:

    \[
    \boxed{
    \text{zero-mass/infinity row}
    \quad+\quad
    \text{real pole-state evaluation/confluent derivative rows}.
    }
    \tag{Gate1CanonicalRows}
    \]

    These rows are already covered by the TP row toolbox: the infinity row is
    the Cauchy row at the ordered source \(\infty\), and the pole-state rows
    are ordered confluent Cauchy rows at the real simple poles \(p_k\).  The
    equality row \(\rho\) and all moving-point rows are also ordered evaluation
    rows.  Hence

    \[
    \boxed{
    \text{TPRowRealizationLemma holds for the canonical free-period
    pole-state Gate 1 row gauge.}
    }
    \tag{Gate1TPRowsPass}
    \]

    This closes the row side of Gate 1.  Combining (Gate1TPRowsPass) with
    (Gate1Sylvester), the repaired Schur-complement minors inherit the sign of
    the corresponding full canonical block minors.  The remaining determinant
    task is now purely column-side: prove that the full canonical block with
    raw endpoint columns

    \[
    H_\gamma^{\rm raw}=-\frac12PQD_\gamma
    \]

    and lift column \(\kappa Q^2\) has the required ordered sign once the
    canonical rows above are used.  This is the next lemma:

    \[
    \boxed{\textbf{EndpointPeriodColumnOrientationLemma.}}
    \]

    It must show that the four columns \(PQD_\gamma\) and the period column
    \(Q^2\), evaluated against the canonical ordered row block, have the
    required orientation.  Without this column-orientation lemma, row total
    positivity alone still does not prove RawAugmentedCircuitSign.

    Column-side audit.

    The column-side lemma cannot be checked from rows alone.  It depends on
    the correction column space \(B\) in

    \[
    H_\gamma^{\rm rep}=H_\gamma^{\rm raw}-BA^{-1}r_\gamma.
    \]

    This matters because the fixed-\(Q\) Hermite correction space is already
    known to fail: with only the Hermite pole-cancellation basis
    \(B_{k,0},B_{k,1}\), the normalized endpoint columns satisfy

    \[
    H_{\alpha_1}=H_{\beta_1}=H_{\alpha_2}=H_{\beta_2}
    =
    -\frac12\operatorname{lc}(P)Q^2,
    \]

    hence collapse onto the period column.  Thus the moving numerator/pole
    correction space must be used, and its columns must enter the sign proof.

    The final Gate 1 theorem is therefore the following more precise statement.

    \[
    \boxed{\textbf{MovingCorrectionColumnOrientationLemma.}}
    \]

    Let \(B_1,\ldots,B_N\) be the actual moving correction numerators

    \[
    B_\nu=QD\,\Delta P_\nu-PD\,\Delta Q_\nu
    \]

    used in the regular moving Schiffer chart.  Form the full canonical block

    \[
    \boxed{
    \mathcal M_{\rm mov}
    =
    \begin{pmatrix}
    A & r_{\alpha_1}&r_{\beta_1}&r_{\alpha_2}&r_{\beta_2}&r_\Pi\\
    LB&
    L(H_{\alpha_1}^{\rm raw})&
    L(H_{\beta_1}^{\rm raw})&
    L(H_{\alpha_2}^{\rm raw})&
    L(H_{\beta_2}^{\rm raw})&
    L(\kappa Q^2)
    \end{pmatrix}.
    }
    \tag{Gate1MovingBlock}
    \]

    Here \(A_{\mu\nu}=\ell_\mu(B_\nu)\), \(r_{\gamma,\mu}=\ell_\mu(H_\gamma^{\rm raw})\),
    and \(L\) ranges over the raw circuit rows: moving point evaluations,
    boundary row \(b\), and equality row \(\rho\).  The lemma must prove that
    every relevant minor of \(\mathcal M_{\rm mov}\) has the ordered sign
    needed for the lifted circuit inequality.

    If MovingCorrectionColumnOrientationLemma holds, then:

    \[
    \text{MovingCorrectionColumnOrientationLemma}
    \Rightarrow
    \text{SchurBlockTotalPositivityLemma}
    \Rightarrow
    \text{RawAugmentedCircuitSign}.
    \tag{Gate1FinalConditional}
    \]

    The endpoint-period column problem is therefore not a row-realization
    problem anymore.  It is a concrete finite determinant problem for the
    actual moving correction columns \(QD\Delta P-PD\Delta Q\).  The current
    text has not yet supplied those columns explicitly enough to sign
    \(\mathcal M_{\rm mov}\).  That is the last Gate 1 hard datum.

    Moving-column algebra audit.

    The natural moving correction image can be computed.  In the monic
    \(Q\)-chart,

    \[
    \deg \Delta P\le d-3,\qquad \deg \Delta Q\le d-1,
    \]

    and

    \[
    QD\Delta P-PD\Delta Q
    =
    D(Q\Delta P-P\Delta Q).
    \]

    Since \(\gcd(P,Q)=1\) in a regular chart, the map

    \[
    (\Delta P,\Delta Q)\longmapsto Q\Delta P-P\Delta Q
    \]

    from

    \[
    \mathbb R[z]_{\le d-3}\oplus\mathbb R[z]_{\le d-1}
    \]

    to \(\mathbb R[z]_{\le 2d-3}\) is an isomorphism.  Indeed, if
    \(Q\Delta P=P\Delta Q\), then \(Q\mid\Delta Q\), impossible for
    \(\deg\Delta Q\le d-1\) unless \(\Delta Q=0\), and then \(\Delta P=0\);
    the dimensions are both \(2d-2\).  Therefore the moving correction columns
    span exactly

    \[
    \boxed{
    D\cdot\mathbb R[z]_{\le 2d-3}.
    }
    \tag{Gate1CorrectionImage}
    \]

    Now consider the raw endpoint columns

    \[
    E_\gamma:=P QD_\gamma.
    \]

    At the branch endpoint \(\delta\),

    \[
    E_\gamma(\delta)=0\quad(\delta\ne\gamma),
    \qquad
    E_\gamma(\gamma)=P(\gamma)Q(\gamma)D_\gamma(\gamma).
    \]

    In the regular non-pinched chart these endpoint values are nonzero.  Hence
    for any polynomial \(F\in\mathbb R[z]_{\le 2d+1}\), choose

    \[
    a_\gamma=
    \frac{F(\gamma)}
    {P(\gamma)Q(\gamma)D_\gamma(\gamma)}.
    \]

    Then

    \[
    F-\sum_\gamma a_\gamma E_\gamma
    \]

    vanishes at all four branch endpoints, hence is divisible by \(D\); its
    quotient has degree at most \(2d-3\).  Thus

    \[
    \boxed{
    \mathbb R[z]_{\le 2d+1}
    =
    D\mathbb R[z]_{\le 2d-3}
    \oplus
    \operatorname{span}\{E_{\alpha_1},E_{\beta_1},E_{\alpha_2},E_{\beta_2}\}.
    }
    \tag{Gate1EndpointInterpolation}
    \]

    Since \(Q^2\in\mathbb R[z]_{\le 2d}\), the period numerator has the
    interpolation identity

    \[
    \boxed{
    Q^2
    =
    D W_Q
    +
    \sum_\gamma
    \frac{Q(\gamma)}
    {P(\gamma)D_\gamma(\gamma)}
    \,P QD_\gamma,
    \qquad
    W_Q\in\mathbb R[z]_{\le 2d-3}.
    }
    \tag{Gate1PeriodInterpolation}
    \]

    This identity is decisive.  Modulo the natural moving correction image
    \(D\mathbb R[z]_{\le 2d-3}\), the period lift column is already in the span
    of the four raw endpoint columns.  Therefore a pure first-order
    endpoint-period column-orientation determinant cannot be a nonzero
    full-block total-positive determinant in this natural moving quotient.

    The first-order Gate 1 route has consequently reached its algebraic limit:
    after the row side is closed, the column side shows that the period lift is
    an endpoint interpolation class modulo moving corrections.  Any remaining
    sign information is not contained in the first-order Schur block alone; it
    must come from the second variation / effective endpoint Hessian.

    The correct next Gate 1 replacement is therefore:

    \[
    \boxed{\textbf{EffectiveEndpointHessianLemma.}}
    \]

    It must compute the finite second-variation form on the endpoint
    interpolation quotient after the minimal moving correction has been
    eliminated.  In symbols, if \(P_{\rm ep}\) denotes the four endpoint
    interpolation columns and \(S\) is the energy-minimal lift of the row data,
    then the relevant matrix is

    \[
    \boxed{
    Q_{\rm eff}
    =
    P_{\rm ep}^{T}
    \bigl(B_{\rm loc}+C_{\log}^{-1}\bigr)
    P_{\rm ep},
    }
    \tag{Gate1Qeff}
    \]

    where \(B_{\rm loc}\) is the finite local branch Hessian and
    \(C_{\log}\) is the Feshbach/Riesz Gram matrix of the row representers for
    the zero-mass, free-period Hilbert space.  The rank-defect fallback is
    excluded only after proving that every nonnegative atomic Farkas
    certificate yields an endpoint direction \(h\) with

    \[
    h^TQ_{\rm eff}h<0.
    \tag{Gate1QeffNeg}
    \]

    This is now the proof-grade Gate 1 continuation.  The first-order
    RawAugmentedCircuitSign route is not closed by determinant orientation;
    it has been reduced to the second-variation Hessian calculation above.

    Gate 1 second-variation reduction.

    Gate 1 data dictionary.

    From this point onward, the fixed-\(Q\) Hermite endpoint table is used only
    as a collapse audit.  The proof-grade endpoint columns are the repaired
    moving-Schiffer columns.  We use the following uniform notation.

    \[
    \boxed{
    C_\Pi(z)=\frac{\kappa}{R(z)},\qquad
    C_\gamma(z)=\frac{H_\gamma^{\rm rep}(z)}{Q(z)^2R(z)}
    \quad
    \left(\gamma\in\{\alpha_1,\beta_1,\alpha_2,\beta_2\}\right).
    }
    \tag{G1DataC}
    \]

    The period orientation is chosen so that the period-transfer density has
    the positive orientation fixed earlier.  For every seed

    \[
    j\in\{\Pi,\alpha_1,\beta_1,\alpha_2,\beta_2\},
    \]

    define

    \[
    \boxed{
    \rho_j=R_c(G_j)=-C_j(c),
    \qquad
    V_j(s)=\int_s^\infty C_j(y)\,dy,
    }
    \tag{G1DataRhoV}
    \]

    with the real boundary value on the relevant component of
    \(\mathbb C\setminus J\).  The reduced boundary entry is

    \[
    \boxed{
    b_j=aV_j(u)+bV_j(v).
    }
    \tag{G1DataB}
    \]

    Finally set

    \[
    \boxed{
    V_S(x)=
    \begin{pmatrix}
    V_{\alpha_1}(x)\\
    V_{\beta_1}(x)\\
    V_{\alpha_2}(x)\\
    V_{\beta_2}(x)
    \end{pmatrix},
    \quad
    b_S=
    \begin{pmatrix}
    b_{\alpha_1}\\
    b_{\beta_1}\\
    b_{\alpha_2}\\
    b_{\beta_2}
    \end{pmatrix},
    \quad
    \rho_S=
    \begin{pmatrix}
    \rho_{\alpha_1}\\
    \rho_{\beta_1}\\
    \rho_{\alpha_2}\\
    \rho_{\beta_2}
    \end{pmatrix}.
    }
    \tag{G1DataVectors}
    \]

    Thus every later occurrence of \(b_S,\rho_S,V_S,V_\Pi,b_\Pi,\rho_\Pi\)
    refers to the repaired moving-chart data above, not to the collapsed
    fixed-\(Q\) endpoint table.

    We now record the exact implication that replaces the failed first-order
    sign theorem.  Let

    \[
    \mathfrak c=(\eta;\,w_1,x_1,\ldots,w_N,x_N;\lambda)
    \]

    be a minimal raw augmented atomic certificate, so

    \[
    \eta b_S+\sum_{k=1}^Nw_kV_S(x_k)-\lambda\rho_S=0
    \tag{G1certS}
    \]

    on the four endpoint Schiffer columns, with

    \[
    \eta\ge0,\qquad w_k>0,\qquad x_k\in Z_0.
    \]

    The corresponding period lift value is

    \[
    \Theta_\Pi(\mathfrak c)
    =
    \eta b_\Pi+\sum_{k=1}^Nw_kV_\Pi(x_k)-\lambda\rho_\Pi.
    \tag{G1certPi}
    \]

    In the first-order route one wanted to prove
    \(\Theta_\Pi(\mathfrak c)<0\).  The interpolation audit above shows that
    this sign is not a first-order column-orientation consequence.  Instead
    form the endpoint interpolation row vector

    \[
    r_{\mathfrak c}
    =
    \eta p_b+\sum_{k=1}^Nw_kp(x_k)-\lambda p_\rho
    \in V^\sharp,
    \tag{G1rc}
    \]

    where \(p_b,p(x),p_\rho\) are the row images of the boundary, point
    evaluation, and equality-anchor functionals in the endpoint interpolation
    quotient.  Minimality of the certificate means \(r_{\mathfrak c}\ne0\)
    unless the support reduces or one is already on a chart-rank / collision
    boundary.

    The replacement sign theorem is therefore:

    \[
    \boxed{\textbf{QeffNegativeCertificate.}}
    \]

    For every non-boundary minimal atomic certificate \(\mathfrak c\),

    \[
    \boxed{
    Q_{\rm eff}(r_{\mathfrak c},r_{\mathfrak c})<0.
    }
    \tag{G1QeffCert}
    \]

    This finite matrix statement is enough to exclude the rank-defect chamber.
    Indeed, assume the separated-chart minimal-lift theorem holds and let

    \[
    \xi_{\mathfrak c}=S r_{\mathfrak c}
    \]

    be the energy-minimal lift.  By construction,

    \[
    \rho^\sharp(\xi_{\mathfrak c})=r_{\mathfrak c},
    \qquad
    \xi_{\mathfrak c}\perp_{\mathcal E_{\log}}W^\sharp.
    \]

    The certificate equations (G1certS) make the first-order endpoint
    Schiffer components vanish in the four repaired endpoint directions; the
    boundary-neutral equality correction has already removed \(R_0,R_c\); and
    the period row is fixed in the free-period quotient.  Thus
    \(\xi_{\mathfrak c}\) is a two-sided feasible tangent direction after the
    standard smooth approximation of the minimal lift.  The second variation
    along this direction is

    \[
    G_{\rm br}(\xi_{\mathfrak c},\xi_{\mathfrak c})
    =
    Q_{\rm eff}(r_{\mathfrak c},r_{\mathfrak c}).
    \tag{G1QeffEqualsSecond}
    \]

    If (G1QeffCert) holds, the second variation is strictly negative.  This
    contradicts the second-order necessary condition for a compact
    non-pinched minimizer in the regular separated chart.  Hence:

    \[
    \boxed{
    \text{QeffNegativeCertificate}
    \Rightarrow
    \text{the compact non-pinched }g=2\text{ rank-defect chamber cannot persist.}
    }
    \tag{G1QeffExcludes}
    \]

    This is a proof, not an additional route name: it is the precise
    second-variation replacement for RawAugmentedCircuitSign.  The only
    remaining Gate 1 computation is the finite sign audit of
    \(Q_{\rm eff}(r_{\mathfrak c},r_{\mathfrak c})\) for the atomic
    certificates.  Degenerate cases in which \(r_{\mathfrak c}=0\), support
    points collide, or the row image leaves the separated chart are exactly
    the Gate 3 boundary modes.

    Finite matrix form of the remaining sign audit.

    Fix a basis \(q_1,\ldots,q_m\) of the endpoint-row image
    \(V_{\rm ep}\subset V^\sharp\) after the zero-mass, free-period, and
    boundary-neutral equality conventions.  Write every certificate row as

    \[
    r_{\mathfrak c}=\sum_{\mu=1}^m\alpha_\mu(\mathfrak c)q_\mu.
    \tag{G1alpha}
    \]

    In this basis the effective endpoint Hessian is the symmetric matrix

    \[
    \boxed{
    \mathcal H_{\mu\nu}
    =
    b(q_\mu,q_\nu)
    +
    (C^{-1})_{\mu\nu},
    }
    \tag{G1Hmatrix}
    \]

    where \(C_{\mu\nu}=\mathcal E_{\log}(g_\mu,g_\nu)\) is the Riesz Gram
    matrix for the row representers and \(b\) is the finite non-log
    branch-state Hessian in the same row coordinates.  Thus

    \[
    Q_{\rm eff}(r_{\mathfrak c},r_{\mathfrak c})
    =
    \alpha(\mathfrak c)^T\mathcal H\,\alpha(\mathfrak c).
    \tag{G1QeffMatrix}
    \]

    The atomic certificate cone is the finite-dimensional cone

    \[
    \mathcal C_{\rm at}
    =
    \left\{
    \alpha(\mathfrak c):
    \eta b_S+\sum_kw_kV_S(x_k)-\lambda\rho_S=0,\
    \eta\ge0,\ w_k>0,\ x_k\in Z_0
    \right\}.
    \tag{G1Cat}
    \]

    After excluding the boundary cases \(r_{\mathfrak c}=0\), support
    collision, and chart-rank loss, normalize

    \[
    \|\alpha(\mathfrak c)\|=1.
    \]

    The normalized certificate set

    \[
    \mathcal C_{\rm at}^{1}
    =
    \mathcal C_{\rm at}\cap S^{m-1}
    \tag{G1Cat1}
    \]

    is compact in the non-boundary separated chart: by conic Carathéodory
    \(N\le5\), \(Z_0\) is compact, and the excluded degeneracies are precisely
    the cases where the support falls to a smaller circuit or exits the chart.

    Therefore the remaining Gate 1 sign is exactly the scalar finite
    optimization

    \[
    \boxed{
    \Lambda_{\rm at}
    =
    \max_{\alpha\in\mathcal C_{\rm at}^{1}}
    \alpha^T\mathcal H\alpha.
    }
    \tag{G1LambdaAt}
    \]

    We have proved the equivalence:

    \[
    \boxed{
    \text{QeffNegativeCertificate}
    \Longleftrightarrow
    \Lambda_{\rm at}<0.
    }
    \tag{G1LambdaCriterion}
    \]

    Indeed, if \(\Lambda_{\rm at}<0\), then every normalized non-boundary
    certificate has negative \(Q_{\rm eff}\)-value, and homogeneity gives
    (G1QeffCert).  Conversely, if (G1QeffCert) holds but
    \(\Lambda_{\rm at}\ge0\), compactness gives a normalized certificate
    attaining a nonnegative value, contradicting (G1QeffCert).

    Thus the card point is now a finite matrix inequality on the explicit cone
    \(\mathcal C_{\rm at}\).  No density closure, PV equation, or first-order
    determinant orientation remains hidden in Gate 1.  To finish Gate 1 one
    must compute \(\mathcal H\) and prove \(\Lambda_{\rm at}<0\), or exhibit an
    optimizer with \(\Lambda_{\rm at}\ge0\) as a concrete obstruction.

    Local-margin versus capacity-load criterion.

    Write

    \[
    \mathcal H=B_{\rm at}+N_{\log},
    \qquad
    N_{\log}=C^{-1},
    \tag{G1HNsplit}
    \]

    in the certificate basis.  Here \(B_{\rm at}\) is the finite non-log
    branch/state Hessian transported to the endpoint-row image, and
    \(N_{\log}\) is the positive Riesz/Feshbach load.  On the normalized
    certificate cone define

    \[
    \boxed{
    \mu_{\rm loc}
    =
    \min_{\alpha\in\mathcal C_{\rm at}^{1}}
    \left(-\alpha^TB_{\rm at}\alpha\right),
    \qquad
    \nu_{\log}
    =
    \max_{\alpha\in\mathcal C_{\rm at}^{1}}
    \alpha^TN_{\log}\alpha.
    }
    \tag{G1Margins}
    \]

    These extrema exist by compactness of \(\mathcal C_{\rm at}^{1}\).  For
    every normalized certificate,

    \[
    \alpha^T\mathcal H\alpha
    =
    \alpha^TB_{\rm at}\alpha+\alpha^TN_{\log}\alpha
    \le
    -\mu_{\rm loc}+\nu_{\log}.
    \]

    Therefore we have the proof-grade sufficient criterion

    \[
    \boxed{
    \mu_{\rm loc}>\nu_{\log}
    \Longrightarrow
    \Lambda_{\rm at}<0.
    }
    \tag{G1DominanceCriterion}
    \]

    Conversely, if \(\mu_{\rm loc}\le\nu_{\log}\), this dominance test gives no
    sign; one must either evaluate the coupled maximum
    \(\Lambda_{\rm at}\) directly or find a sharper correlation estimate
    between \(B_{\rm at}\) and \(N_{\log}\) on \(\mathcal C_{\rm at}^{1}\).

    There is also a pointwise Schur version that avoids explicitly writing
    \(C^{-1}\).  For a nonzero certificate vector \(\alpha\), set

    \[
    T_{\rm loc}(\alpha)=-\alpha^TB_{\rm at}\alpha.
    \]

    If \(T_{\rm loc}(\alpha)>0\), then

    \[
    \alpha^T(B_{\rm at}+C^{-1})\alpha<0
    \]

    is equivalent to

    \[
    \boxed{
    \begin{pmatrix}
    C&\alpha\\
    \alpha^T&T_{\rm loc}(\alpha)
    \end{pmatrix}
    \succ0
    }
    \tag{G1PointSchur}
    \]

    by the Schur complement.  Thus Gate 1 can be closed by either of two fully
    finite checks:

    \[
    \boxed{
    \Lambda_{\rm at}<0
    \quad\text{or}\quad
    \text{(G1PointSchur) for every }\alpha\in\mathcal C_{\rm at}^{1}.
    }
    \tag{G1FiniteCloseOptions}
    \]

    This is the exact next computation.  It requires explicit formulas or
    certified estimates for \(B_{\rm at}\), the row Gram \(C\), and the
    certificate cone \(\mathcal C_{\rm at}\).  It does not require the retired
    first-order determinant sign.

    Two-cut Riesz Gram formula.

    We now make the \(C\)-matrix in (G1HNsplit) computable.  Work in the
    separated two-cut chart

    \[
    J=[\alpha_1,\beta_1]\cup[\alpha_2,\beta_2],
    \qquad
    R(z)^2=\prod_{r=1}^2(z-\alpha_r)(z-\beta_r),
    \qquad
    R(z)\sim z^2.
    \]

    Let \(k_\mu\) be one of the row kernels defining the endpoint-row image
    after zero-mass and fixed-period conventions.  The Riesz representer
    \(g_\mu\in H_{0,\Pi}\) is characterized by

    \[
    \mathcal E_{\log}(g_\mu,h)=\ell_\mu(h)
    =
    \int_J k_\mu(x)\,dh(x)
    \qquad(h\in H_{0,\Pi}).
    \tag{G1RieszDef}
    \]

    Hence, on \(J\), the potential of \(g_\mu\) has the Euler form

    \[
    U_{g_\mu}(x)=k_\mu(x)+A_\mu+B_\mu\pi_0(x),
    \tag{G1RieszEuler}
    \]

    with \(A_\mu,B_\mu\) the Lagrange multipliers for zero mass and fixed
    period.  On each open cut interval, differentiating gives

    \[
    \operatorname{p.v.}\int_J\frac{dg_\mu(t)}{x-t}
    =
    f_\mu(x),
    \qquad
    f_\mu(x):=-k_\mu'(x),
    \tag{G1RieszPV}
    \]

    up to the harmless sign convention fixed by the definition of
    \(\mathcal E_{\log}\).  We use this sign convention below.

    Let \(\mathcal P_\mu\) be the finite set of off-cut poles of \(f_\mu\).  Set

    \[
    \operatorname{PP}_\mu(z)
    =
    \operatorname{PP}_{\mathcal P_\mu}\bigl(R(z)f_\mu(z)\bigr),
    \tag{G1PP}
    \]

    the sum of the principal parts of \(R f_\mu\) at those poles.  Then the
    Cauchy transform of \(g_\mu\) is

    \[
    \boxed{
    C_\mu(z)
    =
    f_\mu(z)
    -
    \frac{\operatorname{PP}_\mu(z)}{R(z)}
    +
    \frac{A_\mu+B_\mu z}{R(z)}.
    }
    \tag{G1RieszCauchy}
    \]

    The term \(\operatorname{PP}_\mu/R\) cancels every off-cut pole of
    \(f_\mu\).  The remaining constants \(A_\mu,B_\mu\) are uniquely fixed by

    \[
    [z^{-1}]_\infty C_\mu=0,
    \qquad
    \Pi(C_\mu)=0,
    \tag{G1RieszNorm}
    \]

    namely zero total mass and the fixed-period normalization.  If this
    \(2\times2\) normalization system is singular, the chart is not a separated
    regular two-cut chart and the case is routed to Gate 3.

    The density is the jump of \(C_\mu\):

    \[
    dg_\mu(x)
    =
    \frac{1}{2\pi i}\left(C_{\mu,-}(x)-C_{\mu,+}(x)\right)\,dx.
    \tag{G1RieszDensity}
    \]

    Therefore the Riesz Gram entries are the explicit finite-Hilbert integrals

    \[
    \boxed{
    C_{\mu\nu}
    =
    \ell_\mu(g_\nu)
    =
    \int_J k_\mu(x)\,dg_\nu(x)
    =
    \int_J k_\mu(x)
    \frac{C_{\nu,-}(x)-C_{\nu,+}(x)}{2\pi i}\,dx.
    }
    \tag{G1RieszGramFormula}
    \]

    Symmetry follows from the Riesz identity

    \[
    C_{\mu\nu}
    =
    \mathcal E_{\log}(g_\mu,g_\nu)
    =
    C_{\nu\mu},
    \]

    and positivity follows from the positive zero-mass log-energy on
    \(H_{0,\Pi}\).  Thus \(C\succ0\) exactly when the chosen row kernels are
    independent modulo the zero-mass/fixed-period constraints; otherwise the
    zero eigenvector is a row-relation boundary and must be removed before
    applying (G1PointSchur).

    This closes the formal construction of the capacity-load matrix.  The
    remaining numerical/symbolic task is now finite: insert the actual kernels
    \(k_\mu\) for the endpoint certificate basis into (G1RieszCauchy), compute
    \(C\) by (G1RieszGramFormula), and then prove either
    (G1DominanceCriterion) or (G1PointSchur).

    Gate 1 row-kernel table.

    The row kernels needed by the separated chart are generated by

    \[
    k_0=1,\quad
    k_u=(x-u)^{-1},\quad
    k_c=(x-c)^{-1},\quad
    k_v=(x-v)^{-1},
    \]

    \[
    k_-=L_-=\log|x-u|-\log|x-c|,
    \qquad
    k_+=L_+=\log|x-c|-\log|x-v|,
    \]

    and

    \[
    k_{\log c}=\log\frac1{|c-x|}=-\log|x-c|.
    \]

    The period coordinate is not inserted as an arbitrary interior step
    kernel.  In the separated chart it is either a topological finite
    coordinate handled by the normalization equation \(\Pi(C_\mu)=0\), or a
    gap-supported \(H^{1/2}\) kernel.  If its jump enters an active support
    interval, the separated Riesz-Gram formula is not applicable and the case
    routes to Gate 3.

    For the row kernels above, \(f_\mu=-k_\mu'\) and the principal parts in
    (G1PP) are explicit:

    \[
    \begin{array}{c|c|c}
    k_\mu & f_\mu=-k_\mu' & \operatorname{PP}_\mu
    \\ \hline
    1 & 0 & 0\\
    (x-s)^{-1},\ s\in\{u,c,v\}
    &
    (x-s)^{-2}
    &
    \dfrac{R(s)}{(z-s)^2}+\dfrac{R'(s)}{z-s}
    \\
    L_- &
    -\dfrac1{x-u}+\dfrac1{x-c}
    &
    -\dfrac{R(u)}{z-u}+\dfrac{R(c)}{z-c}
    \\
    L_+ &
    -\dfrac1{x-c}+\dfrac1{x-v}
    &
    -\dfrac{R(c)}{z-c}+\dfrac{R(v)}{z-v}
    \\
    \log\dfrac1{|c-x|}
    &
    \dfrac1{x-c}
    &
    \dfrac{R(c)}{z-c}
    \end{array}
    \tag{G1RowKernelTable}
    \]

    Here \(s=u,c,v\) are separated from \(J\).  The signs follow from the
    convention \(f=-k'\).  For example,

    \[
    -\frac{d}{dx}L_-(x)
    =
    -\frac1{x-u}+\frac1{x-c},
    \]

    so \(R(z)f(z)\) has simple principal parts
    \(-R(u)/(z-u)+R(c)/(z-c)\).

    Therefore each \(C_\mu\) entering the Gram matrix is obtained by inserting
    the corresponding row of (G1RowKernelTable) into (G1RieszCauchy) and then
    solving the two normalization equations (G1RieszNorm).  This is the first
    fully explicit input needed for \(C\); no unspecified Hilbert row remains
    except the period normalization, whose separated-chart admissibility is
    already isolated.

    Normalization solver for \(A_\mu,B_\mu\).

    Put

    \[
    \widetilde C_\mu(z)
    =
    f_\mu(z)-\frac{\operatorname{PP}_\mu(z)}{R(z)}.
    \tag{G1Ctilde}
    \]

    Define the two linear functionals

    \[
    m(T)=[z^{-1}]_\infty T,
    \qquad
    p(T)=\Pi(T).
    \]

    Then \(A_\mu,B_\mu\) are determined by

    \[
    \begin{pmatrix}
    m(R^{-1})&m(zR^{-1})\\
    p(R^{-1})&p(zR^{-1})
    \end{pmatrix}
    \binom{A_\mu}{B_\mu}
    =
    -
    \binom{m(\widetilde C_\mu)}{p(\widetilde C_\mu)}.
    \tag{G1NormMatrix}
    \]

    Because \(R(z)\sim z^2\),

    \[
    m(R^{-1})=0,\qquad m(zR^{-1})=1.
    \tag{G1MassRow}
    \]

    Hence, in the standard two-cut normalization, set

    \[
    \pi_0=p(R^{-1}),\qquad \pi_1=p(zR^{-1}),
    \qquad
    m_\mu=m(\widetilde C_\mu),\qquad p_\mu=p(\widetilde C_\mu).
    \]

    If \(\pi_0\ne0\), then

    \[
    \boxed{
    B_\mu=-m_\mu,
    \qquad
    A_\mu=
    \frac{-p_\mu+m_\mu\pi_1}{\pi_0}.
    }
    \tag{G1NormSolution}
    \]

    This gives a fully explicit Cauchy transform:

    \[
    \boxed{
    C_\mu(z)
    =
    \widetilde C_\mu(z)
    +
    \frac{1}{R(z)}
    \left(
    \frac{-p_\mu+m_\mu\pi_1}{\pi_0}
    -
    m_\mu z
    \right).
    }
    \tag{G1CmuExplicit}
    \]

    If \(\pi_0=0\), the pair \((m,\Pi)\) does not normalize the
    one-dimensional mass-free nullspace in this chart.  That is a
    period-normalization degeneracy, not a hidden analytic case; it must be
    handled either by changing the period coordinate or by routing the point to
    Gate 3 boundary / chart-rank loss.

    Thus the capacity matrix is now algorithmic:

    \[
    k_\mu
    \longmapsto
    \widetilde C_\mu
    \longmapsto
    (m_\mu,p_\mu)
    \longmapsto
    C_\mu
    \longmapsto
    C_{\nu\mu}
    =
    \int_J k_\nu\,dg_\mu.
    \tag{G1CAlgorithm}
    \]

    Explicit \(\widetilde C_\mu\) and mass coefficients.

    From (G1RowKernelTable), the unnormalized transforms
    \(\widetilde C_\mu=f_\mu-\operatorname{PP}_\mu/R\) are:

    \[
    \boxed{
    \widetilde C_0=0.
    }
    \tag{G1CtildeConst}
    \]

    Thus the constant row is zero on the zero-mass Hilbert space and must be
    removed from any Gram basis.  Keeping it would make \(C\) singular for a
    purely formal reason.

    For \(s\in\{u,c,v\}\),

    \[
    \boxed{
    \widetilde C_s(z)
    =
    \frac{1}{(z-s)^2}
    -
    \frac{1}{R(z)}
    \left(
    \frac{R(s)}{(z-s)^2}
    +
    \frac{R'(s)}{z-s}
    \right)
    =
    \frac{R(z)-R(s)-R'(s)(z-s)}
    {(z-s)^2R(z)}.
    }
    \tag{G1CtildeCauchy}
    \]

    For the two split log rows,

    \[
    \boxed{
    \widetilde C_-(z)
    =
    -\frac1{z-u}+\frac1{z-c}
    -
    \frac1{R(z)}
    \left(
    -\frac{R(u)}{z-u}
    +
    \frac{R(c)}{z-c}
    \right),
    }
    \tag{G1CtildeMinus}
    \]

    and

    \[
    \boxed{
    \widetilde C_+(z)
    =
    -\frac1{z-c}+\frac1{z-v}
    -
    \frac1{R(z)}
    \left(
    -\frac{R(c)}{z-c}
    +
    \frac{R(v)}{z-v}
    \right).
    }
    \tag{G1CtildePlus}
    \]

    For the anchor log row,

    \[
    \boxed{
    \widetilde C_{\log c}(z)
    =
    \frac1{z-c}
    -
    \frac{R(c)}{(z-c)R(z)}.
    }
    \tag{G1CtildeLogc}
    \]

    Taking \(m(T)=[z^{-1}]_\infty T\), and using \(R(z)\sim z^2\), gives

    \[
    \boxed{
    m(\widetilde C_s)=0\quad(s=u,c,v),\qquad
    m(\widetilde C_-)=m(\widetilde C_+)=0,\qquad
    m(\widetilde C_{\log c})=1.
    }
    \tag{G1MassCoefficients}
    \]

    Consequently the mass-normalizing coefficient \(B_\mu=-m_\mu\) is zero for
    the Cauchy rows and split log rows, while

    \[
    \boxed{
    B_{\log c}=-1.
    }
    \tag{G1Blogc}
    \]

    The remaining \(A_\mu\)'s are obtained from (G1NormSolution):

    \[
    A_s=-\frac{p(\widetilde C_s)}{\pi_0},
    \quad
    A_-=-\frac{p(\widetilde C_-)}{\pi_0},
    \quad
    A_+=-\frac{p(\widetilde C_+)}{\pi_0},
    \quad
    A_{\log c}=\frac{-p(\widetilde C_{\log c})+\pi_1}{\pi_0}.
    \tag{G1Acoefficients}
    \]

    Thus every \(C_\mu\) used in the capacity-load matrix is now explicit up
    to the two period constants \(\pi_0,\pi_1\) and the period evaluations
    \(p(\widetilde C_\mu)\).  Those are one-dimensional period integrals in
    the chosen separated chart.

    Period-normalized transform table.

    Let

    \[
    p_s=p(\widetilde C_s)\quad(s=u,c,v),\qquad
    p_-=p(\widetilde C_-),\qquad
    p_+=p(\widetilde C_+),\qquad
    p_{\log c}=p(\widetilde C_{\log c}).
    \]

    In the nondegenerate period chart \(\pi_0\ne0\), the final normalized
    Cauchy transforms are therefore

    \[
    \boxed{
    C_s(z)=
    \widetilde C_s(z)-\frac{p_s}{\pi_0R(z)}
    \quad(s=u,c,v),
    }
    \tag{G1CfinalCauchy}
    \]

    \[
    \boxed{
    C_-(z)=\widetilde C_-(z)-\frac{p_-}{\pi_0R(z)},
    \qquad
    C_+(z)=\widetilde C_+(z)-\frac{p_+}{\pi_0R(z)},
    }
    \tag{G1CfinalSplit}
    \]

    and

    \[
    \boxed{
    C_{\log c}(z)
    =
    \widetilde C_{\log c}(z)
    +
    \frac{1}{R(z)}
    \left(
    \frac{-p_{\log c}+\pi_1}{\pi_0}-z
    \right).
    }
    \tag{G1CfinalLogc}
    \]

    Equivalently, write

    \[
    C_\mu(z)=\frac{N_\mu(z)}{R(z)}.
    \]

    The numerators are the following explicit removable-singularity
    expressions:

    \[
    \boxed{
    N_s(z)
    =
    \frac{R(z)-R(s)-R'(s)(z-s)}{(z-s)^2}
    -
    \frac{p_s}{\pi_0},
    \quad s=u,c,v,
    }
    \tag{G1Ns}
    \]

    \[
    \boxed{
    N_-(z)
    =
    -\frac{R(z)-R(u)}{z-u}
    +
    \frac{R(z)-R(c)}{z-c}
    -
    \frac{p_-}{\pi_0},
    }
    \tag{G1Nminus}
    \]

    \[
    \boxed{
    N_+(z)
    =
    -\frac{R(z)-R(c)}{z-c}
    +
    \frac{R(z)-R(v)}{z-v}
    -
    \frac{p_+}{\pi_0},
    }
    \tag{G1Nplus}
    \]

    and

    \[
    \boxed{
    N_{\log c}(z)
    =
    \frac{R(z)-R(c)}{z-c}
    +
    \frac{-p_{\log c}+\pi_1}{\pi_0}
    -
    z.
    }
    \tag{G1Nlogc}
    \]

    These formulae remove the apparent poles at \(u,c,v\).  They also show
    exactly where the period normalization enters: only through the scalar
    period data \(p_\mu,\pi_0,\pi_1\).

    Closed Gram-entry formula.

    Fix the branch convention \(R(z)\sim z^2\) at infinity and set, on the two
    cuts,

    \[
    d\Omega_R(x)
    =
    \frac{R_-(x)^{-1}-R_+(x)^{-1}}{2\pi i}\,dx.
    \tag{G1OmegaR}
    \]

    Since \(C_\mu=N_\mu/R\), the representing density is simply

    \[
    \boxed{
    dg_\mu(x)=N_\mu(x)\,d\Omega_R(x).
    }
    \tag{G1DensityN}
    \]

    Hence for the actual Gate 1 row basis

    \[
    \mathcal K_{\rm G1}
    =
    \left\{
    (x-u)^{-1},(x-c)^{-1},(x-v)^{-1},
    L_-,L_+,\log\frac1{|c-x|}
    \right\},
    \]

    with the constant row removed by zero mass, the capacity-load matrix is

    \[
    \boxed{
    C_{\nu\mu}
    =
    \int_J k_\nu(x)\,N_\mu(x)\,d\Omega_R(x),
    \qquad
    k_\nu\in\mathcal K_{\rm G1}.
    }
    \tag{G1ClosedGramEntry}
    \]

    This is the promised finite sign object.  No density-closure assumption and
    no principal-value equation is being invoked: \(C\) is computed by
    one-dimensional cut integrals of the explicit functions \(N_\mu\).

    The matrix is symmetric by the Riesz identity

    \[
    C_{\nu\mu}
    =
    \mathcal E_{\log}(g_\nu,g_\mu)
    =
    C_{\mu\nu},
    \]

    and it is positive definite on the quotient row span in the regular
    non-pinched chart.  If a nonzero row combination has zero \(C\)-norm, its
    minimal lift is zero and the corresponding row is redundant; that is a
    chart-rank loss and is routed to the Gate 3 boundary stratum.

    Thus the remaining Gate 1 inequality is now a finite, explicit matrix
    assertion.  With \(C\) given by (G1ClosedGramEntry), \(N_{\log}=C^{-1}\),
    and the local endpoint block \(B_{\rm at}\) from the endpoint second
    variation,

    \[
    \boxed{
    \alpha^T\left(B_{\rm at}+C^{-1}\right)\alpha<0
    \quad
    \text{for every nonzero }
    \alpha\in\mathcal C_{\rm at}.
    }
    \tag{G1FinalFiniteInequality}
    \]

    Equivalently,

    \[
    \boxed{
    \begin{pmatrix}
    C&\alpha\\
    \alpha^T&-\alpha^TB_{\rm at}\alpha
    \end{pmatrix}\succ0
    \quad
    \text{for every projective }
    \alpha\in\mathcal C_{\rm at}.
    }
    \tag{G1FinalSchurTest}
    \]

    This is the next exact finite certificate required to finish Gate 1.
    Compared with the failed first-order determinant route, all arbitrary
    bump-correction and moving-chart choices have disappeared; only the
    two-cut period data and the endpoint Hessian remain.

    Explicit finite branch Hessian block.

    It remains to put \(B_{\rm at}\) in the same row coordinates as \(C\).  This
    part is local and can be written without another Hilbert problem.

    Use \(y=(q,a,b,c)\), \(u=c-a\), \(v=c+b\), and set

    \[
    A_2=W''(u),\qquad B_2=W''(v),\qquad
    \lambda_-=\frac1X,\qquad \lambda_+=-\frac1Y.
    \]

    For a state displacement

    \[
    \delta y=(\delta q,\delta a,\delta b,\delta c),
    \]

    the two endpoint energies have second differentials

    \[
    \boxed{
    D^2E_-[\delta y,\delta y]
    =
    -\frac{2}{a}\delta q\,\delta a
    +
    \frac{q}{a^2}(\delta a)^2
    +
    A_2(\delta c-\delta a)^2,
    }
    \tag{G1D2Eminus}
    \]

    and

    \[
    \boxed{
    D^2E_+[\delta y,\delta y]
    =
    -\frac{2}{b}\delta q\,\delta b
    +
    \frac{q}{b^2}(\delta b)^2
    +
    B_2(\delta c+\delta b)^2.
    }
    \tag{G1D2Eplus}
    \]

    Thus the finite branch Hessian form is

    \[
    \boxed{
    B_{\rm at}^{(y)}[\delta y,\delta y]
    =
    \lambda_-D^2E_-[\delta y,\delta y]
    +
    \lambda_+D^2E_+[\delta y,\delta y].
    }
    \tag{G1ByForm}
    \]

    For row coordinates

    \[
    r=(r_0,r_u,r_c,r_v,r_-,r_+,r_{\log},r_\Pi),
    \]

    the branch-state linear equations give the state lift

    \[
    \boxed{
    \delta q=-r_0,\qquad
    \delta c=\frac{r_c}{F_c},
    }
    \tag{G1StateLiftQC}
    \]

    \[
    \boxed{
    \delta a=
    \frac{-\ell_-r_0+A\,r_c/F_c+r_{\log}-r_-}{X},
    }
    \tag{G1StateLiftA}
    \]

    and

    \[
    \boxed{
    \delta b=
    \frac{-r_++\ell_+r_0-B\,r_c/F_c-r_{\log}}{Y}.
    }
    \tag{G1StateLiftB}
    \]

    Here

    \[
    \ell_-=\log\frac1a,\qquad \ell_+=\log\frac1b.
    \]

    The rows \(r_u,r_v,r_\Pi\) do not enter this local state lift; they enter
    the certificate cone and the Riesz load through the row kernels already
    listed in \(\mathcal K_{\rm G1}\).  Therefore the branch block in row
    coordinates is the pullback

    \[
    \boxed{
    B_{\rm at}(r,r')
    =
    B_{\rm at}^{(y)}[T_y r,T_y r'],
    }
    \tag{G1BatPullback}
    \]

    where \(T_y\) is the linear map (G1StateLiftQC)--(G1StateLiftB).

    In the formal endpoint-length basis

    \[
    e_u^0=(0,1,0,0),\qquad
    e_v^0=(0,0,1,0),\qquad
    e_\zeta^0=(0,1,-1,1)
    \]

    of state displacements, the local matrix is

    \[
    \boxed{
    B_{\rm at}^{0}
    =
    \begin{pmatrix}
    \dfrac{q/a^2+A_2}{X}
    &
    0
    &
    \dfrac{q}{a^2X}
    \\[1.1em]
    0
    &
    -\dfrac{q/b^2+B_2}{Y}
    &
    \dfrac{q}{b^2Y}
    \\[1.1em]
    \dfrac{q}{a^2X}
    &
    \dfrac{q}{b^2Y}
    &
    \dfrac{q}{a^2X}-\dfrac{q}{b^2Y}
    \end{pmatrix}.
    }
    \tag{G1BatFormalMatrix}
    \]

    The third diagonal entry reproduces the earlier diagonal-shortcut audit:

    \[
    B_{\rm at}^{0}(e_\zeta^0,e_\zeta^0)
    =
    \frac{q}{a^2X}-\frac{q}{b^2Y}
    =
    \frac{q(a+b)}{a^2bX}>0.
    \]

    Hence the diagonal shortcut still fails.  The value of the present
    calculation is different: it supplies the exact finite local block for the
    Schur test (G1FinalSchurTest).  Gate 1 is therefore reduced to the
    following fully explicit data:

    \[
    \boxed{
    C_{\nu\mu}
    =
    \int_J k_\nu N_\mu\,d\Omega_R,
    \qquad
    B_{\rm at}=T_y^*B_{\rm at}^{(y)}T_y,
    \qquad
    \alpha\in\mathcal C_{\rm at}.
    }
    \tag{G1DataForFinalCheck}
    \]

    The remaining proof obligation is no longer to define either matrix; it is
    to prove the Schur positivity (G1FinalSchurTest) on the atomic certificate
    cone.

    Atomic certificate rows.

    There is one more domain issue that must be kept explicit.  The fixed row
    table \(\mathcal K_{\rm G1}\) above covers the off-cut endpoint, split-log,
    anchor, and equality rows.  A genuine atomic Farkas certificate also
    contains point-potential rows at the support points \(x_k\in Z_0\).  These
    rows are not equal to any fixed finite subset of \(\mathcal K_{\rm G1}\).

    For a certificate

    \[
    \mathfrak c=(\eta;\,w_k,x_k;\lambda),
    \]

    the raw row kernel is

    \[
    \boxed{
    k_{\mathfrak c}(t)
    =
    \eta\left(
    a\log\frac1{|u-t|}
    +
    b\log\frac1{|v-t|}
    \right)
    +
    \sum_k w_k\log\frac1{|x_k-t|}
    -
    \lambda\,\frac1{t-c}.
    }
    \tag{G1CertKernel}
    \]

    With the convention \(f=-k'\), its formal derivative is

    \[
    \boxed{
    f_{\mathfrak c}(z)
    =
    \eta\left(
    \frac{a}{z-u}
    +
    \frac{b}{z-v}
    \right)
    +
    \sum_k\frac{w_k}{z-x_k}
    -
    \frac{\lambda}{(z-c)^2}.
    }
    \tag{G1CertDerivative}
    \]

    The off-cut principal parts are explicit:

    \[
    \operatorname{PP}_{u,v,c}(Rf_{\mathfrak c})
    =
    \eta a\frac{R(u)}{z-u}
    +
    \eta b\frac{R(v)}{z-v}
    -
    \lambda
    \left(
    \frac{R(c)}{(z-c)^2}
    +
    \frac{R'(c)}{z-c}
    \right).
    \tag{G1CertOffcutPP}
    \]

    The terms \(w_k/(z-x_k)\) are on-cut singularities.  They cannot be hidden
    inside the off-cut row table.  The proof-grade way to keep the calculation
    finite is to use symmetric regularized point rows

    \[
    k_{x,\varepsilon}(t)
    =
    \frac12\log\frac1{|x+i\varepsilon-t|}
    +
    \frac12\log\frac1{|x-i\varepsilon-t|},
    \qquad \varepsilon>0,
    \tag{G1PointRegKernel}
    \]

    compute their Riesz transforms by the same formula (G1RieszCauchy), and
    only then take the limit \(\varepsilon\downarrow0\).  For fixed
    \(\varepsilon>0\), the added principal parts are

    \[
    \frac{w_k}{2}
    \left(
    \frac{R(x_k+i\varepsilon)}{z-(x_k+i\varepsilon)}
    +
    \frac{R(x_k-i\varepsilon)}{z-(x_k-i\varepsilon)}
    \right),
    \tag{G1PointRegPP}
    \]

    together with the corresponding period-normalizing
    \((A_{\mathfrak c,\varepsilon},B_{\mathfrak c,\varepsilon})\).

    Thus the actual certificate-capacity object is not a fixed \(6\times6\)
    matrix alone, but the regularized finite family

    \[
    \boxed{
    C_{\mathfrak c,\varepsilon}
    =
    \mathcal E_{\log}(g_{\mathfrak c,\varepsilon},
    g_{\mathfrak c,\varepsilon}),
    \qquad
    g_{\mathfrak c,\varepsilon}=S k_{\mathfrak c,\varepsilon}.
    }
    \tag{G1CertCapacity}
    \]

    The Gate 1 Schur test for an atomic certificate must therefore be read as

    \[
    \boxed{
    \liminf_{\varepsilon\downarrow0}
    \left[
    B_{\rm at}(r_{\mathfrak c,\varepsilon},
    r_{\mathfrak c,\varepsilon})
    +
    N_{\log,\varepsilon}(r_{\mathfrak c,\varepsilon},
    r_{\mathfrak c,\varepsilon})
    \right]
    <0,
    }
    \tag{G1AtomicLimitSchur}
    \]

    or, equivalently, by the projective Schur positivity of the corresponding
    regularized finite Gram block before taking the limit.  If this limit
    exists and is negative uniformly on normalized non-boundary certificates,
    then \(Q_{\rm eff}<0\) for every atomic fallback.  If the limit diverges,
    the sign of the divergent part must be computed from (G1PointRegPP); if a
    support point collides with a branch endpoint or with another support
    point, the certificate is no longer in the non-boundary interior and is
    routed to Gate 3.

    This is the corrected final form of the Gate 1 hard calculation.  The
    previously recorded fixed-row \(C\)-matrix is the off-cut subblock; the
    atomic point rows are supplied by the regularized limit above.

    Point-row blow-up audit.

    The regularized point rows have a decisive asymptotic.  If \(x\) stays in
    the positive-distance interior of \(Z_0\cap J\), then the symmetric row
    \(k_{x,\varepsilon}\) has Riesz norm

    \[
    \boxed{
    \mathcal E_{\log}(g_{x,\varepsilon},g_{x,\varepsilon})
    =
    \log\frac1\varepsilon+O(1),
    \qquad \varepsilon\downarrow0,
    }
    \tag{G1PointSelfBlowup}
    \]

    with the sign fixed by the positive zero-mass logarithmic energy.  The
    reason is local: near \(x\), the two-cut density and the branch \(R\) are
    smooth nonzero after flattening the cut, and the symmetric off-cut
    logarithmic source has the same \(H^{1/2}\)-trace singularity as the
    Poisson kernel in a half-plane.  The zero-mass and period-normalizing
    corrections are smooth in a neighbourhood of \(x\), so they only change
    the \(O(1)\) term.

    For distinct support points separated from each other and from endpoints,
    the cross terms remain finite:

    \[
    \mathcal E_{\log}(g_{x_i,\varepsilon},g_{x_j,\varepsilon})=O(1)
    \quad (i\ne j).
    \tag{G1PointCrossFinite}
    \]

    Consequently, if the atomic certificate contains at least one genuine
    \(Z_0\)-atom, then

    \[
    \boxed{
    \mathcal E_{\log}
    \left(
    \sum_k w_kg_{x_k,\varepsilon},
    \sum_k w_kg_{x_k,\varepsilon}
    \right)
    =
    \left(\sum_{\chi}W_\chi^2\right)\log\frac1\varepsilon+O(1),
    }
    \tag{G1PointClusterBlowup}
    \]

    where the sum is over clusters of support points that remain mutually
    \(o(1)\)-close and \(W_\chi\) is the total positive weight in the cluster.
    Since \(w_k>0\), every nonempty cluster has \(W_\chi>0\).  Thus the
    divergent coefficient is strictly positive unless the \(Z_0\)-atomic part
    is absent.

    This proves a necessary correction to the second-variation route:

    \[
    \boxed{
    \text{A certificate with a nonzero }Z_0\text{-atomic part cannot be
    excluded by a finite negative }Q_{\rm eff}\text{ lift.}
    }
    \tag{G1PointAtomNoQeff}
    \]

    The point-row load diverges with the positive sign, whereas
    \(B_{\rm at}\) is finite.  Therefore the \(Q_{\rm eff}\) continuation can
    only close the no-\(Z_0\)-atom subcase, or it must be preceded by a
    separate no-atom theorem for the reduced Farkas certificate.

    The Gate 1 dichotomy is now exact:

    \[
    \boxed{
    \begin{array}{ll}
    \zeta=0: & \text{prove the finite off-cut Schur test
    (G1FinalSchurTest);}\\[0.3em]
    \zeta\ne0: & \text{prove a no-}Z_0\text{-atom theorem or return to the
    first-order raw sign problem.}
    \end{array}}
    \tag{G1PointDichotomy}
    \]

    This is not a new route.  It is the compatibility condition forced by the
    actual Hilbert topology of the \(Z_0\)-restriction row.

    No-atom subcase.

    The first line of (G1PointDichotomy) is now completely finite.  If
    \(\zeta=0\), the raw augmented certificate has no point rows, so its
    Schiffer equations reduce to

    \[
    \boxed{
    \eta b_S-\lambda\rho_S=0,
    \qquad
    \eta\ge0.
    }
    \tag{G1NoAtomRelation}
    \]

    A nontrivial certificate cannot have \(\eta=\lambda=0\).  If \(\eta=0\),
    then \(\lambda\rho_S=0\).  Thus either \(\lambda=0\), which is the zero
    certificate and is discarded, or

    \[
    \rho_S=0.
    \tag{G1RhoDegenerate}
    \]

    The latter is a row-rank degeneracy of the equality-correction anchor:
    the four endpoint Schiffer columns have no \(R_c\)-projection.  In the
    regular moving chart this is routed to the same chart-rank boundary used
    above; otherwise the equality correction loses its separating row.

    Hence in the interior no-atom case one must have \(\eta>0\).  Normalize
    \(\eta=1\).  Then (G1NoAtomRelation) says exactly that

    \[
    \boxed{
    b_S=\Lambda\rho_S,\qquad \Lambda:=\lambda/\eta.
    }
    \tag{G1NoAtomCollinearity}
    \]

    Therefore the no-atom Farkas fallback exists only on the codimension-three
    collinearity locus \(b_S\in\mathbb R\rho_S\).  If this collinearity fails,
    the no-atom branch is impossible.

    If the collinearity holds, the period lift is

    \[
    \Theta_\Pi^{0}
    =
    \eta b_\Pi-\lambda\rho_\Pi
    =
    \eta\left(b_\Pi-\Lambda\rho_\Pi\right).
    \tag{G1NoAtomLift}
    \]

    Thus the no-atom fallback is excluded precisely when

    \[
    \boxed{
    b_S=\Lambda\rho_S
    \quad\Longrightarrow\quad
    b_\Pi-\Lambda\rho_\Pi<0.
    }
    \tag{G1NoAtomSign}
    \]

    Equivalently, define the scalar collinearity minors

    \[
    \boxed{
    \Delta_{\gamma\gamma'}
    =
    b_\gamma\rho_{\gamma'}-b_{\gamma'}\rho_\gamma,
    \qquad
    \gamma,\gamma'\in\{\alpha_1,\beta_1,\alpha_2,\beta_2\}.
    }
    \tag{G1NoAtomMinors}
    \]

    Then \(b_S\notin\mathbb R\rho_S\) iff at least one
    \(\Delta_{\gamma\gamma'}\ne0\).  If all minors vanish and
    \(\rho_S\ne0\), the ratio is unique:

    \[
    \Lambda=\frac{b_\gamma}{\rho_\gamma}
    \quad\text{for any }\gamma\text{ with }\rho_\gamma\ne0.
    \tag{G1NoAtomLambda}
    \]

    If all minors vanish and \(\rho_S=0\), then either \(b_S\ne0\), in which
    case (G1NoAtomRelation) has no nonzero no-atom certificate, or \(b_S=0\),
    in which case the four Schiffer endpoint columns lose both the boundary
    and equality-anchor projections.  That is a repaired-column row-rank
    degeneration and is routed to Gate 3.

    We record the finite theorem needed for this branch:

    \[
    \boxed{\textbf{Gate1NoAtomCertificateExclusion}.}
    }
    \]

    In the regular moving chart, the \(\zeta=0\) Farkas branch is absent if
    some \(\Delta_{\gamma\gamma'}\ne0\).  If all minors vanish and
    \(\rho_S\ne0\), it is excluded exactly by

    \[
    \boxed{
    b_\Pi-\frac{b_\gamma}{\rho_\gamma}\rho_\Pi<0
    \quad
    (\rho_\gamma\ne0).
    }
    \tag{G1NoAtomFinalCheck}
    \]

    If all minors vanish and \(\rho_S=b_S=0\), the case is not an interior
    no-atom certificate but a chart-rank boundary mode.

    This closes the \(\zeta=0\) subcase as an explicit finite algebraic test:
    either \(b_S\) is not collinear with \(\rho_S\), or the unique collinearity
    ratio gives a negative period lift.  No \(Q_{\rm eff}\) or point-row
    regularization remains in this subcase.

    Consequently the only genuinely infinite-dimensional Gate 1 branch left is
    the \(\zeta\ne0\) branch.  By (G1PointAtomNoQeff), that branch cannot be
    closed by a finite negative \(Q_{\rm eff}\) lift; it requires either a
    no-\(Z_0\)-atom theorem for the reduced Farkas fallback or a direct proof
    of the raw first-order sign with \(Z_0\)-atoms included.

    \(Z_0\)-atomic cone criterion.

    The remaining branch can nevertheless be written as an exact finite conic
    envelope problem.  Define the augmented \(Z_0\)-column

    \[
    \mathcal V_Z(x)=
    \binom{V_S(x)}{V_\Pi(x)}
    \in\mathbb R^5,
    \qquad x\in Z_0.
    \tag{G1VZ}
    \]

    For \(y\in\mathbb R^4\), define the upper lifted cone envelope

    \[
    \boxed{
    \Phi_Z(y)
    =
    \sup
    \left\{
    \sum_k w_kV_\Pi(x_k):
    \sum_kw_kV_S(x_k)=y,\quad
    w_k>0,\quad x_k\in Z_0
    \right\},
    }
    \tag{G1PhiZ}
    \]

    with \(\Phi_Z(y)=-\infty\) if \(y\) is outside
    \(\operatorname{cone}\{V_S(x):x\in Z_0\}\).  By conic Carathéodory the
    supremum may be tested with at most five \(Z_0\)-points.

    If \(\eta>0\), normalize \(\eta=1\) and put

    \[
    y(\Lambda)=-b_S+\Lambda\rho_S.
    \tag{G1yLambda}
    \]

    The raw \(Z_0\)-atomic obstruction exists exactly when

    \[
    \boxed{
    \Phi_Z(y(\Lambda))
    \ge
    -b_\Pi+\Lambda\rho_\Pi
    \quad\text{for some }\Lambda\in\mathbb R.
    }
    \tag{G1ZAtomObstructionEta}
    \]

    Therefore the \(\eta>0\) \(Z_0\)-atomic branch is excluded exactly by

    \[
    \boxed{
    \Phi_Z(-b_S+\Lambda\rho_S)
    <
    -b_\Pi+\Lambda\rho_\Pi
    \qquad(\Lambda\in\mathbb R).
    }
    \tag{G1ZAtomSignEta}
    \]

    If \(\eta=0\), the relation is homogeneous:

    \[
    \sum_kw_kV_S(x_k)=\lambda\rho_S.
    \]

    The corresponding obstruction exists exactly when

    \[
    \boxed{
    \Phi_Z(\lambda\rho_S)\ge \lambda\rho_\Pi
    \quad\text{for some }\lambda\in\mathbb R\setminus\{0\}.
    }
    \tag{G1ZAtomObstructionHom}
    \]

    Hence the homogeneous atomic branch is excluded exactly by the strict
    reverse inequality for every nonzero \(\lambda\).

    This gives the sharp replacement for a vague no-atom theorem:

    \[
    \boxed{
    \text{\(Z_0\)-atomic Gate 1 is equivalent to the lifted cone-envelope
    inequalities (G1ZAtomSignEta) and (G1ZAtomObstructionHom).}
    }
    \tag{G1ZAtomConeCriterion}
    \]

    A literal no-\(Z_0\)-atom theorem would be the stronger claim that
    \(y(\Lambda)\) and \(\lambda\rho_S\) never enter the projected cone at all.
    That is not a formal consequence of finite-dimensional Farkas.  The
    correct proof target is the lifted strict inequality above.

    Cone-envelope duality.

    Let

    \[
    K_Z=\operatorname{cone}\{\mathcal V_Z(x):x\in Z_0\}\subset\mathbb R^5.
    \]

    Since \(Z_0\) is compact and \(\mathcal V_Z\) is continuous in the regular
    chart, the relevant cone section is closed after excluding the only
    possible positive-lift recession ray

    \[
    \sum_kw_kV_S(x_k)=0,\qquad \sum_kw_kV_\Pi(x_k)>0.
    \tag{G1PositiveLiftRecession}
    \]

    If such a recession ray exists, the cone-envelope inequality fails
    outright and gives an explicit atomic obstruction.  Otherwise standard
    finite-dimensional conic duality gives

    \[
    \boxed{
    \Phi_Z(y)
    =
    \inf_{\theta\in\mathbb R^4}
    \left\{
    \theta\cdot y:
    \theta\cdot V_S(x)\ge V_\Pi(x)\quad(x\in Z_0)
    \right\}.
    }
    \tag{G1PhiDual}
    \]

    Hence the \(\eta>0\) atomic branch is excluded if, for every
    \(\Lambda\in\mathbb R\), one constructs \(\theta_\Lambda\in\mathbb R^4\)
    such that

    \[
    \boxed{
    \theta_\Lambda\cdot V_S(x)\ge V_\Pi(x)
    \quad(x\in Z_0),
    }
    \tag{G1ThetaMajorantEta}
    \]

    and

    \[
    \boxed{
    \theta_\Lambda\cdot(-b_S+\Lambda\rho_S)
    <
    -b_\Pi+\Lambda\rho_\Pi.
    }
    \tag{G1ThetaStrictEta}
    \]

    Similarly, the homogeneous branch is excluded if, for every
    \(\lambda\ne0\), one constructs \(\theta_\lambda\) with the same majorant
    property and

    \[
    \boxed{
    \theta_\lambda\cdot(\lambda\rho_S)<\lambda\rho_\Pi.
    }
    \tag{G1ThetaStrictHom}
    \]

    This is now the exact Step 3 target: the atom branch is a family of scalar
    potential majorants on \(Z_0\), not an unstructured measure problem.

    Dual majorant reduction.

    For \(\theta\in\mathbb R^4\), define

    \[
    \boxed{
    G_\theta(x)=\theta\cdot V_S(x)-V_\Pi(x).
    }
    \tag{G1Gtheta}
    \]

    The majorant condition in (G1ThetaMajorantEta) is simply

    \[
    G_\theta(x)\ge0\qquad(x\in Z_0).
    \tag{G1GthetaMajorant}
    \]

    Since \(V_j'=-C_j\), the derivative is

    \[
    \boxed{
    G_\theta'(x)
    =
    -\theta\cdot C_S(x)+C_\Pi(x).
    }
    \tag{G1GthetaDerivative}
    \]

    Substituting the repaired moving-chart columns gives

    \[
    \boxed{
    Q(x)^2R(x)G_\theta'(x)
    =
    P_\theta(x),
    \qquad
    P_\theta(z)=
    \kappa Q(z)^2-\sum_\gamma\theta_\gamma H_\gamma^{\rm rep}(z).
    }
    \tag{G1Ptheta}
    \]

    Therefore the \(Z_0\)-majorant problem is equivalent to a one-dimensional
    sign problem for the real numerator \(P_\theta\), together with the
    endpoint/contact values of \(G_\theta\).

    We record the exact lemma needed:

    \[
    \boxed{\textbf{Gate1ZAtomDualMajorant}.}
    }
    \]

    Suppose that for the parameter \(\Lambda\) under consideration one can
    choose \(\theta_\Lambda\) such that:

    1.  \(P_{\theta_\Lambda}\) has the prescribed alternating sign on the
        components of \(Z_0\), after division by the fixed sign of
        \(Q^2R\);
    2.  every contact point of \(G_{\theta_\Lambda}\) with zero is simple only
        in the alternating pattern forced by that sign table;
    3.  \(G_{\theta_\Lambda}\ge0\) at one reference endpoint of each component
        of \(Z_0\).

    Then \(G_{\theta_\Lambda}\ge0\) on all of \(Z_0\).  The same statement
    applies to \(\theta_\lambda\) in the homogeneous case.

    If the alternation system has no solution, or if a contact point collides
    with a branch endpoint, a pole, another contact point, or a density sign
    boundary, the point is not in the compact non-pinched regular interior and
    is routed to Gate 3.  If the alternation system has a solution but the
    sign table above fails, then the \(Z_0\)-atomic branch remains a concrete
    obstruction; one must not declare Gate 1 closed.

    Strict lift gap in residual variables.

    The majorant alone is not enough; it must give the strict lifted gap in
    the correct direction.  With the present convention

    \[
    G_\theta=\theta\cdot V_S-V_\Pi,
    \]

    define the boundary and anchor residuals

    \[
    \boxed{
    G_\theta^{(b)}
    :=
    \theta\cdot b_S-b_\Pi
    =
    aG_\theta(u)+bG_\theta(v),
    }
    \tag{G1BoundaryResidual}
    \]

    and

    \[
    \boxed{
    G_\theta^{(c)}
    :=
    \theta\cdot\rho_S-\rho_\Pi.
    }
    \tag{G1AnchorResidual}
    \]

    Therefore the strict dual inequality for the \(\eta>0\) atom branch is
    exactly

    \[
    \theta_\Lambda\cdot(-b_S+\Lambda\rho_S)
    <
    -b_\Pi+\Lambda\rho_\Pi
    \]

    if and only if

    \[
    \boxed{
    G_{\theta_\Lambda}^{(b)}
    -\Lambda G_{\theta_\Lambda}^{(c)}
    >0.
    }
    \tag{G1StrictLiftEtaResidual}
    \]

    This sign is positive because \(G_\theta\) was defined as
    \(\theta\cdot V_S-V_\Pi\).  If the opposite residual convention is used,
    every displayed strict residual sign must be reversed.

    Similarly, the homogeneous strict inequality

    \[
    \theta_\lambda\cdot(\lambda\rho_S)<\lambda\rho_\Pi
    \]

    is equivalent to

    \[
    \boxed{
    \lambda G_{\theta_\lambda}^{(c)}<0.
    }
    \tag{G1StrictLiftHomResidual}
    \]

    We record the exact strict-gap lemma:

    \[
    \boxed{\textbf{Gate1StrictLiftGap}.}
    }
    \]

    Suppose the dual majorant lemma gives \(G_\theta\ge0\) on \(Z_0\).  If, in
    addition, (G1StrictLiftEtaResidual) holds for the corresponding
    \(\theta_\Lambda\), then the \(\eta>0\) \(Z_0\)-atomic certificate is
    excluded for that \(\Lambda\).  If
    (G1StrictLiftHomResidual) holds for the corresponding \(\theta_\lambda\),
    then the homogeneous \(Z_0\)-atomic certificate is excluded for that
    \(\lambda\).

    Equality in either strict residual is not an interior closure.  It must
    either be routed to Gate 3 as a contact degeneration, endpoint/pole
    collision, density-sign boundary, or chart-rank loss, or it remains an
    explicit Gate 1 obstruction.  Thus the remaining proof target after Step 5
    is completely finite and explicit: construct the majorants
    \(\theta_\Lambda,\theta_\lambda\), prove their \(P_\theta\)-sign tables on
    \(Z_0\), and verify the strict residual inequalities above.

    Gate 1 cone-envelope assembly.

    We now isolate the exact assembly statement.  This is the part of Gate 1
    that no longer contains hidden measure theory or informal cone language.

    \[
    \boxed{\textbf{Gate1ConeEnvelopeAssembly}.}
    }
    \]

    Assume the following three finite checks hold in the regular non-pinched
    moving chart:

    1.  the no-atom branch satisfies

        \[
        b_S=\Lambda\rho_S
        \quad\Longrightarrow\quad
        b_\Pi-\Lambda\rho_\Pi<0,
        \]

        with the degenerate cases routed to chart-rank boundary as in
        Gate1NoAtomCertificateExclusion;

    2.  for every \(\Lambda\in\mathbb R\), there is
        \(\theta_\Lambda\) such that

        \[
        G_{\theta_\Lambda}(x)\ge0\quad(x\in Z_0),
        \qquad
        G_{\theta_\Lambda}^{(b)}
        -\Lambda G_{\theta_\Lambda}^{(c)}>0;
        \]

    3.  for every \(\lambda\ne0\), there is \(\theta_\lambda\) such that

        \[
        G_{\theta_\lambda}(x)\ge0\quad(x\in Z_0),
        \qquad
        \lambda G_{\theta_\lambda}^{(c)}<0.
        \]

    Then no raw augmented Farkas certificate exists in the compact non-pinched
    regular rank-defect interior.

    Proof.  Let a minimal raw augmented certificate be given.  If its
    \(Z_0\)-atomic part is zero, the first assumption excludes it, except for
    the explicitly routed chart-rank boundary cases.

    Suppose now that the certificate has a nonzero \(Z_0\)-atomic part.  If
    \(\eta>0\), normalize \(\eta=1\) and put
    \(\Lambda=\lambda/\eta\).  The certificate equations give

    \[
    \sum_kw_kV_S(x_k)=-b_S+\Lambda\rho_S.
    \]

    By the majorant \(G_{\theta_\Lambda}\ge0\),

    \[
    \sum_kw_kV_\Pi(x_k)
    \le
    \theta_\Lambda\cdot(-b_S+\Lambda\rho_S).
    \]

    The strict residual inequality is exactly

    \[
    \theta_\Lambda\cdot(-b_S+\Lambda\rho_S)
    <
    -b_\Pi+\Lambda\rho_\Pi.
    \]

    Hence

    \[
    b_\Pi+\sum_kw_kV_\Pi(x_k)-\Lambda\rho_\Pi<0,
    \]

    contradicting the nonnegative lifted value required by Farkas.

    If \(\eta=0\), then \(\lambda\ne0\) for a nonzero certificate and

    \[
    \sum_kw_kV_S(x_k)=\lambda\rho_S.
    \]

    The majorant \(G_{\theta_\lambda}\ge0\) gives

    \[
    \sum_kw_kV_\Pi(x_k)\le\theta_\lambda\cdot(\lambda\rho_S),
    \]

    and the homogeneous strict residual gives

    \[
    \theta_\lambda\cdot(\lambda\rho_S)<\lambda\rho_\Pi.
    \]

    This contradicts the homogeneous lifted Farkas inequality.  Therefore no
    interior atomic certificate remains.  By finite-dimensional Farkas and
    conic Carathéodory, the reduced LP is feasible.

    Consequently the only unproved Gate 1 input after this assembly is not a
    cone or Farkas issue: it is the explicit construction of the majorants
    \(\theta_\Lambda,\theta_\lambda\), equivalently the \(P_\theta\)-sign
    tables and strict residual checks recorded above.  Once those finite
    checks are proved, Gate 1 may be marked PASS for the compact non-pinched
    regular \(g=2\) rank-defect interior.  Until then, this section is the
    closed assembly conditional on those checks, not an unconditional Gate 1
    pass.

    Hard-mouth finite margin formulation.

    The remaining \(P_\theta\)-majorant construction can be written as two
    scalar margin problems over the closed dual majorant cone

    \[
    \mathcal D_Z
    =
    \{\theta\in\mathbb R^4:\ G_\theta(x)\ge0\ \text{for all }x\in Z_0\}.
    \tag{G1DualCone}
    \]

    For the affine branch define

    \[
    \boxed{
    M_\eta(\Lambda)
    :=
    \sup_{\theta\in\mathcal D_Z}
    \left(
    G_\theta^{(b)}-\Lambda G_\theta^{(c)}
    \right).
    }
    \tag{G1AffineMargin}
    \]

    Then the \(\eta>0\) atomic branch is excluded for every \(\Lambda\) exactly
    when

    \[
    \boxed{
    M_\eta(\Lambda)>0
    \qquad(\Lambda\in\mathbb R),
    }
    \tag{G1AffineMarginTarget}
    \]

    with equality routed to a contact/boundary degeneration only if the
    maximizer has a boundary contact pattern.

    For the homogeneous branch the target is:

    \[
    \boxed{
    \begin{array}{ll}
    \inf_{\theta\in\mathcal D_Z}G_\theta^{(c)}<0,
    & \lambda>0,\\[0.3em]
    \sup_{\theta\in\mathcal D_Z}G_\theta^{(c)}>0,
    & \lambda<0.
    \end{array}
    }
    \tag{G1HomMarginTarget}
    \]

    These two margin inequalities are precisely the remaining hard mouth.  The
    derivative identity

    \[
    Q^2R\,G_\theta'=P_\theta
    \]

    converts each extremal \(\theta\) into an alternation/contact problem for
    the polynomial numerator

    \[
    P_\theta=\kappa Q^2-\sum_\gamma\theta_\gamma H_\gamma^{\rm rep}.
    \]

    Thus a proof-grade completion of Gate 1 must now do one of the following,
    and nothing weaker suffices:

    - solve the extremal majorant problem on each component of \(Z_0\) and
      prove (G1AffineMarginTarget), (G1HomMarginTarget);
    - or give an explicit signed product/determinant formula for the
      alternation system of \(P_\theta\) implying the same margins;
    - or exhibit a concrete non-boundary \(\Lambda\) or \(\lambda\) for which
      the margin target fails, which would be a genuine Gate 1 obstruction.

    Rank, Schur-complement identities, and \(Q_{\rm eff}\) finite off-cut
    tests do not by themselves imply these margins.  This is the exact point
    at which the compact non-pinched \(g=2\) rank-defect proof still needs a
    new sign calculation.

    Abstract insufficiency audit.

    The margin target above is not a formal consequence of the cone-envelope
    setup alone.  A four-point finite model already satisfies the same
    Farkas/majorant algebra and fails the required margin.  Take

    \[
    Z_0=\{x_1,x_2,x_3,x_4\},\qquad
    V_S(x_i)=e_i,\qquad
    V_\Pi(x_i)=0,
    \]

    and

    \[
    b_S=-(1,1,1,1),\qquad
    \rho_S=0,\qquad
    b_\Pi=1,\qquad
    \rho_\Pi=0.
    \]

    Then

    \[
    b_S+\sum_{i=1}^4V_S(x_i)=0
    \]

    is a positive raw augmented circuit, while the lifted value is

    \[
    b_\Pi+\sum_{i=1}^4V_\Pi(x_i)=1>0.
    \]

    Equivalently, \(\mathcal D_Z=\{\theta_i\ge0\}\), and at
    \(\Lambda=0\)

    \[
    M_\eta(0)=
    \sup_{\theta_i\ge0}\left(\theta\cdot b_S-b_\Pi\right)
    =
    -1<0.
    \]

    Thus the desired strict positive margin can fail even though the finite
    Farkas/cone formalism is perfectly consistent.  This finite model is not a
    claim about the actual moving-Schiffer columns; it proves the logical
    point that Gate 1 cannot be closed from the abstract cone-envelope
    reduction alone.

    Therefore the missing theorem is forced to use the real algebraic content
    of the moving finite-gap chart:

    \[
    \boxed{
    \textbf{MovingSchifferMajorantSignTheorem}.}
    }
    \]

    It must prove (G1AffineMarginTarget) and (G1HomMarginTarget) from the
    explicit repaired columns

    \[
    H_\gamma^{\rm rep}
    =
    QD\,\Delta_\gamma P
    -PD\,\Delta_\gamma Q
    -\frac12PQD_\gamma
    \]

    and the actual moving-chart linear system \(AX_\gamma=-r_\gamma\).  In
    proof-grade form this means either:

    1.  an explicit signed determinant/product formula for the alternation
        system of

        \[
        P_\theta=\kappa Q^2-\sum_\gamma\theta_\gamma H_\gamma^{\rm rep};
        \]

    2.  or a direct solution of the extremal majorant problem on the two
        components of \(Z_0\) proving the two margin inequalities.

    Without one of these two chart-specific sign proofs, writing
    "Gate 1 PASS" would be a logical error.

    First-order quotient obstruction.

    There is an even sharper obstruction to closing Gate 1 by a purely
    first-order endpoint-period determinant.  It comes from the moving-column
    algebra already proved above.

    Let

    \[
    \mathcal I_{\rm mov}=D\mathbb R[z]_{\le 2d-3}
    \]

    be the moving correction image and set

    \[
    E_\gamma=PQD_\gamma.
    \]

    In the quotient

    \[
    \mathcal Q_{\rm ep}
    =
    \mathbb R[z]_{\le 2d+1}/\mathcal I_{\rm mov},
    \]

    the endpoint classes \([E_\gamma]\) form the branch-endpoint interpolation
    basis.  Indeed, evaluation at the four branch endpoints gives

    \[
    E_\gamma(\delta)=0\quad(\delta\ne\gamma),
    \qquad
    E_\gamma(\gamma)=P(\gamma)Q(\gamma)D_\gamma(\gamma)\ne0.
    \]

    Hence every class in \(\mathcal Q_{\rm ep}\) is represented by its four
    endpoint values.  In particular,

    \[
    \boxed{
    [Q^2]
    =
    \sum_\gamma
    \frac{Q(\gamma)}
    {P(\gamma)D_\gamma(\gamma)}
    [E_\gamma].
    }
    \tag{G1PeriodInEndpointQuotient}
    \]

    This identity is independent of the choice of basis in the moving
    correction image.  It says that the period lift is not a new separated
    first-order column in the endpoint interpolation quotient; it is already a
    linear combination of the endpoint Schiffer classes.

    Therefore a strict first-order lifted orientation cannot be obtained from
    quotient rank or Schur-complement algebra alone.  Any strict margin in
    (G1AffineMarginTarget) must use information outside this quotient:

    - the actual non-quotient evaluation/contact pattern of \(G_\theta\) on
      \(Z_0\);
    - a signed determinant/product formula for the fully repaired
      \(P_\theta\)-alternation system;
    - or second-variation data beyond the first-order endpoint-period
      quotient.

    Thus the present hard mouth is resolved negatively at the level of
    first-order quotient algebra:

    \[
    \boxed{
    \text{first-order endpoint-period quotient data alone cannot close Gate 1.}
    }
    \tag{G1NoFirstOrderQuotientClosure}
    \]

    The remaining possible completions are precisely the two non-quotient
    alternatives above: a genuine MovingSchifferMajorantSignTheorem using the
    full \(Z_0\)-alternation/contact structure, or a second-variation theorem
    that handles the rank-defect fallback without relying on strict
    first-order lift orientation.

    Review audit.  The quotient identity (G1PeriodInEndpointQuotient) is an
    accepted obstruction to quotient/rank/Schur-only closures.  It does not
    by itself refute the non-quotient \(P_\theta\)-alternation route, because
    that route uses actual values and contacts on \(Z_0\), not only endpoint
    classes in \(\mathcal Q_{\rm ep}\).  Any numerical probe of this route
    must therefore use the repaired moving-chart columns
    \(H_\gamma^{\rm rep}\) and the actual \(AX_\gamma=-r_\gamma\) rows; the
    collapsed fixed-\(Q\) endpoint table is audit-only and cannot be used as a
    proof-grade test bed.

    2026-05-07 Gate 1 review correction: branch split.

    The current review conclusion is accepted with this scope: Gate 1 is not
    an unconditional PASS, and the endpoint-period quotient identity rules out
    only quotient/rank/Schur-only closures.  It does not prove that every
    first-order approach is impossible; the remaining first-order route must
    use the actual \(Z_0\)-majorant/contact data.

    The rank-defect fallback must therefore be split into two branches.

    No-atom branch.  If the \(Z_0\)-atomic measure vanishes, the certificate
    equations reduce to

    \[
    \eta b_S-\lambda\rho_S=0.
    \]

    In the nondegenerate interior a nonzero certificate has \(\eta>0\).  After
    normalization, with \(\Lambda=\lambda/\eta\),

    \[
    b_S=\Lambda\rho_S.
    \]

    Hence the no-atom branch is a finite collinearity test: if
    \(b_S\notin\mathbb R\rho_S\), no such certificate exists; if
    \(b_S=\Lambda\rho_S\), the lifted scalar must satisfy

    \[
    b_\Pi-\Lambda\rho_\Pi<0
    \]

    or else this remains a genuine finite obstruction.  Degenerate cases such
    as \(b_S=\rho_S=0\) are chart-rank boundary cases and route to Gate 3.

    \(Z_0\)-atomic branch.  If the certificate has positive \(Z_0\)-atomic
    mass, the regularized point-row Riesz load has positive logarithmic
    blow-up, so a finite negative \(Q_{\rm eff}\) lift cannot directly exclude
    this branch.  The correct object is the cone-envelope majorant problem:

    \[
    \Phi_Z(y)
    =
    \sup\left\{\sum_k w_kV_\Pi(x_k):
    \sum_kw_kV_S(x_k)=y,\ w_k>0,\ x_k\in Z_0\right\}.
    \]

    The affine atom branch is excluded precisely by

    \[
    \Phi_Z(-b_S+\Lambda\rho_S)<-b_\Pi+\Lambda\rho_\Pi
    \qquad(\forall\Lambda\in\mathbb R),
    \]

    and the homogeneous atom branch by

    \[
    \Phi_Z(\lambda\rho_S)<\lambda\rho_\Pi
    \qquad(\lambda\ne0).
    \]

    Equivalently, one must construct dual majorants

    \[
    G_\theta=\theta\cdot V_S-V_\Pi\ge0\quad\text{on }Z_0
    \]

    with the strict residual inequalities recorded in
    (G1AffineMarginTarget) and (G1HomMarginTarget).  Through
    \(Q^2R\,G_\theta'=P_\theta\), this is the
    \(P_\theta\)-alternation/sign-table problem for the repaired moving
    Schiffer columns.  This is the next proof obligation; it is not replaced
    by \(Q_{\rm eff}\), abstract Farkas, or quotient rank.

    2026-05-07 route audit: what can still be tried.

    The review statement that Gate 1 is blocked is correct if it means
    "blocked as an unconditional proof."  Two qualifications are important.
    First, the no-atom branch is not automatically proved away; it is reduced
    to the finite collinearity test above and must still be checked from the
    repaired columns.  Second, the quotient obstruction kills only
    endpoint-period quotient and Schur-only arguments.  It does not kill a
    proof using actual \(Z_0\)-values and contacts.

    The live Gate 1 attempts are therefore ordered as follows.

    1.  **Primary route: \(Z_0\)-dual majorant.**  Prove
        MovingSchifferMajorantSignTheorem by constructing
        \(\theta_\Lambda,\theta_\lambda\in\mathcal D_Z\), deriving the
        \(P_\theta\)-alternation/contact pattern on the two components of
        \(Z_0\), and checking the strict boundary/anchor residuals.  This is
        the only first-order route that uses the information lost in
        \(\mathcal Q_{\rm ep}\).

    2.  **Finite no-atom check.**  Compute \(b_S,\rho_S,b_\Pi,\rho_\Pi\) from
        the repaired moving Schiffer columns.  If \(b_S\notin\mathbb R\rho_S\)
        the no-atom branch is absent; if \(b_S=\Lambda\rho_S\), the scalar
        \(b_\Pi-\Lambda\rho_\Pi\) must be strictly negative.  Failure gives a
        concrete finite obstruction rather than a formal proof.

    3.  **Numerical margin oracle.**  Before trying to write a theorem, build
        a diagnostic solver for
        \[
        M_\eta(\Lambda)=
        \sup_{\theta\in\mathcal D_Z}
        \bigl(G_\theta^{(b)}-\Lambda G_\theta^{(c)}\bigr)
        \]
        and the homogeneous margins.  This must use
        \(H_\gamma^{\rm rep}\) and the actual \(AX_\gamma=-r_\gamma\) rows,
        not the fixed-\(Q\) collapsed endpoint table.  A positive numerical
        margin suggests the majorant theorem; a negative margin supplies a
        candidate obstruction.

    4.  **Explicit product route.**  Try to prove a signed
        determinant/product formula for the \(P_\theta\)-alternation system.
        This cannot be a quotient-rank proof; it must include the moving
        correction columns, the equality row \(\rho\), and the actual
        contact/evaluation rows on \(Z_0\).

    5.  **Second-variation route.**  Use \(Q_{\rm eff}\) only for the no-atom
        or off-cut finite subcase.  The \(Z_0\)-atomic branch is not directly
        killed by finite \(Q_{\rm eff}\) because the point-row Riesz load has
        positive logarithmic blow-up.  Any second-variation attack on the
        atomic branch needs a new mechanism, not the old finite lift.

    These are attempts, not completed gates.  Gate 2 may be used only after
    one of the Gate 1 attempts produces reduced LP feasibility.

    2026-05-07 mainline continuation: certified majorant oracle.

    The existing two-interval diagnostic scripts solve a corrected
    one-cut/two-interval ansatz and check its sign chart.  They do not output
    the repaired Gate 1 data

    \[
    H_\gamma^{\rm rep},\quad AX_\gamma=-r_\gamma,\quad
    V_S,\rho_S,b_S,V_\Pi,\rho_\Pi,b_\Pi.
    \]

    Therefore those scripts cannot, by themselves, certify
    MovingSchifferMajorantSignTheorem.  A proof-grade numerical or symbolic
    continuation must first extract the repaired moving-Schiffer data.  Once
    that data is available, the remaining verification is finite and has the
    following soundness theorem.

    \[
    \boxed{\textbf{CertifiedMajorantOracleSoundness}.}
    }
    \]

    Suppose the repaired moving chart supplies interval enclosures for:

    1.  \(V_S(x),V_\Pi(x)\) on each component of \(Z_0\);
    2.  \(\rho_S,\rho_\Pi,b_S,b_\Pi\);
    3.  \(P_\theta=\kappa Q^2-\sum_\gamma\theta_\gamma
        H_\gamma^{\rm rep}\) and \(Q^2R\) on those components;
    4.  a finite cover of the projective affine parameter
        \((\Lambda:1)\in\mathbb RP^1\), including the point at infinity for
        the homogeneous limit.

    Assume that on every box of this cover the oracle constructs interval
    coefficients \(\theta\) satisfying:

    \[
    G_\theta(x)=\theta\cdot V_S(x)-V_\Pi(x)\ge0
    \quad(x\in Z_0),
    \tag{G1OracleMajorant}
    \]

    with nonnegativity certified either by direct interval lower bounds on
    \(G_\theta\), or by a \(P_\theta/(Q^2R)\)-sign table plus endpoint/contact
    lower bounds; and also

    \[
    G_\theta^{(b)}-\Lambda G_\theta^{(c)}>0
    \tag{G1OracleAffineGap}
    \]

    throughout the finite-\(\Lambda\) part of the box, while the projective
    infinity boxes certify the homogeneous alternatives

    \[
    \inf_{\theta\in\mathcal D_Z}G_\theta^{(c)}<0,
    \qquad
    \sup_{\theta\in\mathcal D_Z}G_\theta^{(c)}>0.
    \tag{G1OracleHomGap}
    \]

    Then MovingSchifferMajorantSignTheorem holds in the regular non-pinched
    chart, except for boxes where a certified denominator separation,
    contact separation, density positivity, or chart-rank interval fails; each
    such failed box is a Gate 3 boundary candidate, not an interior Gate 1
    pass.

    Proof.  The interval inequalities (G1OracleMajorant) place every produced
    \(\theta\) in the dual cone \(\mathcal D_Z\).  For each finite
    \(\Lambda\), (G1OracleAffineGap) is exactly
    \(M_\eta(\Lambda)>0\) with a witnessed feasible dual point.  For the
    projective infinity directions, (G1OracleHomGap) is exactly
    (G1HomMarginTarget).  Gate1ConeEnvelopeAssembly then excludes every
    \(Z_0\)-atomic Farkas certificate.  The no-atom certificates are handled
    separately by Gate1NoAtomCertificateExclusion.  Hence finite-dimensional
    Farkas leaves no certificate, so the reduced LP is feasible.  The only
    exceptions are boxes where the interval hypotheses required to interpret
    the repaired chart fail; by definition these are chart-rank, contact,
    endpoint/pole collision, or density-boundary cases routed to Gate 3.
    \(\square\)

    This theorem is the current mainline bridge.  It does not prove the
    margins by itself; it states exactly what a rigorous computation or
    signed alternation proof must certify.  The next concrete task is to
    derive the repaired moving-Schiffer data extractor for \(H_\gamma^{\rm rep}\)
    and \(AX_\gamma=-r_\gamma\).  Without that extractor, any numerical
    margin calculation is testing the wrong object.

    Repaired moving-Schiffer data extractor.

    We now make that extractor explicit.  This is still linear algebra, not a
    sign theorem, but it fixes the exact data that every Gate 1 oracle must
    consume.

    Fix the regular moving chart data

    \[
    D(z)=\prod_{\delta\in\Gamma}(z-\delta),
    \qquad
    \Gamma=\{\alpha_1,\beta_1,\alpha_2,\beta_2\},
    \]

    and the numerator/pole pair \(P,Q\) with \(Q\) monic and separated from
    \(J\cup\{u,c,v\}\).  Let

    \[
    \mathcal X=\mathcal X_P\oplus\mathcal X_Q
    \]

    be the allowed coefficient space for \((\Delta P,\Delta Q)\) after the
    monic-\(Q\) gauge has removed the leading \(Q\)-coefficient.  Define the
    moving correction map

    \[
    \boxed{
    B(\Delta P,\Delta Q)=QD\,\Delta P-PD\,\Delta Q.
    }
    \tag{G1ExtractorB}
    \]

    Let

    \[
    h_\gamma^{raw}=-\frac12PQD_\gamma,
    \qquad D_\gamma=D/(z-\gamma).
    \]

    The chart rows are a fixed ordered list

    \[
    \ell=(\ell_1,\ldots,\ell_N)
    \]

    consisting of the rows that must remain fixed under an endpoint Schiffer
    move: zero mass, the chosen free-period/filling convention if it is not
    quotiented, moving-\(Q\) gauge rows, pole/residue-state rows, and any
    regular chart equality rows.  The anchor row \(R_c\) is not in this list;
    it is corrected later by the boundary-neutral bump pair.  In the regular
    non-pinched chart \(N=\dim\mathcal X\) and the square matrix

    \[
    \boxed{
    A_{\ell,X}=\ell(BX)
    }
    \tag{G1ExtractorA}
    \]

    is invertible.  If it is not invertible, the point is a chart-rank
    boundary case and is routed to Gate 3.

    For each endpoint \(\gamma\), set

    \[
    r_\gamma=\ell(h_\gamma^{raw})
    \tag{G1ExtractorR}
    \]

    and solve

    \[
    \boxed{
    AX_\gamma=-r_\gamma.
    }
    \tag{G1ExtractorSolve}
    \]

    Then define

    \[
    \boxed{
    H_\gamma^{rep}=h_\gamma^{raw}+BX_\gamma
    =
    -\frac12PQD_\gamma-BA^{-1}r_\gamma.
    }
    \tag{G1ExtractorH}
    \]

    The endpoint Cauchy column and potential column are

    \[
    C_\gamma(z)=\frac{H_\gamma^{rep}(z)}{Q(z)^2R(z)},
    \qquad
    V_\gamma(s)=\int_s^\infty C_\gamma(y)\,dy
    \]

    with the usual continuous boundary value on \(Z_0\).  The period column is

    \[
    H_\Pi=\kappa Q^2,\qquad
    C_\Pi=\frac{\kappa}{R},\qquad
    V_\Pi(s)=\int_s^\infty C_\Pi(y)\,dy,
    \]

    with the sign of \(\kappa\) chosen to match the oriented positive
    period-transfer density.  Finally set

    \[
    \boxed{
    \rho_j=-C_j(c),\qquad
    b_j=aV_j(u)+bV_j(v),
    \qquad j\in\{\Pi\}\cup\Gamma.
    }
    \tag{G1ExtractorRows}
    \]

    \[
    V_S=(V_{\alpha_1},V_{\beta_1},V_{\alpha_2},V_{\beta_2})^T,
    \quad
    \rho_S=(\rho_{\alpha_1},\rho_{\beta_1},\rho_{\alpha_2},\rho_{\beta_2})^T,
    \quad
    b_S=(b_{\alpha_1},b_{\beta_1},b_{\alpha_2},b_{\beta_2})^T.
    \]

    The extractor has the following correctness property.

    \[
    \boxed{\textbf{RepairedSchifferDataExtractorSoundness}.}
    }
    \]

    If \(A\) is invertible, then:

    1.  every repaired endpoint column satisfies all moving-chart rows,

        \[
        \ell(H_\gamma^{rep})=0;
        \]

    2.  in particular, if the zero-mass row is included in \(\ell\), then
        \(R_0(G_\gamma)=0\);

    3.  the anchor/equality correction data are exactly the rows
        \(\rho_\gamma=-C_\gamma(c)\), because \(R_c\) was deliberately not
        included in \(A\);

    4.  the reduced boundary entries are exactly
        \(b_\gamma=aV_\gamma(u)+bV_\gamma(v)\), since the equality correctors
        are chosen boundary-neutral.

    Proof.  By construction

    \[
    \ell(H_\gamma^{rep})
    =
    \ell(h_\gamma^{raw})+\ell(BX_\gamma)
    =
    r_\gamma+AX_\gamma
    =
    0.
    \]

    The zero-mass statement is the zero-mass component of this row identity.
    Since \(R_c\) is not a row of \(A\), it is not forced by the moving-chart
    solve and remains precisely the scalar \(-C_\gamma(c)\) that the
    boundary-neutral bump correction removes.  Boundary neutrality gives
    \(B_{\rm red}(G_\gamma)=B_{\rm safe}(G_\gamma)\), and the anchored neck
    identity gives \(B_{\rm safe}(G_\gamma)=aV_\gamma(u)+bV_\gamma(v)\).
    This proves the extractor formulas.  \(\square\)

    Thus the data needed by CertifiedMajorantOracleSoundness are now
    specified without ambiguity.  The next proof task is not to define more
    rows, but to either evaluate this extractor in the concrete moving chart
    or prove a signed \(P_\theta\)-alternation theorem from the extracted
    columns.

    Finite-contact alternation reduction.

    We can now remove another layer of infinitary language from
    MovingSchifferMajorantSignTheorem.  The cone \(\mathcal D_Z\) is defined
    by the continuum of inequalities \(G_\theta(x)\ge0\), but an extremal
    failure or extremal proof is witnessed by finitely many contacts.

    Let

    \[
    \mathcal D_Z
    =
    \{\theta\in\mathbb R^4:\theta\cdot V_S(x)-V_\Pi(x)\ge0
    \ \text{for all }x\in Z_0\}.
    \]

    For a fixed finite \(\Lambda\), define the affine residual functional

    \[
    L_\Lambda(\theta)=G_\theta^{(b)}-\Lambda G_\theta^{(c)}.
    \]

    If \(M_\eta(\Lambda)=\sup_{\theta\in\mathcal D_Z}L_\Lambda(\theta)\) is
    finite and not attained, then after normalizing a maximizing sequence in
    projective \(\theta\)-space one obtains either a nonzero recession
    direction in \(\mathcal D_Z\), or a boundary/contact degeneration.  The
    former is exactly the positive-lift recession obstruction already recorded;
    the latter routes to Gate 3.  Thus an interior proof or obstruction may be
    studied at an extremal \(\theta_*\in\mathcal D_Z\).

    At an extremal \(\theta_*\), choose a minimal active contact set

    \[
    X=\{x_1,\ldots,x_m\}\subset Z_0,
    \qquad
    G_{\theta_*}(x_i)=0,
    \]

    whose normal cone contains the affine objective row.  By conic
    Carathéodory in \(\mathbb R^4\), one may take \(m\le4\) for the affine
    branch after the boundary/anchor row has been fixed; for the homogeneous
    projective branch the corresponding raw circuit uses at most five
    contacts.  Equivalently, there are nonnegative weights \(w_i\), not all
    zero, such that the KKT normal-cone equation reads

    \[
    \nabla_\theta L_\Lambda
    =
    -\sum_{i=1}^m w_i V_S(x_i)
    \]

    in the affine case.  The minus sign is essential: the constraints are
    \(G_\theta(x)\ge0\), so the outward normal cone is generated by
    \(-V_S(x_i)\), not \(+V_S(x_i)\).  Equivalently, the primal atomic equation
    is

    \[
    \sum_{i=1}^m w_iV_S(x_i)=-b_S+\Lambda\rho_S.
    \tag{G1AffineKKT}
    \]

    The corresponding homogeneous/projective version is obtained by replacing
    \(-b_S+\Lambda\rho_S\) with the ray \(\lambda\rho_S\).  If an active
    contact lies in the interior of a
    component of \(Z_0\), then the contact is stationary:

    \[
    G_{\theta_*}'(x_i)=0.
    \]

    Using \(Q^2R\,G_{\theta_*}'=P_{\theta_*}\), every interior contact gives

    \[
    P_{\theta_*}(x_i)=0.
    \]

    If the contact is an endpoint contact, the stationarity condition is
    replaced by the one-sided sign condition for
    \(P_{\theta_*}/(Q^2R)\).  If two contacts collide, if a stationary contact
    hits a branch endpoint or pole, or if the sign of \(Q^2R\) is not
    separated on the component, the case is a Gate 3 boundary/contact
    degeneration.

    Hence the remaining sign theorem is finite:

    \[
    \boxed{\textbf{FiniteContactMajorantReduction}.}
    }
    \]

    To prove MovingSchifferMajorantSignTheorem in the regular interior it is
    enough to handle all nondegenerate contact patterns with:

    1.  at most four affine contacts, or at most five homogeneous/projective
        contacts;
    2.  equations \(G_\theta(x_i)=0\) and, for interior contacts,
        \(P_\theta(x_i)=0\);
    3.  the componentwise sign table for \(P_\theta/(Q^2R)\) between contacts;
    4.  the KKT cone equation
        \(\sum_iw_iV_S(x_i)=-b_S+\Lambda\rho_S\) in the affine branch, or
        \(\sum_iw_iV_S(x_i)=\lambda\rho_S\) in the homogeneous branch;
    5.  the strict residual inequality \(L_\Lambda(\theta)>0\), or the
        homogeneous alternatives for \(G_\theta^{(c)}\).

    Proof.  The normal-cone statement is the KKT condition for maximizing a
    linear functional over the closed convex cone \(\mathcal D_Z\) after the
    recession and boundary cases have been separated.  Since the active
    inequalities are \(G_\theta(x)\ge0\), their outward normals are
    \(-V_S(x)\); this gives (G1AffineKKT), with the same sign convention as
    the primal atomic Farkas equation.  Carathéodory reduces the active set
    to at most the ambient dimension, with one extra point in the homogeneous
    projective circuit.  Interior contact stationarity follows because a
    nonnegative \(C^1\) function attaining a zero minimum in the interior has
    derivative zero.  The derivative identity gives
    \(P_\theta(x_i)=0\).  The sign table between consecutive contacts is
    exactly the assertion that \(G_\theta\) cannot cross below zero.  This
    proves the reduction.  \(\square\)

    The practical consequence is important: the next computation need not
    scan all atomic measures on \(Z_0\).  It must enumerate finite contact
    patterns, solve the corresponding \(G=0\), \(P=0\) system using the
    extracted \(H_\gamma^{rep}\), and certify the residual sign.  A failure of
    any nondegenerate pattern gives a concrete Gate 1 obstruction; a
    degeneracy routes to Gate 3.

    Contact-pattern ledger.

    We now spell out the finite enumeration implied by
    FiniteContactMajorantReduction.  Write the active zero set as the disjoint
    union of its regular components

    \[
    Z_0=Z_L\cup Z_R,
    \qquad
    Z_\nu=[s_\nu^-,s_\nu^+]\quad(\nu=L,R),
    \]

    after deleting empty components.  Endpoint contact means contact at one of
    the four points \(s_\nu^\pm\); interior contact means contact in
    \((s_\nu^-,s_\nu^+)\).

    A contact pattern is the data

    \[
    \mathfrak p=
    \bigl(m_L^-,m_L^0,m_L^+;m_R^-,m_R^0,m_R^+;\epsilon\bigr),
    \]

    where \(m_\nu^\pm\in\{0,1\}\) records whether the endpoint \(s_\nu^\pm\)
    is active, \(m_\nu^0\) is the number of interior contacts on \(Z_\nu\),
    and \(\epsilon\in\{\mathrm{aff},\mathrm{hom}\}\) records whether the
    finite-\(\Lambda\) affine branch or the homogeneous/projective branch is
    being tested.  The total contact count is

    \[
    |\mathfrak p|=
    m_L^-+m_L^0+m_L^++m_R^-+m_R^0+m_R^+.
    \]

    The admissible counts are

    \[
    |\mathfrak p|\le4\quad(\epsilon=\mathrm{aff}),
    \qquad
    |\mathfrak p|\le5\quad(\epsilon=\mathrm{hom}).
    \]

    For each interior contact introduce a variable \(x_i\) constrained to the
    corresponding open component.  For each endpoint contact the point is
    fixed.  The contact equations are:

    \[
    G_\theta(x_i)=0
    \quad\text{for every contact,}
    \tag{G1ContactEq}
    \]

    and

    \[
    P_\theta(x_i)=0
    \quad\text{for every interior contact.}
    \tag{G1StationaryEq}
    \]

    Endpoint contacts instead carry the one-sided derivative sign:

    \[
    \pm\,\frac{P_\theta(s_\nu^\pm)}{Q(s_\nu^\pm)^2R(s_\nu^\pm)}\ge0,
    \tag{G1EndpointContactSign}
    \]

    with the sign chosen so that \(G_\theta\) increases into the component
    from a left endpoint and decreases into the component toward a right
    endpoint.  Between consecutive contacts on each component the sign of
    \(P_\theta/(Q^2R)\) must force \(G_\theta\) to stay nonnegative; this is
    the interval sign-table condition.

    The unknowns for an affine pattern are

    \[
    \theta\in\mathbb R^4,\qquad
    \Lambda\in\mathbb R,\qquad
    \{x_i\}_{\text{interior contacts}},
    \]

    together with optional positive normal-cone weights if one wants to solve
    the KKT form rather than the contact form.  The output inequality is

    \[
    L_\Lambda(\theta)=G_\theta^{(b)}-\Lambda G_\theta^{(c)}>0.
    \tag{G1PatternAffineResidual}
    \]

    For homogeneous/projective patterns, replace \(\Lambda\) by the projective
    direction \(\lambda=\pm1\) and certify the appropriate side of
    \(G_\theta^{(c)}\):

    \[
    G_\theta^{(c)}<0\quad(\lambda>0),
    \qquad
    G_\theta^{(c)}>0\quad(\lambda<0).
    \tag{G1PatternHomResidual}
    \]

    A pattern is regular if all interior contacts are distinct and stay inside
    their assigned components, no contact hits a \(Q\)-pole or branch endpoint
    except by an endpoint-contact label, \(Q^2R\) has separated sign on every
    open subinterval between contacts, and the moving-chart matrix \(A\)
    remains invertible.  Failure of any regularity condition routes to Gate 3.

    Therefore the actual Gate 1 computational/proof obligation is the finite
    statement:

    \[
    \boxed{\textbf{ContactPatternVerification}.}
    }
    \]

    For every regular pattern \(\mathfrak p\), every solution of
    (G1ContactEq), (G1StationaryEq), the interval sign-table conditions, and
    the relevant KKT cone equation satisfies the strict residual
    (G1PatternAffineResidual) or
    (G1PatternHomResidual).  If the pattern has no solution, it is harmless;
    if it degenerates, it routes to Gate 3; if it has a regular solution with
    non-strict or wrong residual, that solution is a genuine Gate 1
    obstruction.

    This is the most concrete form of the main line so far: enumerate
    \(\mathfrak p\), solve finite equations, verify interval sign tables and
    residuals.

    Normalized contact system.

    For each regular contact pattern, the equations can be normalized so that
    the unknown \(\theta\) is solved by a square linear system once the contact
    locations and the branch parameter are fixed.

    Let \(X=(x_1,\ldots,x_r)\) be the ordered interior contacts of the pattern,
    and let \(Y=(y_1,\ldots,y_e)\) be the fixed endpoint contacts.  Define the
    contact-evaluation matrix

    \[
    \mathcal E_{\mathfrak p}(X,Y)
    =
    \begin{pmatrix}
    V_S(y_1)^T\\
    \vdots\\
    V_S(y_e)^T\\
    V_S(x_1)^T\\
    \vdots\\
    V_S(x_r)^T
    \end{pmatrix},
    \]

    and the corresponding period vector

    \[
    v_{\Pi,\mathfrak p}(X,Y)
    =
    \begin{pmatrix}
    V_\Pi(y_1)\\
    \vdots\\
    V_\Pi(y_e)\\
    V_\Pi(x_1)\\
    \vdots\\
    V_\Pi(x_r)
    \end{pmatrix}.
    \]

    The contact equations \(G_\theta=0\) are

    \[
    \mathcal E_{\mathfrak p}(X,Y)\theta
    =
    v_{\Pi,\mathfrak p}(X,Y).
    \tag{G1ContactLinear}
    \]

    If \(|\mathfrak p|=4\) and
    \(\det\mathcal E_{\mathfrak p}\ne0\), then

    \[
    \boxed{
    \theta_{\mathfrak p}(X,Y)
    =
    \mathcal E_{\mathfrak p}(X,Y)^{-1}
    v_{\Pi,\mathfrak p}(X,Y).
    }
    \tag{G1ThetaPattern}
    \]

    Patterns with fewer than four contacts are treated by adding the affine
    extremality row \(\nabla_\theta L_\Lambda\) or by passing to a lower
    support circuit; if the augmentation determinant vanishes, this is a
    lower-dimensional contact pattern or a Gate 3 degeneration.  Patterns
    with more than four affine contacts are not minimal and reduce by
    Carathéodory.

    After solving for \(\theta_{\mathfrak p}\), each interior contact must also
    satisfy stationarity:

    \[
    \boxed{
    P_{\theta_{\mathfrak p}}(x_i)=0
    \quad(i=1,\ldots,r).
    }
    \tag{G1PatternStationarySystem}
    \]

    Thus a full affine pattern check reduces to:

    1.  solve the finite nonlinear system (G1PatternStationarySystem) in the
        ordered box for \(X\);
    2.  verify the endpoint one-sided signs and the sign table for
        \(P_{\theta_{\mathfrak p}}/(Q^2R)\) on every subinterval between
        contacts;
    3.  verify KKT compatibility: there are weights \(w_i\ge0\), positive on
        the minimal active contacts, such that

        \[
        \boxed{
        \sum_iw_iV_S(z_i)=-b_S+\Lambda\rho_S,
        }
        \tag{G1PatternKKT}
        \]

        where \(z_i\) ranges over the active contacts.  If this cone equation
        fails, the contact pattern is not extremal for that value of
        \(\Lambda\) and cannot witness the affine branch;
    4.  verify the residual

        \[
        L_\Lambda(\theta_{\mathfrak p})>0.
        \]

    For homogeneous/projective patterns with five contacts, one uses the
    homogeneous augmented matrix

    \[
    \mathcal E_{\mathfrak p}^{hom}(X,Y)
    =
    \begin{pmatrix}
    V_S(z_1)^T&-V_\Pi(z_1)\\
    \vdots&\vdots\\
    V_S(z_5)^T&-V_\Pi(z_5)
    \end{pmatrix},
    \]

    where \(z_i\) ranges over all contacts.  A nonzero null vector

    \[
    (\theta_{\mathfrak p},1)
    \quad\text{or}\quad
    (\theta_{\mathfrak p},-1)
    \]

    gives the projective majorant normalization.  The same stationarity and
    sign-table checks apply.  The homogeneous KKT compatibility is

    \[
    \boxed{
    \sum_iw_iV_S(z_i)=\lambda\rho_S,
    \qquad
    w_i\ge0,\quad\lambda\in\{+1,-1\},
    }
    \tag{G1PatternHomKKT}
    \]

    after projective rescaling.  For \(\lambda>0\) the residual check is
    \(G_{\theta_{\mathfrak p}}^{(c)}<0\); for \(\lambda<0\) it is
    \(G_{\theta_{\mathfrak p}}^{(c)}>0\).

    The regularity determinant for a contact pattern is therefore:

    \[
    \boxed{
    \det\mathcal E_{\mathfrak p}\ne0
    \quad\text{(affine four-contact case)}
    }
    \tag{G1PatternDet}
    \]

    or the corresponding rank-four condition for
    \(\mathcal E_{\mathfrak p}^{hom}\).  If this determinant vanishes, the
    pattern is not a regular isolated contact pattern; it either reduces to a
    smaller support pattern or routes to Gate 3.

    This gives a deterministic checklist for each pattern: determinant,
    stationarity, interval sign table, KKT compatibility, and residual.  No
    measure-theoretic fallback remains inside Gate 1 after these finite
    checks.

    Weighted contact obstruction system.

    The previous normalization can be turned into an exact obstruction
    certificate.  This is the useful endpoint of the current Gate 1 reduction:
    a regular failure of MovingSchifferMajorantSignTheorem is equivalent to a
    finite weighted contact system.

    In the affine branch, a regular obstruction consists of:

    \[
    \Lambda\in\mathbb R,\qquad
    \theta\in\mathbb R^4,\qquad
    z_i\in Z_0,\qquad
    w_i>0,
    \]

    with at most four active contacts, satisfying

    \[
    G_\theta(z_i)=0,
    \tag{G1WContact}
    \]

    \[
    \sum_iw_iV_S(z_i)=-b_S+\Lambda\rho_S,
    \tag{G1WAffineKKT}
    \]

    and, for every interior contact,

    \[
    P_\theta(z_i)=0.
    \tag{G1WStationary}
    \]

    Endpoint contacts satisfy the corresponding one-sided derivative sign,
    and the sign table of \(P_\theta/(Q^2R)\) between consecutive contacts
    must certify

    \[
    G_\theta(x)\ge0\qquad(x\in Z_0).
    \tag{G1WSignTable}
    \]

    Finally, it must violate the desired strict margin:

    \[
    L_\Lambda(\theta)
    =
    G_\theta^{(b)}-\Lambda G_\theta^{(c)}
    \le0.
    \tag{G1WAffineBadResidual}
    \]

    In the homogeneous branch, replace (G1WAffineKKT) by

    \[
    \sum_iw_iV_S(z_i)=\lambda\rho_S,
    \qquad
    \lambda\in\{+1,-1\},
    \tag{G1WHomKKT}
    \]

    use at most five contacts, and replace the residual failure by

    \[
    G_\theta^{(c)}\ge0\quad(\lambda=+1),
    \qquad
    G_\theta^{(c)}\le0\quad(\lambda=-1).
    \tag{G1WHomBadResidual}
    \]

    Lemma (weighted obstruction extraction).  Suppose the regular
    non-pinched \(g=2\) rank-defect Gate 1 branch is not excluded by the
    majorant criterion.  Then either the case is a Gate 3 boundary/contact
    degeneration, or there exists an affine or homogeneous weighted contact
    obstruction satisfying the corresponding equations above.

    Proof.  If the affine margin fails for some finite \(\Lambda\), then
    \(M_\eta(\Lambda)\le0\) or the supremum defining \(M_\eta(\Lambda)\) is
    not properly attained.  Non-attainment gives either a positive-lift
    recession ray or a contact/chart degeneration; these have already been
    separated as Gate 3 routes or explicit obstructions.  In the remaining
    regular case, take an extremizer \(\theta\in\mathcal D_Z\).  The active
    contact set \(G_\theta=0\) is nonempty; otherwise one can perturb
    \(\theta\) in the objective direction and improve the residual.  Applying
    the KKT normal-cone condition and conic Carathéodory gives a minimal
    active set with at most four contacts and weights satisfying
    (G1WAffineKKT).  Interior contacts are stationary because \(G_\theta\ge0\)
    and \(G_\theta(z_i)=0\), giving (G1WStationary).  Endpoint contacts carry
    the one-sided sign.  The interval sign table is exactly the remaining
    statement that \(\theta\in\mathcal D_Z\).  Since the margin failed,
    (G1WAffineBadResidual) holds.

    The homogeneous branch is identical after projectivizing the objective
    direction.  Maximizing \(G_\theta^{(c)}\) gives the ray
    \(-\rho_S\), while minimizing \(G_\theta^{(c)}\) gives the ray
    \(+\rho_S\); after rescaling this is (G1WHomKKT) with
    \(\lambda=\pm1\).  Carathéodory in the projective raw circuit gives at
    most five contacts.  The residual failures are precisely
    (G1WHomBadResidual).  \(\square\)

    Therefore Gate 1 can be attacked pattern-by-pattern: for each contact
    pattern, prove the weighted obstruction system has no regular solution.
    Any regular solution with bad residual is no longer a heuristic failure;
    it is a concrete rank-defect obstruction.

    Review audit: contact determinants and the envelope correction.

    The latest Gate 1 review is accepted with the following scope.  The
    reduction to finite contact patterns is correct, and the residual for a
    fixed affine four-contact pattern has the following exact determinant
    form.  For contacts \(z_1,\ldots,z_4\), set

    \[
    E_{\mathfrak p}=
    \begin{pmatrix}
    V_S(z_1)^T\\
    V_S(z_2)^T\\
    V_S(z_3)^T\\
    V_S(z_4)^T
    \end{pmatrix},
    \qquad
    v_{\Pi,\mathfrak p}=
    \begin{pmatrix}
    V_\Pi(z_1)\\
    V_\Pi(z_2)\\
    V_\Pi(z_3)\\
    V_\Pi(z_4)
    \end{pmatrix}.
    \]

    If \(E_{\mathfrak p}\) is invertible, the contact equations give
    \(\theta_{\mathfrak p}=E_{\mathfrak p}^{-1}v_{\Pi,\mathfrak p}\).  With

    \[
    \ell_\Lambda^T=b_S^T-\Lambda\rho_S^T,
    \qquad
    \ell_{\Pi,\Lambda}=b_\Pi-\Lambda\rho_\Pi,
    \]

    the affine residual satisfies

    \[
    \boxed{
    L_\Lambda(\theta_{\mathfrak p})
    =
    -
    \frac{
    \det
    \begin{pmatrix}
    E_{\mathfrak p}&v_{\Pi,\mathfrak p}\\
    \ell_\Lambda^T&\ell_{\Pi,\Lambda}
    \end{pmatrix}
    }{
    \det E_{\mathfrak p}
    }.
    }
    \tag{G1AffineResidualDet}
    \]

    This follows from the Schur determinant identity and is proof-grade.
    The homogeneous five-contact branch is likewise a cofactor computation:
    for

    \[
    E_{\mathfrak p}^{hom}=
    \begin{pmatrix}
    V_S(z_1)^T&-V_\Pi(z_1)\\
    \vdots&\vdots\\
    V_S(z_5)^T&-V_\Pi(z_5)
    \end{pmatrix},
    \]

    an oriented null vector \((\theta,\mu)\) gives the homogeneous residual
    \(\rho_S^T\theta-\rho_\Pi\mu\).

    However, the review also exposes a real trap.  For a fixed contact
    pattern,

    \[
    \det
    \begin{pmatrix}
    E_{\mathfrak p}&v_{\Pi,\mathfrak p}\\
    b_S^T-\Lambda\rho_S^T&b_\Pi-\Lambda\rho_\Pi
    \end{pmatrix}
    =
    D_b-\Lambda D_\rho
    \]

    is affine in \(\Lambda\).  Unless \(D_\rho=0\), one fixed pattern cannot
    have the required nonzero sign for all \(\Lambda\in\mathbb R\).  Thus a
    proof by a single fixed determinant orientation for all \(\Lambda\) would
    be false.  The correct statement is an envelope statement: for each
    \(\Lambda\), some majorant/contact pattern may be active.

    Homogeneous margins give the useful compactification.  If there are
    witnesses \(\theta_R,\theta_L\in\mathcal D_Z\) with

    \[
    G_{\theta_R}^{(c)}<0,
    \qquad
    G_{\theta_L}^{(c)}>0,
    \]

    then \(M_\eta(\Lambda)>0\) for all sufficiently large positive
    \(\Lambda\) by \(\theta_R\), and for all sufficiently large negative
    \(\Lambda\) by \(\theta_L\).  Hence the affine verification may be
    restricted to a compact interval \([\Lambda_-,\Lambda_+]\), after the
    homogeneous margins are proved.  This is now the correct Gate 1 order:

    \[
    \boxed{
    \text{homogeneous margin witnesses}
    \quad\Longrightarrow\quad
    \text{compact affine contact verification}.
    }
    \tag{G1EnvelopeOrder}
    \]

    Consequently the missing theorem is not merely "each fixed pattern has a
    sign."  It is the repaired-column envelope theorem: prove the homogeneous
    witnesses and then exclude all regular weighted contact obstructions on
    the compact affine \(\Lambda\)-range.  A repaired numerator ECT or
    total-positivity theorem would prove this, but it has not yet been
    established.

    Review audit: homogeneous margins via endpoint cone separation.

    The next Gate 1 review is accepted as a conditional reduction, with an
    important caveat about row compatibility.  It gives a useful way to split
    the homogeneous branch from the compact affine branch before attempting
    the full contact-pattern verification.

    Define the recession cone of the endpoint majorant inequalities by

    \[
    \mathcal K_Z
    =
    \{\chi\in\mathbb R^4:\chi\cdot V_S(x)\ge0\quad(x\in Z_0)\}.
    \tag{G1RecessionCone}
    \]

    If \(\mathcal D_Z\ne\emptyset\) and there are
    \(\chi_R,\chi_L\in\mathcal K_Z\) such that

    \[
    \chi_R\cdot\rho_S>0,
    \qquad
    \chi_L\cdot\rho_S<0,
    \tag{G1TwoSidedRhoRecession}
    \]

    then the homogeneous margins follow.  Indeed, for any
    \(\theta_0\in\mathcal D_Z\) and \(t\ge0\),
    \(\theta_0+t\chi_R,\theta_0+t\chi_L\in\mathcal D_Z\), and

    \[
    G_{\theta_0+t\chi}^{(c)}
    =
    G_{\theta_0}^{(c)}+t\,\chi\cdot\rho_S.
    \]

    Thus \(G^{(c)}\) is unbounded above along \(\chi_R\) and unbounded below
    along \(\chi_L\), giving

    \[
    \boxed{
    \sup_{\theta\in\mathcal D_Z}G_\theta^{(c)}>0,
    \qquad
    \inf_{\theta\in\mathcal D_Z}G_\theta^{(c)}<0.
    }
    \tag{G1HomMarginsFromRecession}
    \]

    By finite-dimensional separation, (G1TwoSidedRhoRecession) follows from
    the endpoint cone separation

    \[
    \boxed{
    \rho_S\notin \operatorname{cone}\{V_S(x):x\in Z_0\},
    \qquad
    -\rho_S\notin \operatorname{cone}\{V_S(x):x\in Z_0\}.
    }
    \tag{G1EndpointConeSeparation}
    \]

    Conversely, if either cone inclusion held, conic Carathéodory in
    \(\mathbb R^4\) would give a representation by at most four atoms.  In the
    regular four-atom case, for

    \[
    F_X=[V_S(x_1)\ V_S(x_2)\ V_S(x_3)\ V_S(x_4)]
    \]

    the weights are given by Cramer's rule.  Therefore an off-row cofactor
    alternation of the form

    \[
    \operatorname{sgn}
    \det[V_S(x_1)\cdots \rho_S\cdots V_S(x_4)]
    =
    (-1)^i\sigma_\rho\,\operatorname{sgn}\det F_X
    \tag{G1OffRowAlternation}
    \]

    rules out all-positive weights for both \(\rho_S\) and \(-\rho_S\).
    Lower-support cases are obtained by a limiting argument; determinant
    collapse, contact collision, pole collision, or denominator sign loss is
    routed to Gate 3, not counted as a regular Gate 1 pass.

    The other input needed for the argument is non-emptiness of
    \(\mathcal D_Z\).  By the same cone duality, this is equivalent to absence
    of a positive-lift recession ray:

    \[
    \boxed{
    \sum_iw_iV_S(x_i)=0,\quad w_i>0
    \quad\Longrightarrow\quad
    \sum_iw_iV_\Pi(x_i)\le0
    }
    \tag{G1NoPositiveLiftRecession}
    \]

    again with strict or boundary-routed alternatives in the regular ledger.
    Therefore the corrected homogeneous package is

    \[
    \boxed{
    \text{no positive-lift recession}
    +
    \text{endpoint cone separation}
    \Longrightarrow
    \text{homogeneous margins}
    \Longrightarrow
    \Lambda\text{-compactification}.
    }
    \tag{G1HomConePackage}
    \]

    The colleague's proposed Cauchy/Andreief route is a valid sufficient
    strategy only after the actual repaired rows satisfy a row-by-row
    compatibility theorem.  In particular, one must fix the order and
    basepoint of the integration kernel on the disconnected set
    \(Z_0=Z_L\cup Z_R\), the sign of \(Q^2R\) on each component, the ordered
    position and sign convention for the \(c,u,v\) rows, and the moving-Q /
    period/free-filling normalization rows.  Only after those rows are shown
    to be positive rescalings, confluent limits, or positive averages of a
    single ordered Cauchy system can sign-regularity be transferred through
    the Schur complement to \(H_\gamma^{rep}\).  This missing row-by-row
    statement is the current

    \[
    \boxed{\textbf{RepairedCauchySignRegularity / ChartCompatibility lemma}.}
    \tag{G1ChartCompatibilityTarget}
    \]

    Thus this review improves the route, but it still does not prove Gate 1:
    it reduces the homogeneous margin problem to
    (G1NoPositiveLiftRecession) plus (G1EndpointConeSeparation), and reduces
    both to repaired-column determinant signs that remain to be proved.

    Conditional transfer from Cauchy columns to potential contacts.

    The previous paragraph leaves one useful bridge to record.  Assume, only
    for this paragraph, that the repaired Cauchy columns

    \[
    C_j(x)=\frac{H_j^{rep}(x)}{Q(x)^2R(x)},
    \qquad
    j\in\{\alpha_1,\beta_1,\alpha_2,\beta_2,\Pi\},
    \]

    have already been realized as one compatible ordered sign-regular
    Cauchy/confluent-Cauchy block on the ordered components of \(Z_0\), with
    the sign of \(Q^2R\), the component order, and the integration basepoint
    fixed.  Define

    \[
    V_j(x)=\int_x^{x_*}C_j(t)\,dt
    \tag{G1PotentialFromC}
    \]

    on each component with the same orientation convention.  Then the
    determinant signs for the potential rows are inherited from the signs of
    the \(C_j\)-rows.  Indeed,

    \[
    V_j(x_i)=\int K(x_i,t)C_j(t)\,dt,
    \qquad
    K(x,t)=\mathbf 1_{\{t\text{ lies between }x\text{ and }x_*\}},
    \]

    and the ordered step kernel \(K\) is totally positive on a fixed oriented
    component.  Cauchy-Binet/Andreief therefore expresses
    \(\det(V_j(x_i))\) as an integral of products

    \[
    \det(K(x_i,t_m))\det(C_j(t_m)),
    \]

    where the first factor is nonnegative and the second has the fixed
    sign-regular orientation.  Thus the potential determinant has the same
    fixed sign, unless the integral degenerates by contact/component collapse,
    which is a Gate 3 route.

    The off-row \(\rho_j=-C_j(c)\) is handled in the same conditional block.
    If the ordered position and sign convention of \(c\) relative to the
    \(Z_0\)-components is fixed, then replacing one potential row by
    \(\rho\) is a mixed determinant with one Cauchy evaluation row and the
    remaining step-integrated rows.  Applying the same Andreief expansion with
    one evaluation row gives the alternating cofactor orientation
    (G1OffRowAlternation).  Consequently the endpoint cone separation
    (G1EndpointConeSeparation) follows from this compatible sign-regular
    Cauchy realization.

    Finally, if the five-column orientation includes the lifted circuit side
    of \(V_\Pi\), then every positive circuit of \(V_S\) has nonpositive
    \(V_\Pi\)-lift, giving (G1NoPositiveLiftRecession).  Combining these
    conditional transfers with (G1HomConePackage) proves the homogeneous
    margins and compactifies the affine parameter.  What remains after that is
    the compact affine contact verification, including the boundary row pencil
    \(b-\Lambda\rho\) on the compact interval.  Thus the correct implication is

    \[
    \boxed{
    \begin{gathered}
    \text{compatible sign-regular repaired }C\text{-columns}\\
    +\text{ lifted circuit orientation}
    +\text{ compact affine boundary-row verification}\\
    \Longrightarrow \text{Gate 1}.
    \end{gathered}
    }
    \tag{G1CompatibleCauchyTransfer}
    \]

    This is a proof bridge, not the missing proof itself.  The actual
    remaining work is still to prove the compatible sign-regular realization
    for the repaired columns \(H_\gamma^{rep}\) and for the compact affine
    boundary row pencil.

    Positive-lift recession as a five-point circuit determinant.

    The condition (G1NoPositiveLiftRecession) also has an exact finite
    determinant form.  Let \(x_1,\ldots,x_5\in Z_0\) be a regular five-tuple and
    write

    \[
    F_i=V_S(x_i)\in\mathbb R^4,
    \qquad
    u_i=V_\Pi(x_i).
    \]

    A nontrivial circuit among the \(F_i\)'s is generated by the cofactors

    \[
    a_i=(-1)^i
    \det[F_1\ \cdots\ F_{i-1}\ F_{i+1}\ \cdots\ F_5],
    \tag{G1CircuitCoeff}
    \]

    up to one global nonzero scalar, with the sign convention fixed by the
    chosen column order.  Hence

    \[
    \sum_{i=1}^5 a_iF_i=0.
    \]

    Its lifted value is

    \[
    \sum_{i=1}^5 a_i u_i
    =
    \pm
    \det
    \begin{pmatrix}
    F_1&F_2&F_3&F_4&F_5\\
    u_1&u_2&u_3&u_4&u_5
    \end{pmatrix},
    \tag{G1CircuitLiftDet}
    \]

    where the sign is again only the fixed row/column orientation.  Therefore a
    positive-lift recession ray is excluded in the regular five-point case by
    the following check: whenever the cofactor vector \(a\) can be oriented so
    that \(a_i>0\) for all active points, the determinant in
    (G1CircuitLiftDet) must have the opposite sign.  Lower-support circuits are
    limiting cases; if the relevant cofactors vanish, the configuration is a
    contact or chart degeneration and is routed to Gate 3.

    Thus no-positive-lift recession is not a separate heuristic assumption.  It
    is the five-column version of the same determinant orientation problem: the
    four endpoint columns give the circuit coefficients, and the period column
    \(V_\Pi\) supplies the lifted determinant sign.  A compatible
    five-function ECT/sign-regular theorem would prove (G1NoPositiveLiftRecession)
    by (G1CircuitCoeff)--(G1CircuitLiftDet).

    ECT-A homogeneous closure theorem.

    The preceding determinant reductions can now be packaged as a precise
    theorem for the homogeneous branch.

    \[
    \boxed{\textbf{EndpointOffRowAndLiftedCircuitTheorem}.}
    \]

    Assume the following two determinant statements hold for the actual
    repaired columns, with all vanishing/collision cases routed to Gate 3.

    1.  Endpoint/off-row alternation: for every regular four-tuple in \(Z_0\),
        the endpoint determinant and the cofactors obtained by replacing one
        endpoint column by \(\rho_S\) satisfy (G1OffRowAlternation).

    2.  Lifted circuit orientation: for every regular five-tuple in \(Z_0\),
        the endpoint circuit coefficients (G1CircuitCoeff) and the augmented
        determinant (G1CircuitLiftDet) have the sign excluding a positive
        \(V_\Pi\)-lift whenever the endpoint cofactors are oriented positive.

    Then the homogeneous \(Z_0\)-atomic branch is excluded, and the affine
    parameter \(\Lambda\) is reduced to a compact interval.

    Proof.  The lifted circuit orientation excludes positive-lift recession
    rays.  Indeed, if

    \[
    \sum_iw_iV_S(x_i)=0,\qquad w_i>0,
    \qquad
    \sum_iw_iV_\Pi(x_i)>0,
    \]

    then conic Carathéodory in the five-dimensional lifted circuit space gives
    such a relation with at most five atoms.  In the regular five-atom case the
    endpoint null vector is the cofactor vector (G1CircuitCoeff), and the lift
    is exactly (G1CircuitLiftDet), contradicting the lifted circuit orientation.
    Lower-support and zero-cofactor cases are limits of the same system; by
    hypothesis they are Gate 3 degenerations.  Hence
    (G1NoPositiveLiftRecession) holds, so \(\mathcal D_Z\ne\emptyset\).

    Next, endpoint/off-row alternation implies endpoint cone separation.  If

    \[
    \rho_S=\sum_{i=1}^Nw_iV_S(x_i),
    \qquad w_i>0,
    \]

    then conic Carathéodory in \(\mathbb R^4\) gives \(N\le4\).  For a regular
    four-atom representation, Cramer's rule gives the weights by the cofactors
    in (G1OffRowAlternation), so their signs alternate and cannot all be
    positive.  The same argument applies to \(-\rho_S\), and lower-support
    degeneracies are routed to Gate 3.  Thus (G1EndpointConeSeparation) holds.

    Since \(\mathcal D_Z\ne\emptyset\), choose
    \(\theta_0\in\mathcal D_Z\).  By finite-dimensional separation applied to
    (G1EndpointConeSeparation), there are
    \(\chi_R,\chi_L\in\mathcal K_Z\) with
    \(\chi_R\cdot\rho_S>0\) and \(\chi_L\cdot\rho_S<0\).  Therefore
    \(\theta_0+t\chi_R,\theta_0+t\chi_L\in\mathcal D_Z\) for \(t\ge0\), and
    \(G^{(c)}\) tends respectively to \(+\infty\) and \(-\infty\) along these
    rays.  Hence the two homogeneous margins in
    (G1HomMarginsFromRecession) hold.

    Finally, the homogeneous margins give the compactification already recorded
    in (G1EnvelopeOrder): a witness with \(G^{(c)}<0\) makes
    \(M_\eta(\Lambda)>0\) for all sufficiently large positive \(\Lambda\), and
    a witness with \(G^{(c)}>0\) makes \(M_\eta(\Lambda)>0\) for all sufficiently
    large negative \(\Lambda\).  Thus only a compact affine interval remains.
    \(\square\)

    This theorem closes the homogeneous branch conditional on two explicit
    determinant sign statements.  It does not close the compact affine branch:
    the boundary row pencil \(b-\Lambda\rho\), the affine contact sign tables,
    and the repaired-column ChartCompatibility proof still have to be checked
    on the compact \(\Lambda\)-range.

    Compact affine residual-minimum formulation.

    After EndpointOffRowAndLiftedCircuitTheorem, the affine parameter is
    restricted to a compact interval \(I_\Lambda=[\Lambda_-,\Lambda_+]\).  The
    remaining affine branch can therefore be stated as a finite family of
    compact pattern-minimum problems.

    For a regular affine contact pattern \(\mathfrak p\), let
    \(\mathcal S_{\mathfrak p}\) be the set of tuples

    \[
    (\Lambda,z,\theta,w),
    \qquad
    \Lambda\in I_\Lambda,
    \qquad
    w_i>0,
    \]

    satisfying the contact equations \(G_\theta(z_i)=0\), the interior
    stationarity equations \(P_\theta(z_i)=0\), the assigned endpoint
    one-sided signs, the interval sign table for \(P_\theta/(Q^2R)\), and the
    affine KKT equation

    \[
    \sum_iw_iV_S(z_i)=-b_S+\Lambda\rho_S.
    \tag{G1CompactAffineKKT}
    \]

    On this set define the residual

    \[
    R_{\mathfrak p}(\Lambda,z,\theta)
    =
    G_\theta^{(b)}-\Lambda G_\theta^{(c)}.
    \tag{G1CompactAffineResidual}
    \]

    If the pattern is a four-contact invertible pattern, this residual is the
    determinant quotient (G1AffineResidualDet); for lower-support patterns it
    is the same linear functional evaluated on the remaining KKT solution.

    The exact compact affine target is

    \[
    \boxed{
    m_{\mathfrak p}
    :=
    \inf_{\mathcal S_{\mathfrak p}}
    R_{\mathfrak p}
    >0
    \quad
    \text{for every regular affine pattern } \mathfrak p.
    }
    \tag{G1PatternPositiveMinimum}
    \]

    If \(\mathcal S_{\mathfrak p}\) is empty, the pattern is harmless.  If an
    infimum is approached only by contact collision, endpoint/pole hit,
    denominator sign loss, vanishing weight, or chart-rank loss, the limit is
    a Gate 3 route.  Otherwise compactness gives a regular minimizer.  Thus a
    failure of (G1PatternPositiveMinimum) produces an explicit regular tuple in
    \(\mathcal S_{\mathfrak p}\) with

    \[
    R_{\mathfrak p}\le0,
    \]

    which is exactly the weighted affine obstruction extracted earlier.
    Conversely, any regular weighted affine obstruction lies in some
    \(\mathcal S_{\mathfrak p}\) and makes (G1PatternPositiveMinimum) fail.

    Therefore, after ECT-A, the remaining Gate 1 affine work is precisely the
    finite list of inequalities (G1PatternPositiveMinimum), not a new
    measure-theoretic or quotient-rank problem.  This formulation is the
    correct target for either a symbolic determinant proof or an interval
    contact oracle using the repaired data.

    Most likely remaining route.

    The proof should now proceed in the following order.

    First, attack the ECT-A determinant signs for the actual repaired columns:

    \[
    \boxed{
    \text{Endpoint/off-row alternation}
    \quad+\quad
    \text{five-point lifted circuit orientation}.
    }
    \tag{G1NextECTA}
    \]

    This is the highest-leverage task because it closes the homogeneous branch
    and converts the affine branch from an all-\(\Lambda\) problem into the
    compact pattern-minimum problem (G1PatternPositiveMinimum).  The expected
    proof is not a quotient/rank argument.  It must be a determinant product or
    sign-regularity proof for the actual repaired moving-Schiffer columns
    \(H_\gamma^{rep}\), with the \(c\)-row and the period lift column included.

    Second, after ECT-A, prove the compact affine inequalities
    \(m_{\mathfrak p}>0\) pattern by pattern.  The most practical route is an
    interval-certified contact oracle using the repaired data:

    \[
    H_\gamma^{rep},\quad
    C_\gamma=\frac{H_\gamma^{rep}}{Q^2R},\quad
    V_S,\rho_S,b_S,V_\Pi,\rho_\Pi,b_\Pi.
    \tag{G1OracleInputs}
    \]

    The oracle must not use the fixed-\(Q\) collapsed table.  Its output should
    classify each pattern as empty, Gate 3 boundary, or positive residual
    \(m_{\mathfrak p}>0\).  A regular pattern with \(m_{\mathfrak p}\le0\) is a
    real obstruction, not a numerical nuisance.

    Third, keep the second-variation \(Q_{\rm eff}\) line only as a fallback
    for the compact affine hard cases.  It is not the right first move for the
    \(Z_0\)-atomic homogeneous branch because point-row loads have positive
    logarithmic blow-up; it may still help after ECT-A has removed the
    homogeneous recession directions and localized the affine branch.

    Thus the most likely successful route is:

    \[
    \boxed{
    \text{repaired-column ECT-A}
    \Longrightarrow
    \text{compact affine contact verification}
    \Longrightarrow
    \text{Gate 1}.
    }
    \tag{G1MostLikelyRoute}
    \]

    The least promising route remains any attempt to declare PASS from
    endpoint-period quotient rank, a fixed-pattern determinant for all
    \(\Lambda\), or finite \(Q_{\rm eff}\) against nonzero \(Z_0\)-atomic
    loads.

    ECT-A as full moving-block Schur minors.

    The two determinant statements in (G1NextECTA) can be pushed one step
    closer to the actual moving chart.  They are not independent analytic
    assertions about the integrated potentials; after the Cauchy-to-potential
    transfer above, each is a Schur-complement minor of the full moving block.

    Let \(L_X\) denote the ordered row block corresponding to a regular
    four-tuple \(X=(x_1,\ldots,x_4)\) of potential contact rows, and let
    \(L_{X;i\to c}\) be the mixed row block obtained by replacing the \(i\)-th
    potential row by the equality/off-row \(c\)-evaluation row
    \(\rho_j=-C_j(c)\).  Then endpoint/off-row alternation is equivalent to
    fixed signs of the repaired minors

    \[
    \det L_X(H_{\alpha_1}^{rep},H_{\beta_1}^{rep},
             H_{\alpha_2}^{rep},H_{\beta_2}^{rep}),
    \]

    and

    \[
    \det L_{X;i\to c}(H_{\alpha_1}^{rep},H_{\beta_1}^{rep},
             H_{\alpha_2}^{rep},H_{\beta_2}^{rep}).
    \]

    By (Gate1BlockDet), each such determinant is

    \[
    \frac{
    \det
    \begin{pmatrix}
    A&r_{\alpha_1}&r_{\beta_1}&r_{\alpha_2}&r_{\beta_2}\\
    L_\bullet B&
    L_\bullet H_{\alpha_1}^{raw}&
    L_\bullet H_{\beta_1}^{raw}&
    L_\bullet H_{\alpha_2}^{raw}&
    L_\bullet H_{\beta_2}^{raw}
    \end{pmatrix}}
    {\det A},
    \tag{G1ECTASchur4}
    \]

    with \(L_\bullet=L_X\) or \(L_{X;i\to c}\).  Since the canonical chart
    orientation fixes \(\det A>0\), the sign problem is exactly the sign of the
    displayed full moving determinant.

    Similarly, the lifted five-point circuit determinant uses the five columns

    \[
    H_{\alpha_1}^{rep},\ H_{\beta_1}^{rep},\
    H_{\alpha_2}^{rep},\ H_{\beta_2}^{rep},\ \kappa Q^2,
    \]

    evaluated against the five-point potential row block \(L_Y\).  Its sign is
    the sign of

    \[
    \frac{
    \det
    \begin{pmatrix}
    A&r_{\alpha_1}&r_{\beta_1}&r_{\alpha_2}&r_{\beta_2}&r_\Pi\\
    L_Y B&
    L_Y H_{\alpha_1}^{raw}&
    L_Y H_{\beta_1}^{raw}&
    L_Y H_{\alpha_2}^{raw}&
    L_Y H_{\beta_2}^{raw}&
    L_Y(\kappa Q^2)
    \end{pmatrix}}
    {\det A}.
    \tag{G1ECTASchur5}
    \]

    Therefore ECT-A will be proved once the two full-block product formulas
    (G1ECTASchur4) and (G1ECTASchur5) are signed for all admissible ordered
    row blocks, with zero determinants routed to Gate 3.  This is the most
    concrete next theorem:

    \[
    \boxed{\textbf{ECTAFullMovingBlockSignLemma}.}
    \tag{G1ECTAFullBlockTarget}
    \]

    It must expand the full determinants in (G1ECTASchur4) and
    (G1ECTASchur5) as positive factors times ordered Cauchy/Vandermonde
    products.  This is narrower than the earlier
    MovingCorrectionColumnOrientationLemma: only the off-row four-minors and
    lifted five-minors needed for homogeneous closure are required first.
    After they are proved, the proof can move to compact affine
    \(m_{\mathfrak p}>0\) verification.

    The proof checklist for ECTAFullMovingBlockSignLemma is therefore:

    \[
    \boxed{
    \begin{array}{c|c}
    \text{factor} & \text{required sign input}\\ \hline
    \det A & \text{positive chart orientation}\\
    L_X,L_{X;i\to c},L_Y & \text{ordered step/evaluation rows on }Z_0\\
    B_\nu=QD\Delta P_\nu-PD\Delta Q_\nu
      & \text{canonical moving correction basis}\\
    H_\gamma^{raw}=-\frac12PQD_\gamma
      & \text{endpoint interpolation column sign}\\
    \kappa Q^2 & \text{period lift orientation}\\
    Q^2R & \text{fixed component signs}
    \end{array}
    }
    \tag{G1ECTAFullBlockChecklist}
    \]

    Any sign-changing row convention, non-real/multiple pole, vanishing
    endpoint value, or contact/component collision is not an ECT-A pass; it is
    a Gate 3 route or a genuine obstruction.  Thus the next proof attempt
    should start by choosing an explicit ordered moving-correction basis
    \(B_\nu\) and writing the two determinants (G1ECTASchur4),
    (G1ECTASchur5) in that basis.

    Canonical moving-correction basis reduction.

    The basis choice in (G1ECTAFullBlockChecklist) can be normalized without
    changing the substance of the sign problem.  By (Gate1CorrectionImage), in
    the regular monic \(Q\)-chart the moving correction image is exactly

    \[
    \{QD\Delta P-PD\Delta Q\}
    =
    D\mathbb R[z]_{\le 2d-3}.
    \]

    Therefore choose the canonical ordered correction columns

    \[
    \boxed{
    B_m^{can}(z)=D(z)z^m,\qquad 0\le m\le 2d-3,
    }
    \tag{G1CanonicalCorrectionBasis}
    \]

    and, for each \(m\), choose the unique pair
    \((\Delta P_m,\Delta Q_m)\) with

    \[
    Q\Delta P_m-P\Delta Q_m=z^m
    \]

    in the degree ranges of the monic chart.  The actual moving correction
    basis and the canonical basis differ by an invertible change-of-basis
    matrix.  Its determinant only changes the full moving determinants by the
    same nonzero global orientation factor.  We fix the canonical orientation
    by requiring \(\det A>0\) in this basis; if the determinant changes sign
    under a different chart basis, that sign is a basis convention, not a
    mathematical circuit sign.

    Thus ECTAFullMovingBlockSignLemma may be proved using
    \(B_m^{can}=Dz^m\).  In this basis, the normalization block and raw endpoint
    columns reduce to evaluations of the polynomial list

    \[
    Dz^0,\ldots,Dz^{2d-3},
    \qquad
    -\frac12PQD_{\alpha_1},\ldots,-\frac12PQD_{\beta_2},
    \qquad
    \kappa Q^2.
    \tag{G1CanonicalColumnList}
    \]

    The next determinant product to derive is therefore a bordered
    interpolation determinant for (G1CanonicalColumnList) against the ordered
    rows \(A\), \(L_X\), \(L_{X;i\to c}\), or \(L_Y\).  This is preferable to
    working with arbitrary \((\Delta P,\Delta Q)\)-coordinates, because all
    moving correction columns now vanish at the four branch endpoints through
    the common factor \(D\), while the raw endpoint columns
    \(PQD_\gamma\) interpolate the endpoint values.  Any failure of
    invertibility of the change-of-basis map is exactly \(\gcd(P,Q)\ne1\) or a
    degree/chart degeneration and is routed to Gate 3.

    Correction: the five-column first-order block is singular.

    The canonical basis reduction also reveals a hard obstruction to the
    proposed full-block proof of the lifted five-point orientation.  By
    (Gate1PeriodInterpolation),

    \[
    Q^2
    =
    DW_Q
    +
    \sum_\gamma
    \frac{Q(\gamma)}{P(\gamma)D_\gamma(\gamma)}\,P QD_\gamma.
    \]

    In the canonical column list this says that the period column
    \(\kappa Q^2\) is already a linear combination of the correction columns
    \(Dz^m\) and the four raw endpoint columns \(PQD_\gamma\).  Therefore the
    full determinant in (G1ECTASchur5), with all correction columns adjoined,
    is identically zero before any row signs are considered.  Equivalently,
    the Schur-complement five-column determinant cannot furnish a strict
    lifted circuit orientation at first order.

    Thus ECTAFullMovingBlockSignLemma must be split:

    \[
    \boxed{
    \begin{array}{c|c}
    \text{part} & \text{status}\\ \hline
    \text{four-column endpoint/off-row alternation}
      & \text{still plausible by canonical full-block signs}\\
    \text{five-column lifted circuit orientation}
      & \text{not available from first-order full-block determinant}
    \end{array}
    }
    \tag{G1ECTASplitAfterPeriodInterpolation}
    \]

    This is not a new failure; it is the same endpoint-period quotient
    obstruction in canonical coordinates.  The period lift is an endpoint
    interpolation class modulo moving corrections, so no first-order
    determinant product involving the full correction block can give a strict
    period-lift sign.  The lifted positive-circuit negativity needed for
    \(\mathcal D_Z\ne\emptyset\) must come from one of the non-first-order
    mechanisms already isolated: a direct majorant construction on \(Z_0\), a
    compact affine/contact envelope argument after endpoint cone separation, or
    a second-variation/effective Hessian input.  It cannot be proved by the
    naive (G1ECTASchur5) determinant.

    The corrected next target is therefore narrower:

    \[
    \boxed{
    \text{prove endpoint/off-row alternation first;}
    \quad
    \text{treat lifted circuit negativity by majorant/envelope or }Q_{\rm eff}.
    }
    \tag{G1CorrectedNextAfterSingularFiveBlock}
    \]

    Computation start: repaired data extractor core.

    The numerical route has now started with the required first object, not
    with the old fixed-\(Q\) table.  The new script

    \[
    \texttt{1038/gate1\_repaired\_data\_extractor.py}
    \]

    implements the canonical linear-algebra extractor:

    \[
    B_m^{can}=Dz^m,\qquad
    A_{row,m}=row(B_m^{can}),\qquad
    r_\gamma=row\!\left(-\frac12PQD_\gamma\right),
    \]

    solves

    \[
    AX_\gamma=-r_\gamma,
    \]

    and outputs

    \[
    H_\gamma^{rep}
    =
    -\frac12PQD_\gamma+\sum_m(X_\gamma)_mB_m^{can}.
    \]

    The smoke test

    \[
    \texttt{python3 1038/gate1\_repaired\_data\_extractor.py --toy-g2}
    \]

    uses a synthetic regular \(g=2\) chart and verifies the extractor algebra:

    \[
    \det A=5.394710695371\cdot10^7,\qquad
    \kappa(A)=6.851468981911\cdot10^2,
    \]

    \[
    \max_\gamma |AX_\gamma+r_\gamma|
    =
    6.821210263297\cdot10^{-13},
    \qquad
    \max_{\gamma,row}|row(H_\gamma^{rep})|
    =
    7.691625114603\cdot10^{-13}.
    \tag{G1ExtractorSmoke}
    \]

    This is not a Gate 1 certificate.  It proves only that the extractor core
    implements (G1ExtractorSolve)--(G1ExtractorH) correctly once a regular
    moving chart \(P,Q,D,\ell\) is supplied.  The existing
    \(\texttt{solve\_two\_interval\_finite\_gap.py}\) script remains a local
    one-cut/two-interval branch diagnostic; it does not supply the compact
    non-pinched \(g=2\) data \((P,Q,D,\Gamma,\ell)\), and therefore cannot by
    itself run the Gate 1 repaired oracle.

    The next computational step is to provide a real compact \(g=2\) chart
    input to this extractor, then compute \(C_\gamma=H_\gamma^{rep}/(Q^2R)\),
    \(V_S,\rho_S,b_S\), and the endpoint/off-row determinant smoke tests.

    Old two-interval JSON audit.

    The extractor now also has a guard mode

    \[
    \texttt{--audit-two-interval-json}
    \]

    to check whether an existing diagnostic JSON can be used as Gate 1 input.
    Running it on

    \[
    \texttt{two\_interval\_branch\_certificate\_skeleton.json},\quad
    \texttt{two\_interval\_branch\_certificate\_top\_split.json},\quad
    \texttt{two\_interval\_small\_eta\_certificate.json},\quad
    \texttt{two\_interval\_tiny\_eta\_certificate.json}
    \]

    gives

    \[
    \texttt{gate1\_ready = False}.
    \tag{G1OldTwoIntervalAudit}
    \]

    The reason is structural, not a missing Python dependency.  These files
    record the old local ansatz

    \[
    F(z)=\frac{(z+A)\sqrt{(z-\alpha)(z-\beta)}}
    {(z-\ell)(z-r)(z-1)},
    \]

    so the audit can reconstruct only

    \[
    P(z)=z+A,\qquad Q(z)=(z-\ell)(z-r)(z-1),
    \]

    and a single moving cut \([\alpha,\beta]\).  For the first skeleton row it
    reports

    \[
    P=[1.2627187696571671,\ 1.0],
    \]

    \[
    Q=[0.04754235870292919,\ -1.8273266191379003,\ 0.7797842604349712,\ 1.0]
    \]

    in ascending-coefficient order.  What is missing is exactly the Gate 1
    input:

    \[
    \Gamma=\{\alpha_1,\beta_1,\alpha_2,\beta_2\},
    \quad
    \ell_1,\ldots,\ell_N,
    \quad
    \kappa,
    \quad
    Z_0,u,c,v.
    \]

    Therefore the old branch JSONs cannot be converted into repaired Gate 1
    data by a harmless wrapper.  They remain useful local branch diagnostics,
    but any computation of \(M_\eta(\Lambda)\), endpoint/off-row determinants,
    or \(P_\theta\)-sign tables from them would be testing the wrong object.

    Proof-grade chart JSON entry point.

    The same extractor now accepts a real chart file by

    \[
    \texttt{--chart-json PATH}.
    \]

    The required minimal schema is

    \[
    \boxed{
    \texttt{\{P,Q,gammas,rows\}},
    }
    \tag{G1ChartJsonSchema}
    \]

    where \(P,Q\) are ascending coefficient lists, `gammas` is the ordered
    four-endpoint list

    \[
    \Gamma=\{\alpha_1,\beta_1,\alpha_2,\beta_2\},
    \]

    and `rows` is the ordered regular moving-chart row list, with row entries
    of the form

    \[
    \texttt{\{"kind":"eval","x":x\}}
    \quad\text{or}\quad
    \texttt{\{"kind":"deriv","x":x,"order":m\}}.
    \]

    Optional fields

    \[
    \texttt{kappa},\quad \texttt{Z0},\quad \texttt{u},\quad
    \texttt{c},\quad \texttt{v},\quad \texttt{contact\_points}
    \]

    are reserved for the next majorant/determinant stage.  On a supplied chart
    the entry point runs the repaired extractor and also checks the quotient
    identity

    \[
    Q^2
    =
    DW_Q+
    \sum_\gamma
    \frac{Q(\gamma)}{P(\gamma)D_\gamma(\gamma)}PQD_\gamma.
    \tag{G1ChartJsonPeriodAudit}
    \]

    A synthetic chart JSON smoke test gives

    \[
    \max|AX+r|=3.410605131648\cdot10^{-13},\qquad
    \max|row(H_\gamma^{rep})|=3.845812557302\cdot10^{-13},
    \]

    and

    \[
    \max|\operatorname{rem}_D(Q^2-\sum_\gamma
    Q(\gamma)(P(\gamma)D_\gamma(\gamma))^{-1}PQD_\gamma)|
    =
    5.329070518201\cdot10^{-15}.
    \tag{G1ChartJsonSmoke}
    \]

    Thus the computation route is now blocked only by the absence of a real
    compact non-pinched \(g=2\) chart file, not by extractor infrastructure.
    Once such a file is supplied, the next executable checks are:

    1.  repaired row residuals and conditioning of \(A\);
    2.  endpoint/off-row four-column determinant smoke tests;
    3.  construction of \(C_\gamma=H_\gamma^{rep}/(Q^2R)\) and numerical
        quadrature for \(V_S,\rho_S,b_S\);
    4.  compact affine contact/envelope search.

    The entry point already implements the first part of item 3 when an
    off-cut anchor \(c\) is supplied.  With the branch convention
    \(R(z)\sim z^2\) at \(+\infty\), it evaluates the real off-cut branch

    \[
    R(c)=\sqrt{\prod_{\gamma\in\Gamma}(c-\gamma)}
    \]

    with the sign flipped on the middle gap, and returns

    \[
    \rho_\gamma=-C_\gamma(c)
    =
    -\frac{H_\gamma^{rep}(c)}{Q(c)^2R(c)}.
    \tag{G1ChartJsonRho}
    \]

    On the synthetic chart with \(c=-0.4\), the smoke output is

    \[
    R(c)=-2.087103255711,\qquad
    \max_\gamma|\rho_\gamma|=2.992534365488.
    \tag{G1ChartJsonRhoSmoke}
    \]

    The absolute potential rows \(V_S,b_S\) are deliberately not faked by a
    path integral; they require the cut density and the chosen logarithmic
    potential normalization.  That is the next numerical layer after a real
    chart file is available.

    Right-exterior potential layer.

    The first safe potential layer is now implemented for the right exterior
    component only.  If \(s>\beta_2=\max\Gamma\), then the real path
    \([s,\infty)\) does not cross a cut or pole, and the definition

    \[
    V_j(s)=\int_s^\infty C_j(y)\,dy
    \tag{G1RightExteriorV}
    \]

    is numerically unambiguous.  The extractor evaluates this integral by the
    change of variables

    \[
    y=s+\frac{t}{1-t},\qquad 0<t<1,
    \]

    followed by Gauss-Legendre quadrature.  This is deliberately restricted to
    the right exterior component; middle-gap or left-exterior rows require a
    separate boundary-value convention and are not silently computed.

    With synthetic data

    \[
    c=-0.4,\qquad u=2.2,\qquad v=3.0,\qquad a=0.4,\qquad b=0.6,\qquad
    \kappa=1,
    \]

    and contact points \(2.05,2.5\), the chart-json entry point computes four
    right-exterior potential rows and skips none:

    \[
    \texttt{right-exterior V rows computed/skipped}=4/0,
    \]

    and the boundary combination satisfies

    \[
    \max_j|b_j|=7.071555885807\cdot10^2.
    \tag{G1RightExteriorVSmoke}
    \]

    Therefore, if a real Gate 1 chart has \(u,v\) and contact samples in the
    right exterior component, the executable data path now reaches
    \(H_\gamma^{rep}\), \(\rho_S\), right-exterior \(V_S\), \(V_\Pi\), and
    \(b_S,b_\Pi\).  The remaining missing numerical layers are the other
    off-cut components and the compact contact/envelope optimization.

    Right-exterior off-row determinant smoke test.

    The same right-exterior data path now checks the first homogeneous-margin
    determinant pattern.  If four right-exterior contact points

    \[
    x_1<x_2<x_3<x_4,\qquad x_i>\beta_2
    \]

    are supplied, it forms

    \[
    E=(V_S(x_i)^T)_{i=1}^4
    \]

    and replaces each row in turn by \(\rho_S^T\).  It reports the signs of

    \[
    \frac{\det E_{i\to\rho}}{\det E}.
    \tag{G1RightExteriorOffRowDet}
    \]

    On the synthetic chart with contact points

    \[
    2.02,\quad 2.2,\quad 2.5,\quad 3.0,
    \]

    the smoke output is

    \[
    \det E=-3.344745723982\cdot10^1,
    \]

    and

    \[
    \operatorname{sgn}\left(\frac{\det E_{i\to\rho}}{\det E}\right)
    =
    (-,+,-,+).
    \tag{G1RightExteriorOffRowSmoke}
    \]

    Thus the executable can now detect the off-row alternation required by the
    endpoint-cone separation test in any right-exterior four-contact sample.
    This remains only a smoke test until a real compact non-pinched \(g=2\)
    chart is supplied.

    Right-exterior off-row grid scan.

    A single four-contact smoke test is not enough.  The extractor therefore
    also accepts a right-exterior grid specification

    \[
    \texttt{"right\_exterior\_grid":\{"start":s_0,"stop":s_1,"count":N\}}
    \]

    and checks every four-tuple of grid points.  For each tuple it reports
    whether the relative cofactor signs in (G1RightExteriorOffRowDet)
    alternate, whether \(\det E\) is numerically singular, and the first
    nonalternating tuple if one exists.

    On the synthetic chart with grid

    \[
    s_0=2.02,\qquad s_1=4.0,\qquad N=8,
    \]

    the scan gives

    \[
    \texttt{alternating\_four\_tuples}=15,\qquad
    \texttt{total\_four\_tuples}=70,\qquad
    \texttt{singular\_four\_tuples}=0.
    \tag{G1RightExteriorGridSmoke}
    \]

    The first nonalternating tuple is approximately

    \[
    (2.02,\ 2.302857142857143,\ 2.585714285714286,\ 2.8685714285714283),
    \]

    with

    \[
    \det E=0.6096211894375172,\qquad
    \operatorname{relative\ signs}=(-,+,+,-).
    \]

    This is a useful warning, not a theorem about the actual Gate 1 chart: the
    synthetic chart is not constrained to satisfy the real Schiffer ECT
    theorem.  It proves that a hand-picked four-contact smoke test can be
    misleading and that the grid/envelope scan is necessary before promoting
    numerical evidence into a sign claim.

    The grid scan now also records sign-pattern frequencies and the smallest
    \(|\det E|\) tuple.  For the same synthetic grid the pattern distribution is

    \[
    \begin{array}{c|c}
    \text{relative sign pattern} & \text{count}\\ \hline
    (-,-,+,-) & 40\\
    (-,+,+,-) & 15\\
    (+,-,+,-) & 15
    \end{array}
    \tag{G1RightExteriorGridPatternSmoke}
    \]

    while the smallest determinant magnitude occurs at

    \[
    (3.1514285714285712,\ 3.434285714285714,\ 3.717142857142857,\ 4.0),
    \qquad
    \det E=3.872350669859211\cdot10^{-8}.
    \]

    The first nonalternating tuple is not near this smallest determinant:
    it has \(\det E=0.6096211894375172\).  Thus the synthetic failure is not
    merely a near-singular determinant artifact.  For a real chart, passing a
    grid scan with a healthy determinant floor would be meaningful evidence;
    failing it would immediately localize the obstruction pattern.

    Repository-wide Gate 1 chart-input scan.

    The extractor now has a repository scan mode

    \[
    \texttt{--scan-jsons ROOT}
    \]

    which classifies each JSON file as a proof-grade Gate 1 chart candidate,
    an old two-interval diagnostic, or unrelated JSON.  This is deliberately a
    schema check rather than a theorem: it answers whether the numerical route
    has the required input object

    \[
    \{P,Q,\Gamma,\ell\}
    \]

    with four branch endpoints and a square regular moving-chart row list.

    Running

    \[
    \texttt{python3 1038/gate1\_repaired\_data\_extractor.py --scan-jsons 1038}
    \]

    gives

    \[
    \texttt{total JSON files}=7,\qquad
    \texttt{gate1 chart ready}=0,
    \]

    with counts

    \[
    \{\texttt{other\_json}:3,\quad
      \texttt{old\_two\_interval\_diagnostic}:4\}.
    \tag{G1JsonScan1038}
    \]

    A full repository scan

    \[
    \texttt{python3 1038/gate1\_repaired\_data\_extractor.py --scan-jsons .}
    \]

    gives

    \[
    \texttt{total JSON files}=130,\qquad
    \texttt{gate1 chart ready}=0,
    \]

    with counts

    \[
    \{\texttt{other\_json}:122,\quad
      \texttt{json\_non\_object}:2,\quad
      \texttt{unreadable\_json}:2,\quad
      \texttt{old\_two\_interval\_diagnostic}:4\}.
    \tag{G1JsonScanRepo}
    \]

    Thus the current computational blocker is now verified, not inferred:
    there is no proof-grade compact non-pinched \(g=2\) chart JSON anywhere in
    the repository.  Continuing the numerical Gate 1 route requires producing
    or deriving such a chart file.  The existing JSON files can audit old
    local branches, but they cannot run the repaired moving-Schiffer majorant
    computation.

    Chart-generation audit.

    The next possible escape would be to derive the missing chart file from
    numerical constants already present in the ledger.  A direct search for
    four-endpoint data

    \[
    \alpha_1<\beta_1<\alpha_2<\beta_2
    \]

    and for concrete \(P,Q\) compact \(g=2\) coefficients found no such
    candidate.  The numerical constants currently present are the one-cut /
    old two-interval constants, for example

    \[
    x_L=-1.8081073680988165,\qquad
    x_R=0.02632310766384517,
    \]

    and the old ansatz values reconstructed by the audit,

    \[
    P(z)=z+1.2627187696571671,
    \qquad
    Q(z)=(z-\ell)(z-r)(z-1).
    \]

    These do not determine a compact non-pinched two-cut chart.  The local
    compact-neck equations in the ledger specify the state variables

    \[
    y=(q,a,b,c),\qquad u=c-a,\qquad v=c+b,
    \]

    with endpoint equations

    \[
    q\log(1/a)+W(u)=0,\qquad
    q\log(1/b)+W(v)=0,
    \]

    stationarity

    \[
    aW'(u)+bW'(v)=0,
    \]

    and the branch row

    \[
    F(c)=0,\qquad F'(c)<0.
    \]

    But these equations are local neck equations in an external field \(W\);
    they do not by themselves produce the global finite-gap objects

    \[
    P,\ Q,\ \Gamma,\ \ell,\ \kappa,\ Z_0,u,c,v.
    \]

    In particular, the ledger explicitly leaves the proof-grade chart rows
    \(\ell\), the pole/residue-state convention, and the global period/filling
    normalization as inputs to the repaired extractor.  Therefore a chart
    builder cannot be honestly implemented from the current formulas without
    first writing the missing global finite-gap chart equations.

    The computational route is now sharply split:

    1.  **Chart-construction route.**  Write and solve the compact non-pinched
        \(g=2\) finite-gap chart equations that output
        \(\{P,Q,\Gamma,\ell,\kappa,Z_0,u,c,v\}\).  This is the next necessary
        numerical step if the proof is to continue by repaired majorants.
    2.  **Row-realization proof route.**  Prove the
        RepairedCauchySignRegularity / ChartCompatibility theorem directly,
        without relying on a numerical chart instance.
    3.  **Second-variation route.**  Continue the Riesz/Gram route, but it
        still needs the same separated two-cut chart parameters and the
        endpoint-transfer realization.  It is not currently a bypass around
        the missing chart.

    Thus the best next action is not another scan or another old-JSON run.  It
    is to formulate the global compact \(g=2\) chart equations as an executable
    solver target.

    Minimal chart-solver specification.

    The solver target should not reuse the fixed-\(Q\) Hermite endpoint table.
    That table has already been audited:

    \[
    H_{\alpha_1}=H_{\beta_1}=H_{\alpha_2}=H_{\beta_2}
    =
    -\frac12\operatorname{lc}(P)\,Q^2,
    \]

    so all four endpoint columns are proportional to the period column.  Any
    solver built on that table would reproduce the known collapse, not Gate 1
    data.  The solver must instead target the full moving-Schiffer chart.

    The minimal output contract is the chart JSON schema:

    \[
    \boxed{
    \texttt{P,Q,gammas,rows,kappa,Z0,u,c,v}
    }
    \tag{G1ChartSolverOutput}
    \]

    with optional contact samples and grid boxes for majorant tests.  Here
    \(P,Q\) are ascending coefficient lists, \(Q\) is monic, and
    `gammas` is

    \[
    \Gamma=(\alpha_1,\beta_1,\alpha_2,\beta_2).
    \]

    A legitimate compact \(g=2\) solver must choose unknowns at least

    \[
    \alpha_1,\beta_1,\alpha_2,\beta_2,\quad
    p_1,\ldots,p_d,\quad
    P\text{-coefficients},\quad
    \text{residue/pole-state variables},\quad
    u,c,v,\quad \text{period/filling variable},
    \]

    subject to:

    1.  finite-gap representation

        \[
        F(z)=\frac{P(z)}{Q(z)}R(z),\qquad
        R(z)^2=\prod_{\gamma\in\Gamma}(z-\gamma),\qquad R(z)\sim z^2;
        \]

    2.  decay and mass normalization \(F(z)=m_F/z+O(z^{-2})\) with fixed
        \(m_F>0\);
    3.  positivity/interlacing: real simple \(Q\)-poles off the cuts, positive
        residues, and positive cut density;
    4.  endpoint neck equations for the first extra positive component

        \[
        q\log(1/a)+W(u)=0,\qquad
        q\log(1/b)+W(v)=0,\qquad
        aW'(u)+bW'(v)=0,
        \]

        where \(a=c-u\), \(b=v-c\);
    5.  branch equation

        \[
        F(c)=0,\qquad F'(c)<0;
        \]

    6.  fixed period/filling convention and the associated orientation
        \(\kappa\);
    7.  the ordered regular moving-chart rows \(\ell\) for the full
        moving-Schiffer correction system.

    Items 1--5 are present in the ledger as analytic constraints.  Items 6--7
    are not yet explicit enough to code: the chart row list must say exactly
    which moving-\(P\), moving-\(Q\), pole/residue, period/filling, and
    normalization rows are fixed.  This is the smallest missing mathematical
    definition before a real chart solver can be written.

    Therefore the next proof/computation target is:

    \[
    \boxed{
    \textbf{CompactG2MovingChartEquations.}
    }
    \]

    It must define the unknown vector, the equation vector, the period/filling
    convention, and the ordered row list \(\ell\) so that its solutions export
    exactly (G1ChartSolverOutput).  Once this is written, the existing repaired
    extractor and determinant/envelope oracles become executable on the
    resulting chart.

    Row-count audit for the proposed canonical moving chart.

    There is a concrete consistency check before any solver can be written.  In
    the current canonical-basis reduction the moving correction image is stated
    as

    \[
    D\mathbb R[z]_{\le 2d-3}.
    \]

    Its dimension is

    \[
    \dim D\mathbb R[z]_{\le 2d-3}=2d-2.
    \tag{G1CorrectionDim}
    \]

    The same ledger later describes the canonical Gate 1 rows as the
    zero-mass/infinity row plus real pole-state evaluation/confluent derivative
    rows.  If all pole rows

    \[
    H\mapsto H(p_k),\qquad H\mapsto H'(p_k),
    \qquad k=1,\ldots,d
    \]

    are included, this already gives \(2d\) rows, or \(2d+1\) rows if the
    zero-mass row is also included.  Thus the proposed row list is larger than
    the proposed correction space:

    \[
    2d-2
    \quad\text{versus}\quad
    2d\ \text{or}\ 2d+1.
    \tag{G1RowCountMismatch}
    \]

    For the numerically relevant cubic \(Q\) case this is

    \[
    4\quad\text{correction columns, but }6\text{ pole rows, or }7\text{ with mass}.
    \]

    Therefore the text cannot yet define the square matrix \(A_{\ell,X}\) in a
    proof-grade way.  One of the following must be true before a chart solver
    is meaningful:

    1.  the correction image \(D\mathbb R[z]_{\le2d-3}\) is too small for the
        full moving-\(P,Q\) pole-state chart and must be enlarged;
    2.  only a selected \(2d-2\)-row subset of the pole/mass/period conditions
        belongs to \(A\), with the remaining rows treated as open state
        coordinates or quotient rows;
    3.  some of the pole eval/deriv rows are dependent on the chosen degree
        ranges and should not be counted independently;
    4.  the canonical row checklist is only a TP-row toolbox, not the actual
        normalization list \(\ell\).

    This is now the smallest concrete obstruction to writing
    CompactG2MovingChartEquations.  Before any new numerical solve, the proof
    must specify a square moving-chart linear system:

    \[
    \boxed{
    \#\ell=\dim\mathcal X,\qquad
    A_{\ell,X}=\ell(BX)\text{ invertible}.
    }
    \tag{G1SquareChartRequirement}
    \]

    Until then, a chart builder would have to guess which rows are equations
    and which rows are state outputs, and any resulting Gate 1 computation
    would not be proof-grade.

    Row-count resolution forced by the monic chart.

    The first option above, enlarging the correction image, is not harmless in
    the monic \(Q\)-chart.  The ledger already proves

    \[
    (\Delta P,\Delta Q)\longmapsto Q\Delta P-P\Delta Q
    \]

    is an isomorphism

    \[
    \mathbb R[z]_{\le d-3}\oplus\mathbb R[z]_{\le d-1}
    \xrightarrow{\ \sim\ }
    \mathbb R[z]_{\le 2d-3},
    \]

    because \(\gcd(P,Q)=1\) and \(Q\) is monic.  Hence the moving correction
    image has the fixed dimension \(2d-2\).  Enlarging it would change the
    finite-gap chart rather than merely complete the missing data.

    Therefore the only proof-compatible repair is:

    \[
    \boxed{
    \text{choose exactly }2d-2\text{ independent normalization rows for }A,
    \text{ and treat every other pole/residue/period quantity as a state
    output, open inequality, or quotient row.}
    }
    \tag{G1RowCountResolution}
    \]

    In particular, the statement "zero-mass plus all \(H(p_k),H'(p_k)\) rows"
    cannot be the actual row list \(\ell\) for \(A\).  It can only be a
    toolbox of possible TP rows or a larger diagnostic row set.  The chart
    equations must specify which \(2d-2\) rows are imposed and why the remaining
    pole/residue signs are preserved as regular state inequalities.

    For cubic \(Q\), this means the next solver must choose four independent
    rows.  A plausible square gauge is a four-row pole-state gauge, for example
    selected residue/pole-position rows after the monic \(Q\) coordinate has
    absorbed the other two pole rows; but this is not yet written in the proof.
    It must be derived from the actual finite-gap parameterization, not chosen
    for numerical convenience.

    Thus the next theorem is more precise:

    \[
    \boxed{
    \textbf{SquareMovingChartGaugeLemma.}
    }
    \]

    It must identify the \(2d-2\) rows in \(\ell\), prove
    \(A_{\ell,X}\) is invertible in the regular non-pinched chart, and prove
    that all omitted pole/residue/period conditions are either quotient
    directions or open regularity inequalities routed to Gate 3 when they fail.
    Only after this lemma is fixed can CompactG2MovingChartEquations be
    implemented without guessing.

    Algebraic square gauge versus sign-compatible square gauge.

    The earlier normalization construction already contains an algebraic
    square-gauge existence statement: remove redundant normalization rows and
    choose a correction subspace \(\mathcal H_{\rm norm}\) on which

    \[
    \mathcal N:\mathcal H_{\rm norm}\to\operatorname{im}\mathcal N
    \]

    is an isomorphism.  This is enough to define repaired columns as abstract
    Schur-complement columns.  It is not enough for the Gate 1 sign theorem.

    The reason is that a generic basis of \(\operatorname{im}\mathcal N\) is a
    generic linear combination of Cauchy/confluent rows.  Such a basis may be
    perfectly invertible while destroying every ordered determinant sign.  The
    total-positivity transfer requires the rows of \(A\) themselves to be
    ordered Cauchy rows, confluent Cauchy rows, positive averages, or positive
    rescalings thereof.  Gaussian elimination, QR row selection, or arbitrary
    basis compression cannot be used in a proof of the circuit orientation
    unless the transition matrix is known to be totally positive with fixed
    sign.

    Therefore SquareMovingChartGaugeLemma must be strengthened to:

    \[
    \boxed{
    \textbf{TPSquareMovingChartGaugeLemma.}
    }
    \]

    It must choose exactly \(2d-2\) normalization rows satisfying all three
    requirements:

    1.  they span \(\operatorname{im}\mathcal N\) on
        \(D\mathbb R[z]_{\le2d-3}\);
    2.  the resulting \(A_{\ell,X}\) is invertible in the regular chart;
    3.  the selected row list is TP-compatible: ordered Cauchy/confluent rows
        or positive averages with a fixed orientation.

    This separates two facts that were previously conflated:

    \[
    \text{abstract repaired columns exist}
    \quad\not\Rightarrow\quad
    \text{their Schur minors have a sign.}
    \]

    For computation, an arbitrary independent row subset can still be useful
    to generate candidate repaired data.  For proof, the selected subset must
    be TP-compatible.  The next calculation should therefore search for a
    natural TP-compatible square subset of the overcomplete pole/mass/period
    row list, rather than compressing rows by arbitrary numerical linear
    algebra.

    Pole-row subset audit tool.

    The extractor now has

    \[
    \texttt{--audit-pole-row-subsets}
    \]

    to enumerate square subgauges of the overcomplete pole row list.  For a
    supplied chart, or for the synthetic \(g=2\) smoke chart, it takes the real
    roots \(p_k\) of \(Q\), forms the candidate rows

    \[
    H\mapsto H(p_k),\qquad H\mapsto H'(p_k),
    \]

    applies them to the canonical correction columns

    \[
    Dz^m,\qquad 0\le m\le2d-3,
    \]

    and enumerates all square row subsets of size \(2d-2\).  This is not a
    Gate 1 sign certificate; it is a gauge-search diagnostic for
    TPSquareMovingChartGaugeLemma.

    On the synthetic cubic \(Q\) chart, the command

    \[
    \texttt{python3 1038/gate1\_repaired\_data\_extractor.py --toy-g2
    --audit-pole-row-subsets}
    \]

    reports

    \[
    d=3,\qquad 6\text{ candidate pole rows},\qquad 4\text{ correction columns},
    \]

    and all

    \[
    \binom64=15
    \]

    square subsets are full rank, with determinant magnitudes ranging from

    \[
    7.019243915694513\cdot10^5
    \quad\text{to}\quad
    5.104535926940518\cdot10^8.
    \tag{G1PoleRowSubsetToy}
    \]

    The first full-rank subset is

    \[
    H(p_1),\ H'(p_1),\ H(p_2),\ H'(p_2).
    \]

    This smoke result supports the computational feasibility of selecting a
    square pole-row gauge, but it also reinforces the proof distinction:
    full rank is easy; the remaining proof-grade condition is that the chosen
    square subset has a fixed ordered Cauchy/confluent determinant orientation
    in the actual regular chart.

    Pole-row orientation audit.

    The pole-row subset audit now also records determinant signs and row-kind
    patterns.  On the same synthetic cubic smoke chart, all \(15\) square
    subsets remain full rank, but their determinant signs are not uniform:

    \[
    \#\{\det A>0\}=11,\qquad
    \#\{\det A<0\}=4.
    \tag{G1PoleRowSubsetSigns}
    \]

    Moreover the repeated row-kind pattern

    \[
    E,D,E,D
    \]

    itself has both signs in the toy enumeration.  The command reports

    \[
    E,D,E,D:\quad 4\text{ positive},\quad 1\text{ negative}.
    \]

    This is only a toy row-rank/orientation diagnostic, not a proof-grade
    counterexample.  Its value is methodological: it confirms that
    \( \det A\ne0\) is far too weak for Gate 1.  Even among square pole-row
    gauges, orientation depends on the selected ordered row subset.  Therefore
    `TPSquareMovingChartGaugeLemma` cannot be replaced by "choose any
    full-rank square submatrix"; it must specify a canonical ordered row
    selection, or prove a row-order/sign normalization that makes the relevant
    Schur minors Cauchy-sign-compatible.

    The conditional PV equation is not used in this reduction.

    Gate 2: Proposition 4.1 interface.

    Gate 2 now applies to the reduced LP produced by Gate 1.

    Suppose there is a finite linear combination of the repaired endpoint seeds,
    the period seed, and the boundary-neutral equality correctors such that the
    equality-corrected perturbation \(\widehat V\) satisfies

    \[
    R_0(\widehat V)=R_c(\widehat V)=0,
    \qquad
    B_{\rm safe}(\widehat V)<0,
    \qquad
    \widehat V<0\quad\text{on }Z_0.
    \tag{G2hyp}
    \]

    Here

    \[
    B_{\rm safe}(\widehat V)
    =
    a\widehat V(u)+b\widehat V(v)
    \]

    is the anchored neck boundary derivative multiplier.  The regularized
    Schiffer cutoffs have only integrable endpoint singularity
    \(O(|x-\gamma|^{-1/2})\), and their cutoff errors tend to zero in all rows
    and uniformly on \(Z_0\).  The smooth equality-correction bumps are
    \(C^1\) near the moving boundary and continuous near \(Z_0\).  Therefore,
    after choosing sufficiently small cutoff scale \(\rho\), the strict
    inequalities in (G2hyp) persist and the perturbation satisfies the
    regularity/admissibility hypotheses of Proposition 4.1: \(C^1\) near
    \(\partial E\), continuous near \(Z_0\), strictly negative on \(Z_0\), and
    bounded below on compact subsets of the positive set.

    Proposition 4.1 then gives the one-sided first variation formula.  Since
    \(\widehat V<0\) on \(Z_0\), no new positive component is born from the
    active interior zero set.  The boundary contribution of the neck is

    \[
    aX\,\delta L_{uv}
    =
    a\widehat V(u)+b\widehat V(v)
    =
    B_{\rm safe}(\widehat V)<0,
    \qquad aX>0.
    \]

    In the reduced rank-defect setup the remaining boundary rows are either
    fixed by the state constraints or included in the same boundary functional.
    Hence the total one-sided length derivative is negative:

    \[
    \left.\frac{d}{d\varepsilon}\right|_{0+}|E_\varepsilon|<0.
    \]

    Thus:

    \[
    \boxed{
    \textbf{Gate 2 result: PASS.}\quad
    \text{Gate 1 reduced LP feasibility}
    \Rightarrow
    \text{rank-defect candidate is not a minimizer.}
    }
    \]

    Therefore Gate 2 is closed as an interface theorem.  The rank-defect
    compact non-pinched \(g=2\) interior is excluded only after Gate 1 supplies
    the reduced LP feasibility, equivalently after the remaining
    \(P_\theta\)-majorant/sign-table checks in Gate1ConeEnvelopeAssembly are
    proved.

    Gate 3: PinchingBoundaryReduction.

    The proof-grade form is the following compactness statement.

    \[
    \boxed{
    \textbf{PinchingBoundaryReduction.}\quad
    \partial\mathcal C_{g=2}
    \subset
    \mathcal C_{g\le1}^{\rm corr}
    \cup \mathcal C_{\rm one-cut}
    \cup \mathcal C_{g=2}^{\rm excluded}.
    }
    \tag{G3theorem}
    \]

    Here \(\mathcal C_{g=2}\) is the separated positive \(g=2\) finite-gap
    chart.  Its compactification uses:

    - coefficient convergence of \(D_n(z)=\prod_{\delta}(z-\delta_{n})\) and
      \(Q_n\), with the roots ordered on the real line;
    - weak convergence of the positive pole/endpoint atoms;
    - \(L^1_{\rm loc}\) convergence of the absolutely continuous densities on
      non-colliding cut interiors;
    - Hausdorff convergence of the closed active-zero sets \(Z_{0,n}\);
    - local uniform convergence of logarithmic potentials off the limiting
      support, with \(C^1\) convergence near every non-colliding boundary
      point.

    This compactness follows from fixed total mass, the real separated
    Stieltjes chart, and the coefficient compactification of the finite
    branch/pole data.  Conversely, if none of the boundary failures below
    occurs, all discriminants, resultants, residues, density signs, chart
    determinants, and anchor distances stay bounded away from zero.  The
    implicit-function chart is then still regular and non-pinched, so the
    point was not in \(\partial\mathcal C_{g=2}\).  Thus the list below is
    exhaustive.

    \[
    \begin{array}{c|c|c}
    \text{boundary mode} & \text{compactness mechanism} & \text{route} \\ \hline
    \text{branch pinching} & \operatorname{disc}D\to0
      & \text{lower genus or endpoint atom} \\
    Q\text{-pole collision} & \operatorname{disc}Q\to0
      & \text{merged real atom / lower pole stratum} \\
    \text{multiple pole} & \gcd(Q,Q')\ne1
      & \text{lower pole stratum or residue-zero face} \\
    \text{density sign loss} & \rho_n\downarrow0\text{ somewhere on a cut}
      & \text{positivity boundary / lower support} \\
    \text{residue zero} & m_{k,n}\to0
      & \text{atom deletion / lower pole stratum} \\
    \text{endpoint atom creation} & \text{collapsed interval or pole endpoint limit}
      & \text{corrected }g=1\text{ or one-cut face} \\
    Z_0\text{-collision or closure} & d(Z_{0,n},\partial E_n)\to0
      & \text{active-set boundary / lower genus} \\
    c\text{ hitting a forbidden set} & d(c_n,\partial E_n\cup Z_{0,n}\cup Q_n^{-1}(0))\to0
      & \text{anchor singular boundary}
    \end{array}
    \tag{G3modes}
    \]

    We verify the routes.

    Branch pinching.  Suppose two adjacent endpoints
    \(\alpha_n<\beta_n\) satisfy \(\alpha_n,\beta_n\to\gamma\).  Write

    \[
    D_n(z)=(z-\alpha_n)(z-\beta_n)\widetilde D_n(z).
    \]

    Away from \(\gamma\), \(R_n(z)/(z-\gamma)\to \widetilde R(z)\).  The
    measures on the shrinking cut have weak limits of the form
    \(m_\gamma\delta_\gamma\) with \(m_\gamma\ge0\), because all densities are
    nonnegative.  If \(m_\gamma=0\), the shrinking factor is removable and the
    limit has the lower-genus radical \(\widetilde R\).  If \(m_\gamma>0\),
    the limit is the same lower-genus radical plus a nonnegative endpoint
    atom.  In both cases mass and potential rows converge by weak convergence
    of logarithmic potentials away from \(\gamma\), and the active-zero set
    converges in Hausdorff topology.  Hence no new \(g=2\) stratum remains.

    \(Q\)-pole collisions and multiple poles.  In the real positive chart the
    pole part is a Stieltjes sum

    \[
    \sum_k \frac{m_{k,n}}{z-p_{k,n}},\qquad m_{k,n}\ge0.
    \]

    If \(p_{i,n},p_{j,n}\to p\), the weak limit is a single atom with residue
    \(m_i+m_j\).  If a pole becomes multiple after cancellation, the partial
    fraction expansion is still the weak limit of simple positive atoms; any
    zero limiting residue deletes the atom.  If \(p\) reaches a branch
    endpoint, the limit is an endpoint atom and is already covered by the
    branch-pinching route.  If the limit leaves the separated real interlacing
    class, the density sign condition fails, so the state lies on the
    positivity boundary rather than in a new chamber.

    Density sign loss and residue zero.  If a residue tends to zero, the atom
    disappears and the pole stratum has lower dimension.  If the absolutely
    continuous density loses strict positivity on a cut, then either the
    vanishing factor cancels a branch factor, lowering genus, or the
    Schiffer/Jacobian chart determinant vanishes.  The latter is exactly a
    chart-rank boundary; it is not an additional compact \(g=2\) interior
    because regularity would otherwise keep all density signs open.

    Endpoint atoms.  Endpoint atoms can only arise as weak limits of mass on a
    collapsing cut or of real atoms whose poles reach an endpoint.  These are
    the two cases above.  The limiting variational problem is therefore the
    corrected \(g=1\) or one-cut endpoint-atom problem, not a new rank-defect
    \(g=2\) chamber.

    \(Z_0\)-collision and anchor collision.  If \(Z_{0,n}\) collides with a
    moving boundary, then either the strict \(Z_0\)-negativity used in Gate 2
    survives after regularization, or an active component is pinched and the
    support genus drops.  If \(c_n\) hits a branch endpoint, a pole, an atom,
    or \(Z_0\), then \(R_c\) or \(R_{\ell c}\) is singular and the fixed
    anchored chart is invalid.  The only possible limit is the corresponding
    state-lift or pinching boundary already listed above.

    Therefore every compactified boundary limit of a \(g=2\) chamber routes to

    \[
    \boxed{
    \text{corrected }g=1,\quad
    \text{one-cut},\quad
    \text{lower genus},\quad
    \text{an excluded regular }g=2\text{ case, or a rank-defect }g=2
    \text{ case conditional on Gate 1.}
    }
    \tag{G3route}
    \]

    Thus the intended boundary route is:

    \[
    \boxed{
    \textbf{Gate 3 status: proof route identified, compactness proof still required.}
    }
    \]

    To upgrade Gate 3 to proof-grade PASS, the boundary compactness lemma must
    still be written with coefficient convergence, weak convergence of atoms,
    \(L^1_{\rm loc}\) convergence of densities, Hausdorff closure of active
    zero sets, local uniform convergence of potentials, and a proof that
    endpoint atoms/pole collisions do not create a new counterexample stratum.
    Until that lemma is supplied, Gate 3 remains a routed proof obligation, not
    a closed theorem.

    The remaining global gates are the high-genus local-neck reduction,
    regularity removal, and the one-cut upper construction.

    Gate 4: HighGenusLocalNeckReduction.

    The proof-grade statement is:

    \[
    \boxed{
    \textbf{HighGenusLocalNeckReduction.}\quad
    \mathcal C^{\rm reg}_{g\ge3}
    \subset
    \text{local }g=2\text{ obstruction}
    \cup \partial\mathcal C.
    }
    \tag{G4theorem}
    \]

    Let a regular compact finite-gap chamber have genus \(g\ge3\), with
    ordered cuts \(J_i=[\alpha_i,\beta_i]\).  Since the chamber is compact and
    non-pinched, all gaps \((\beta_i,\alpha_{i+1})\) are nonempty.  Let
    \(K\) be the actual KKT normal after the free-period quotient.  If the
    projection of \(K\) to every adjacent two-cut block vanished, then by
    overlapping adjacent blocks \(K\) would vanish on every cut.  The Cauchy
    transform of \(K\) would then vanish on the support and at infinity, hence
    \(K=0\), contradicting nontriviality of the separating normal.  Therefore
    some adjacent block

    \[
    J_{i,i+1}=J_i\cup J_{i+1}
    \]

    has nonzero normal projection and a genuine local neck gap
    \((\beta_i,\alpha_{i+1})\).

    Freeze all rows supported outside a small neighborhood of this block:
    outside branch endpoints, outside pole-state rows, outside active-zero
    rows, and the outside period/filling rows.  Let \(R_{\rm out}\) be their
    row matrix evaluated on smooth signed density bumps supported in the
    positive-density interiors of the outside cuts.  Regularity of the
    high-genus chart says exactly that this row map has full rank after the
    local block variables are held fixed.  If it does not, the full chart
    Jacobian has dropped rank; by Gate 3 this is a boundary/lower-genus
    degeneration, not a regular high-genus interior.

    Hence choose outside bump correctors \(\Psi_{\rm out}\) with
    \(R_{\rm out}(\Psi_{\rm out})=I\).  For any local perturbation \(G_{\rm loc}\),
    set

    \[
    \widehat G_{\rm loc}
    =
    G_{\rm loc}
    -
    \Psi_{\rm out}\,R_{\rm out}(G_{\rm loc}).
    \tag{G4correct}
    \]

    Then all frozen outside rows vanish on \(\widehat G_{\rm loc}\).  This is
    the Schur complement of the outside row block.  Because the correctors are
    supported away from the neck, they are \(C^1\) near the local moving
    boundaries and continuous near the local active-zero set; they restore
    constraints without changing the sign of a strict local neck descent after
    taking the local perturbation small enough.

    The remaining rows on \(J_i\cup J_{i+1}\) are exactly the \(g=2\) rows:
    the local anchor row, the two endpoint difference rows, the smooth-bump
    equality rows, and the four Schiffer endpoint columns
    \[
    \alpha_i,\beta_i,\alpha_{i+1},\beta_{i+1}.
    \]
    Thus the Schur-complement local LP has the same form as the \(g=2\)
    reduced LP:

    \[
    b_\Pi^{(i)}+\sum_{\gamma\in\{\alpha_i,\beta_i,\alpha_{i+1},\beta_{i+1}\}}
    s_\gamma b_\gamma^{(i)}<0,
    \]

    \[
    f_\Pi^{(i)}(x)+
    \sum_{\gamma\in\{\alpha_i,\beta_i,\alpha_{i+1},\beta_{i+1}\}}
    s_\gamma f_\gamma^{(i)}(x)<0
    \quad (x\in Z_0\cap J_{i,i+1}).
    \tag{G4LP}
    \]

    The free-period quotient does not introduce a new pointwise sign-shifter.
    In genus \(g\), the period rows are absorbed by the filling variables
    \(\tau_1,\ldots,\tau_{g-1}\).  For any extended left-cokernel
    \((\kappa,\kappa_\Pi)\), the \(\tau\)-columns force the period multipliers
    to vanish:

    \[
    \kappa^TA=0,\qquad \kappa_{\Pi,m}=0\quad(m=1,\ldots,g-1).
    \]

    Hence higher genus does not revive the forbidden free
    \(\lambda\pi_0\)-type pointwise sign-shifter.

    The local Schur-complement block has only three possible outcomes.

    1.  The local block is regular.  Then the positive free-period local
        lineality gives the same KKT normal/sign contradiction as the regular
        \(g=2\) compact case: the actual normal must be orthogonal to a
        positive lineality direction, while cone separation gives a
        nonnegative integrand.  This is impossible unless the normal is zero,
        contradicting nontriviality.

    2.  The local block is rank-defect but non-pinched.  This branch is
        reduced to the Gate 1 cone-envelope/majorant checks and the Gate 2
        first-variation interface.  Once Gate 1 supplies reduced LP
        feasibility, the outside bump correctors restore all frozen
        high-genus rows without changing the strict local descent, and the
        high-genus candidate is not a minimizer.  Until then, this branch is
        conditional on the same \(P_\theta\)-majorant hard mouth.

    3.  The local block degenerates: a branch endpoint collides, a pole-state
        row loses rank, a density sign is lost, \(Z_0\) collides with the
        local boundary, or the anchor row becomes singular.  This is exactly
        one of the Gate 3 boundary modes, and it routes to lower genus,
        corrected \(g=1\), the one-cut face, or an already excluded \(g=2\)
        case.

    Therefore every regular compact high-genus chamber contains a local
    \(g=2\)-type neck obstruction or degenerates to a Gate 3 boundary stratum:

    \[
    \boxed{
    g\ge3
    \Rightarrow
    \text{local }g=2\text{ obstruction or boundary/lower genus.}
    }
    \tag{G4route}
    \]

    Thus the intended high-genus route is:

    \[
    \boxed{
    \textbf{Gate 4 status: proof route identified, global Schur complement
    proof still required.}\quad
    \text{The local-neck reduction is not yet proof-grade.}
    }
    \]

    To upgrade Gate 4 to PASS, the proof must explicitly show that freezing
    outside rows and applying outside bump correctors produces a legitimate
    Schur complement whose effective local rows are exactly the \(g=2\) neck
    rows, with all non-local logarithmic-capacity tails accounted for.  If that
    Schur complement loses rank or changes the local orientation, the state
    must be routed to Gate 3 boundary/lower genus rather than treated as a
    closed high-genus exclusion.

    Conditional on Gates 1, 3, and 4, all regular finite-gap compact chambers
    are reduced to the one-cut/lower-genus branch or excluded by the local
    \(g=2\) obstruction.  The remaining gates are regularity removal and the
    one-cut upper construction.

    Gate 5: Lemma R / regularity removal.

    The proof-grade regularity statement is:

    \[
    \boxed{
    \textbf{Lemma R.}\quad
    \text{A normalized minimizing counterexample either has regular
    finite-gap approximants with the same strict length defect, or lies on a
    Gate 3 boundary stratum.}
    }
    \tag{G5lemma}
    \]

    Let \(\mu\) be a compactified normalized minimizer with
    \(|E_\mu|<M_{\rm oc}\).  Choose \(\delta>0\) with
    \(|E_\mu|+\delta<M_{\rm oc}\).  Construct raw regular data
    \(\mu_\epsilon^{raw}\) as follows: split multiple poles by
    \(O(\epsilon)\), separate coincident branch endpoints by \(O(\epsilon)\),
    replace persistent zero residues by positive \(O(\epsilon)\) residues,
    and add a \(C^\infty\) positive density floor \(O(\epsilon)\) on active
    cuts.  The added floor is compensated by subtracting \(O(\epsilon)\) mass
    from an existing positive atom or positive density subinterval, so total
    mass stays \(1+O(\epsilon^2)\) before row restoration.

    The logarithmic kernels are locally integrable, so
    \(\mu_\epsilon^{raw}\rightharpoonup\mu\) implies local uniform convergence
    of potentials off the limiting support.  On neighborhoods of
    non-colliding boundaries the support stays separated, hence the Cauchy
    transforms converge in \(C^1\).  The superlevel sets therefore satisfy

    \[
    |E_{\mu_\epsilon^{raw}}|\to |E_\mu|
    \]

    by the one-dimensional boundary variation formula and the fact that
    active-zero collisions are exactly Gate 3 boundary events.  Thus
    \(|E_{\mu_\epsilon^{raw}}|<M_{\rm oc}-\delta/2\) for small \(\epsilon\).

    Let \(\mathcal R\) be the finite vector of exact rows: mass, filling,
    pole-state, active-zero, endpoint, and anchor rows.  In a regular chart
    the Jacobian \(D\mathcal R\) with respect to the finite branch/pole/atom
    variables and smooth row-corrector bumps is invertible.  The implicit
    function theorem gives a correction

    \[
    \mu_\epsilon=\mu_\epsilon^{raw}+O(\|\mathcal R(\mu_\epsilon^{raw})\|)
    \]

    with \(\mathcal R(\mu_\epsilon)=0\).  Since the row defects are
    \(O(\epsilon)\), the correction is \(O(\epsilon)\) in the compactified
    topology, preserves positivity for small \(\epsilon\), and keeps

    \[
    |E_{\mu_\epsilon}|<M_{\rm oc}.
    \]

    Thus any strict non-regular counterexample whose row Jacobian regularizes
    produces a strict regular finite-gap counterexample, contradicting
    Gates 1--4.

    If no such invertible row Jacobian exists along the regularizing
    sequences, then some determinant in the regular chart tends to zero.  By
    the exhaustion in Gate 3, this can only be branch pinching, pole
    collision, multiple pole, residue zero, density sign loss,
    \(Z_0\)-collision, or anchor singularity.  Therefore failure of
    regularization is not a new case; it is a Gate 3 boundary/lower-genus
    collapse.

    Finally, the one-sided variations used in Proposition 4.1 are stable
    under the same approximation: \(C^1\) convergence near moving boundaries
    preserves boundary derivatives, local uniform convergence near \(Z_0\)
    preserves strict negativity after shrinking \(\epsilon\), and the positive
    density floor preserves compact lower bounds.  Hence no minimizer escapes
    the regular finite-gap exclusion by a loss of admissibility in the limit.

    Hence the intended regularization route is:

    \[
    \boxed{
    \textbf{Gate 5 status: proof route identified, Lemma R still required.}\quad
    \text{The row-restoration/regularization argument is not yet proof-grade.}
    }
    \tag{LemmaRStatus}
    \]

    To upgrade this to PASS, the compactified finite-gap charts, the
    row-restoration map, the IFT topology, preservation of positivity and
    strict length defect, and the equivalence between Jacobian degeneration and
    Gate 3 boundary collapse must be proved explicitly.  Until then, Lemma R
    is a proof obligation rather than a closed regularity-removal theorem.

    The remaining task on the upper side is to write the one-cut construction
    with exact defining equations and verify its admissibility.

    Gate 6: One-cut upper construction.

    The proof-grade upper construction is an exact one-parameter family; it
    does not require the infimum to be attained.  Define the branch by exact
    equations, not by the decimal value.
    For \(a\in(-1,1)\), set

    \[
    s(a)=\sqrt{2(1+a)},\qquad
    y(a)=\sqrt{\frac{1+a}{2}},
    \]

    and

    \[
    J(a)=\frac1\pi\int_a^1
    \frac{\log(1/(1-t))}
    {(t+1)\sqrt{(1-t)(t-a)}}\,dt.
    \]

    Define \(A(a)\) by the level equation

    \[
    U_a(1)=0,
    \qquad
    A(a)=
    \frac{\log(4/(1-a))}
    {\log2+s(a)J(a)}.
    \tag{G6A}
    \]

    Equivalently, after evaluating the integral,

    \[
    \log2+s(a)J(a)
    =
    \log\frac{1+y(a)}{1-y(a)}.
    \]

    Let \(c(a)=A(a)s(a)\), and define

    \[
    d\mu_a
    =
    A(a)\delta_{-1}
    +
    \frac{x+1-c(a)}
    {\pi(x+1)\sqrt{(1-x)(x-a)}}\,\mathbf1_{[a,1]}(x)\,dx.
    \tag{G6mu}
    \]

    The mass identity

    \[
    \frac1\pi\int_a^1
    \frac{dx}{(x+1)\sqrt{(1-x)(x-a)}}
    =
    \frac1{s(a)}
    \]

    gives continuous mass \(1-A(a)\), so \(\mu_a(\mathbb R)=1\).  The
    positivity condition is

    \[
    0\le A(a)\le y(a),
    \tag{G6pos}
    \]

    because \(x+1-c(a)\ge0\) on \([a,1]\) is equivalent to
    \(c(a)\le a+1\).  The admissible parameter set

    \[
    \mathcal A_{\rm oc}=\{a\in(-1,1):0<A(a)<y(a)\}
    \tag{G6Aset}
    \]

    is nonempty.  For example \(a=1/2\) gives

    \[
    A(1/2)=\frac{\log 8}{\log(7+4\sqrt3)}<\frac{\sqrt3}{2}=y(1/2),
    \]

    by elementary rational upper/lower bounds for the two logarithms.

    Fix the branch

    \[
    R_a(z)=\sqrt{(z-a)(z-1)},\qquad
    R_a(z)\sim z,\qquad R_a(z)<0\quad(z<a).
    \]

    For \(z\notin[a,1]\), the potential derivative is

    \[
    U_a'(z)
    =
    -\frac{z+1-c(a)}{(z+1)R_a(z)},
    \tag{G6dU}
    \]

    and the normalization is \(U_a(z)+\log|z|\to0\) at infinity.  The branch
    convention makes \(U_a\equiv0\) on \([a,1]\), because the boundary values
    of \(R_a\) are purely imaginary on the cut and the level equation fixes
    the additive constant.

    On the exterior real line the sign table from (G6dU) is:

    \[
    \begin{array}{c|c}
    \text{interval} & \operatorname{sign} U_a' \\ \hline
    (-\infty,-1) & + \\
    (-1,c(a)-1) & - \\
    (c(a)-1,a) & +
    \end{array}
    \tag{G6sign}
    \]

    Thus \(U_a\) is monotone on each exterior interval, tends to
    \(-\infty\) as \(z\to-\infty\), has the logarithmic singularity
    \(+\infty\) at the atom \(-1\) when \(A(a)>0\), and reaches level \(0\) on
    the cut.  Since \(0<A(a)<y(a)\) implies \(c(a)-1<a\), the last sign in
    (G6sign) gives

    \[
    U_a(c(a)-1)=-\int_{c(a)-1}^{a}U_a'(t)\,dt<0.
    \]

    It follows from the limits at \(-\infty\), \(-1\), \(c(a)-1\), and the
    cut endpoint \(a\) that there are exactly two exterior zeros:

    \[
    x_L(a)<-1<x_R(a)<c(a)-1<a,
    \qquad
    U_a(x_L(a))=U_a(x_R(a))=0.
    \tag{G6zeros}
    \]

    Moreover

    \[
    E_{\mu_a}=(x_L(a),x_R(a))
    \quad\text{up to endpoints},
    \qquad
    |E_{\mu_a}|=x_R(a)-x_L(a).
    \]

    Define the current one-cut candidate / provisional upper value by the
    exact variational equation

    \[
    M_{\rm oc}
    =
    \inf_{a\in\mathcal A_{\rm oc}}
    \bigl(x_R(a)-x_L(a)\bigr),
    \tag{G6M}
    \]

    The displayed decimal is only a numerical evaluation of (G6M), not a
    definition.  For every \(a\in\mathcal A_{\rm oc}\), \(\mu_a\) is
    admissible and \(|E_{\mu_a}|=x_R(a)-x_L(a)\).  Taking an infimizing
    sequence in \(\mathcal A_{\rm oc}\) gives the upper bound

    \[
    \boxed{
    L_-\le M_{\rm oc}.
    }
    \tag{G6upper}
    \]

    Therefore:

    \[
    \boxed{
    \textbf{Gate 6 result: PROOF-GRADE PASS.}\quad
    \text{The one-cut construction gives }L_-\le M_{\rm oc}\text{ with }
    M_{\rm oc}\text{ defined by exact equations.}
    }
    \]

    The last gate is theorem assembly, but it is conditional: Gates 1--5 give
    the lower exclusion only after the open Gate 1, Gate 3, Gate 4, and Gate 5
    proof obligations are closed.  Gate 6 gives the matching one-cut upper
    construction.

    Gate 7: Final theorem assembly.

    Conditional on the remaining Gate 1, Gate 3, Gate 4, and Gate 5 lemmas,
    Gates 1--5 prove the lower-bound exclusion.  Indeed, assume for
    contradiction that there is an admissible normalized minimizer with

    \[
    |E_\mu|<M_{\rm oc}.
    \]

    Lemma R (Gate 5) either regularizes \(\mu\) to regular finite-gap
    counterexamples with the same strict inequality, or routes \(\mu\) to a
    covered boundary/lower-genus branch.  In the regularized case, Gates 1--4
    would exclude every compact finite-gap chamber only after the remaining
    Gate 1 \(P_\theta\)-majorant checks and the Gate 3--5 compactness
    obligations are proved: regular \(g=2\), rank-defect \(g=2\),
    compactified \(g=2\) boundary, and all \(g\ge3\) local-neck reductions.  In
    the boundary case, Gate 3 routes to corrected \(g=1\),
    one-cut, lower genus, or an already excluded stratum.  The only remaining
    branch is the one-cut branch defining \(M_{\rm oc}\), and by definition of
    \(M_{\rm oc}\) no admissible one-cut element has length below
    \(M_{\rm oc}\).  Under those conditional inputs, this contradiction gives

    \[
    \boxed{
    L_-\ge M_{\rm oc}.
    }
    \tag{G7lower}
    \]

    Gate 6 gives the matching upper construction:

    \[
    \boxed{
    L_-\le M_{\rm oc}.
    }
    \tag{G7upper}
    \]

    Therefore the final assembly is still conditional:

    \[
    \boxed{
    \textbf{Gate 7 assembly: CONDITIONAL.}\quad
    \text{If Gates 1, 3, 5, and 6 are upgraded to proof-grade lemmas, then }
    L_- = M_{\rm oc}.
    }
    \tag{G7conditional}
    \]

    Here \(M_{\rm oc}\) is the value defined by the one-cut equations
    (G6A)--(G6M); the decimal \(1.8344304757626617\ldots\) is only its
    numerical evaluation.  The unconditional equality must not be asserted
    before the remaining proof obligations above are closed.

    A further finite-Hilbert equation follows only under an additional
    density/closure hypothesis: the allowed regularized seed class must be
    large enough, after equality correction, to test all smooth compactly
    supported density perturbations in \(J\).  If that density hypothesis is
    established, then the dual kernel is

    \[
    H_{\eta,\zeta}(x)
    =
    \eta\left(
    a\log\frac1{|x-u|}
    +b\log\frac1{|x-v|}
    \right)
    +U_\zeta(x)
    -
    (\eta\beta+\gamma)^TM^{-1}
    \binom{1}{(x-c)^{-1}},
    \tag{H}
    \]

    and annihilation of all smooth density tests gives \(H_{\eta,\zeta}=0\)
    on \(J\).  Differentiating this identity yields, up to the global sign
    convention in the \(R_c\)-row,

    \[
    \operatorname{p.v.}\int_J\frac{d\zeta(s)}{x-s}
    +
    \eta\left(\frac a{x-u}+\frac b{x-v}\right)
    =
    \frac{\Lambda_c}{(x-c)^2}.
    \tag{PV}
    \]

    This finite-Hilbert equation is a conditional fallback target, not yet a
    proved consequence of LP failure.  It should not be the next default
    route unless a density/closure theorem for the seed class is first proved.
    The immediate route is the finite-dimensional reduced Schiffer table and
    AtomicFallbackExclusion above.

    Caveats: this formula is only valid after the zero-mass/fixed-period
    convention is fixed, the period row is continuous in the separated chart,
    \(\operatorname{Rel}=0\) or the calculation is restricted to
    \(\operatorname{Rel}^{\perp}\), and all \(p_i^0\) are feasible row vectors.
    Here \(\operatorname{Rel}=0\) must mean independence as continuous
    functionals on the chosen Hilbert space, not only pointwise independence on
    smooth bumps.  The passage from the bump calculation to the Hilbert
    statement requires density of smooth compactly supported perturbations in
    the separated-chart energy space and continuity of every row.

    Stop/go for the Hessian step:

    - GO if the \(K_{\log}\) Gram contribution preserves the old five
      identities up to one positive scale, or if the actual-entry clamp still
      implies the Wronskian sign contradiction.
    - STOP this Hessian-clamp route if the actual entries give only generic
      PSD inequalities with no sign or ratio control.  In that case do not
      revive the old five-entry assumption; switch to direct actual-density or
      cone KKT endpoint tests.

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

Closing it by itself would not have proved \(L_- = M_{\rm oc}\).  The missing
bridges were the one-cut upper construction, the corrected lower-genus branch,
the pinching/degeneration lemma, the high-genus local-neck reduction, the
regularity-removal interface, and the normalized minimizer reduction.  Gates
3--7 above are the ledger closure of those bridges.
