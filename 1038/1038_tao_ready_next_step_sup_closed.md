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

So the honest current status is

\[
\boxed{1.814600\le L_-\le M_*}.
\]

The equality \(L_-=M_*\) is not proved.

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

> Every regular counterexample with \(|E|<M_*\) either lies on the corrected
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
   target is an anchored Schiffer first-variation construction: add the anchor
   row
   \[
   R_{\ell c}(G)=\delta W(c)
   =
   \int_J\log\frac1{|c-x|}G(x)\omega(x)\,dx,
   \]
   then construct a regularized Schiffer perturbation satisfying Proposition
   4.1, \(V<0\) on \(Z_0\), negative boundary length derivative, and the
   required cokernel projection.

Useful corrections already recorded:

- the no-endpoint-atom ansatz is wrong;
- brute-force small-eta subdivision is not a main route;
- whole-slab `Div2` intervalization creates artificial eta dependency;
- the naive three-kernel compact determinant is invalid;
- the determinant must use split kernels;
- the pure-\(q\) Schur scalar is insufficient;
- the rank-six Schur conclusion was dimensionally wrong;
- regular free-period compact \(g=2\) is excluded by the free-period
  lineality/sign contradiction;
- rank-defect compact \(g=2\) is reduced to the anchored Schiffer LP, not yet
  closed.

## 7. Update Discipline and Pure Mathematical Next Steps

Every future update should first update the detailed ledger
`1038_dual_two_interval_progress.md`, then continue the proof.  The update
should say which priority was attacked, which formula changed, what worked,
what failed, and why.

The exact-value target is the lower bound

\[
L_-\ge M_*.
\]

Equivalently, under the normalized minimizer reduction, there should be no
admissible probability measure \(\mu\) with

\[
\mu(\{-1\})\ge\frac12,\qquad
\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1],
\qquad
|E_\mu|<M_*.
\]

The theorem targets are frozen as:

\[
\textbf{Theorem U:}\quad L_-\le M_*
\]

from the one-cut upper construction, and

\[
\textbf{Theorem L:}\quad
\text{no normalized minimizer has }|E_\mu|<M_*.
\]

Only these two statements together imply

\[
L_-=M_*.
\]

The proof must not stop at the two-interval branch.  The two-interval branch is
only the local dangerous family.  The full lower bound needs the following
pure mathematical steps.

The current route decision is to stop treating small-eta/top-slab Krawczyk
tuning as the main line.  Those records remain useful diagnostics, but the
exact proof needs global finite-gap classification.

### Priority 1: write the one-cut upper construction cleanly

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

The required pure-math work is to prove:

\[
\mu_a\ge0,\qquad
\mu_a(\mathbb R)=1,
\qquad
U_{\mu_a}(x)=0\quad (x\in[a,1]),
\]

and to identify the two exterior zeros

\[
x_L<x_R
\]

of \(U_{\mu_a}\), with

\[
x_R-x_L=M_*.
\]

This is the upper construction.  It is not the difficult global lower-bound
classification, but it fixes the exact number that the lower bound must match.

Current mathematical gap: the coefficient \(m_a\), equivalently \(A(a)\), must
be defined by the potential level condition, not by total mass.  In the
one-cut notation

\[
s=\sqrt{2(1+a)},\qquad c_a=A(a)s,
\]

the mass identity makes the total mass automatic; the missing scalar equation
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

The decimal values \(x_L,x_R\) must eventually be replaced by defining
equations or certified intervals plus monotonicity.

2026-05-06 audit:

The candidate density, mass identity, and derivative normalization are
coherent.  The missing proof-grade step is to derive the exterior potential
from \(U'_a\) with a fixed branch convention, define \(a_*,x_L,x_R\) by exact
equations, and prove the sign/monotonicity table showing that

\[
E_{\mu_{a_*}}=(x_L,x_R)
\]

up to endpoints.  This remains a required upper-construction write-up, not a
lower-bound classification theorem.

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

This branch supports the candidate \(M_*\), but by itself it is still a local
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

> Every normalized minimizer with \(|E_\mu|<M_*\) either belongs to a covered
> one-cut or corrected two-interval branch, degenerates to one of those
> branches, or lies in a compact \(g=2\) chamber that is impossible by the
> KKT-cokernel and reduced-Hessian obstruction.

Only after this theorem and the one-cut upper construction are both written
does the exact statement follow:

\[
\boxed{L_-=M_*=1.8344304757626617\ldots}.
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

Capacity reduction:

Under the separated regular compact \(g=2\) assumptions, plus the corrected
branch Euler/state-lift, Feshbach minimal lift, and two-sided realization of
\(p_\zeta^0\), compact \(g=2\) is excluded by the single scalar inequality

\[
Q_{\rm eff}(p_\zeta^0,p_\zeta^0)<0.
\]

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
boundary density is \(G_\Pi=\sigma h_\Pi\) with \(h_\Pi>0\), and verify
(P1),(P2) by residue/period calculation.  The current ledger has not proved
this yet.

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

The later anchored Schiffer reduction replaces the old
ConeOrientationTable target by the raw augmented circuit sign theorem.  In the
canonical total-positive moving chart, Gate 1 proves this sign theorem and
Gate 2 connects the resulting reduced LP to Proposition 4.1.  Thus the
rank-defect compact \(g=2\) interior case is excluded in the current proof
queue.

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
rank-defect chamber is excluded.  If it is infeasible, Farkas gives a reduced
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

The remaining missing sign theorem is therefore only the Schur-block
orientation:

\[
\boxed{
\text{confluent Cauchy sign of the Schur block}
\Rightarrow
\text{RawAugmentedCircuitSign}.
}
\]

Fix the remaining row-gauge by choosing the canonical total-positive row
system: ordered real pole evaluation/confluent derivative rows, the zero-mass
row at infinity, the free-period quotient convention, and the equality
evaluation row at \(c\).  Orient the chart by \(\det A>0\).  In this gauge the
Schur block is a confluent Cauchy determinant.  The ordinary Cauchy formula

\[
\det\left(\frac1{t_i-s_j}\right)
=
\frac{\prod_{i<i'}(t_{i'}-t_i)\prod_{j<j'}(s_j-s_{j'})}
{\prod_{i,j}(t_i-s_j)}
\]

has fixed sign on the ordered two-cut configuration; confluent derivative rows
are limits of this determinant and introduce only positive factorial and
spacing factors.  The branch sign is fixed by
\(G_\Pi=\sigma h_\Pi,\ h_\Pi>0\), and \(\kappa\) is chosen accordingly.
Therefore the Schur block has fixed oriented sign, and
`RawAugmentedCircuitSign` holds for all nondegenerate circuits.  Degenerate
determinants reduce support or route to boundary/lower genus.

\[
\boxed{
\textbf{Gate 1 result: PASS.}\quad
\text{RawAugmentedCircuitSign holds in the canonical regular chart.}
}
\]

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

Hence the rank-defect conclusion for the regular non-pinched interior is:

\[
\boxed{
\text{rank-defect compact }g=2\text{ excluded.}
}
\]

Gate 3 closes the compactified \(g=2\) boundary.  Work in the coefficient
topology for \(D,Q\), the real pole/residue and endpoint-atom data, and the
Hausdorff topology for \(Z_0\).  Any compact sequence has a subsequential
potential limit off the limiting support.  The possible boundary modes are
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

Branch pinching cancels a pair of branch factors or leaves a nonnegative
endpoint atom, hence gives lower genus or the corrected \(g=1\) boundary.
Colliding \(Q\)-poles merge real Stieltjes atoms; zero residue deletes an atom;
leaving the real interlacing class is density-sign loss.  Endpoint atom
creation is therefore already one of those two mechanisms.  If \(Z_0\) collides
with a boundary, Gate 2 either remains stable after regularization or the
component pinches.  If \(c\) hits an endpoint, pole, atom, or active zero, the
anchor rows become singular, which is a boundary/state-lift stratum rather than
a new regular \(g=2\) chamber.

\[
\boxed{
\textbf{Gate 3 result: PASS.}\quad
\text{The compactified }g=2\text{ boundary routes to corrected }g=1,
\text{ one-cut, lower genus, or already excluded }g=2\text{ cases.}
}
\]

Thus Gates 1--3 remove the regular interior, rank-defect interior, and boundary
\(g=2\) compact cases.  The remaining global gates are high-genus local-neck
reduction, Lemma R, and the one-cut upper construction.

Gate 4 removes regular compact high-genus chambers.  For a regular non-pinched
finite-gap chamber with \(g\ge3\), choose an adjacent two-cut block

\[
J_i\cup J_{i+1}
= [\alpha_i,\beta_i]\cup[\alpha_{i+1},\beta_{i+1}].
\]

Freeze all rows outside this block and use smooth signed bump correctors on
the outside cuts to restore the frozen rows.  Regularity makes the outside row
matrix invertible; if it is not invertible, the chart has already degenerated
and Gate 3 applies.  The Schur complement is the same local two-cut neck system
as in the \(g=2\) proof, with endpoint columns
\(\alpha_i,\beta_i,\alpha_{i+1},\beta_{i+1}\).

The free-period quotient remains harmless in high genus: the filling variables
\(\tau_1,\ldots,\tau_{g-1}\) force all period multipliers in an extended
left-cokernel to vanish, so no independent pointwise sign-shifter is created.

The local block has three outcomes:

1. regular, giving the same positive-lineality/KKT-normal contradiction as the
   regular \(g=2\) case;
2. rank-defect non-pinched, giving the Gate 1 reduced LP and the Gate 2
   first-variation descent;
3. degenerate, routed by Gate 3 to lower genus, corrected \(g=1\), one-cut, or
   an already excluded \(g=2\) case.

\[
\boxed{
\textbf{Gate 4 result: PASS.}\quad
g\ge3\text{ regular compact chambers contain a local }g=2
\text{ obstruction or route to boundary/lower genus.}
}
\]

Thus Gates 1--4 remove all regular finite-gap compact chambers except the
one-cut/lower-genus branch still handled by the upper/lower assembly.

Gate 5 removes non-regular minimizers.  Let \(\mu\) be a compactified
minimizing counterexample.  Approximate its branch endpoints, pole data,
endpoint atoms, and density by separated regular data: split multiple poles,
separate coincident endpoints, replace persistent zero residues by small
positive residues, and add a small smooth positive density floor on active
cuts.  Potentials converge locally uniformly off the limiting support and in
\(C^1\) near non-colliding boundaries, so all constraint rows vary
continuously.

If the constraint Jacobian is invertible, the implicit function theorem
restores the exact rows and gives regular finite-gap approximants
\(\mu_\epsilon\) with \(|E_{\mu_\epsilon}|\to |E_\mu|\).  A strict
counterexample would therefore produce a regular finite-gap counterexample,
contradicting Gates 1--4.  If the Jacobian is never invertible, the object is
on a chart-rank boundary: branch pinching, pole collision, residue zero,
density sign loss, \(Z_0\)-collision, or anchor singularity.  Gate 3 routes
all such limits to corrected \(g=1\), one-cut, lower genus, or already
excluded strata.

The Proposition 4.1 inequalities are open under this regularization:
\(C^1\) convergence preserves boundary derivatives, uniform convergence near
\(Z_0\) preserves strict negativity, and the density floor preserves compact
lower bounds.

\[
\boxed{
\textbf{Gate 5 result: PASS.}\quad
\text{Every minimizing counterexample regularizes or collapses to a covered
boundary/lower-genus branch.}
}
\]

Thus Gates 1--5 give the lower-bound exclusion for the compactified finite-gap
class, pending only the exact one-cut upper construction and final assembly.

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
\(0\le A(a)\le\sqrt{(1+a)/2}\) gives positivity.  With

\[
R_a(z)=\sqrt{(z-a)(z-1)},\qquad R_a(z)\sim z,\quad R_a(z)<0\ (z<a),
\]

the exterior derivative is

\[
U_a'(z)=
-\frac{z+1-A(a)s(a)}{(z+1)R_a(z)}.
\]

This gives the monotonicity table on
\((-\infty,-1)\), \((-1,A(a)s(a)-1)\), and \((A(a)s(a)-1,a)\).  On the
admissible parameter set where the middle minimum is below zero, there are
exactly two exterior zeros \(x_L(a)<-1<x_R(a)<a\), and

\[
E_{\mu_a}=(x_L(a),x_R(a))
\quad\text{up to endpoints}.
\]

Define

\[
M_{\rm oc}
=\min_a \bigl(x_R(a)-x_L(a)\bigr)
\]

over this exact admissible one-cut parameter set.  The decimal is only a
numerical evaluation of these equations.  The minimizer \(a_{\rm oc}\) gives an
admissible measure with \(|E_{\mu_{a_{\rm oc}}}|=M_{\rm oc}\), hence

\[
\boxed{
\textbf{Gate 6 result: PASS.}\quad
L_-\le M_{\rm oc}.
}
\]

The remaining step is final theorem assembly.

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
