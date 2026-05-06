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

The conjectural exact value is

\[
M_*=1.8344304757626617\ldots,
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

Useful corrections already recorded:

- the no-endpoint-atom ansatz is wrong;
- brute-force small-eta subdivision is not a main route;
- whole-slab `Div2` intervalization creates artificial eta dependency;
- the naive three-kernel compact determinant is invalid;
- the determinant must use split kernels;
- the pure-\(q\) Schur scalar is insufficient;
- the rank-six Schur conclusion was dimensionally wrong;
- the compact route now needs a KKT cokernel plus reduced Hessian identity.

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
L_-\le M_*.
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

The finite effective object, if the non-log part factors through
\(\rho^\sharp\), is

\[
Q_{\rm eff}(r)=\mathcal E_{\log}(Sr,Sr)+b(r,r),
\qquad r\in V^\sharp=\rho^\sharp(\mathcal X_\Pi).
\]

Separately, one should prove a row-realization lemma: smooth compactly
supported density bumps realize all row vectors in
\(\operatorname{Rel}^{\perp}\), and if the seven kernels

\[
1,(x-u)^{-1},(x-c)^{-1},(x-v)^{-1},L_-,L_+,
\log\frac1{|c-x|},\pi_0
\]

are independent, every period-zero enlarged row vector is actually realizable.
This supports Chebyshev tests, but it does not by itself make the Hessian
finite-dimensional.

Until the minimal-lift or actual-density formulation is closed, the six local
rows cannot be treated as arbitrary free Hessian coordinates.  Any cokernel
vector is meaningful only through its action on the actual row image \(V\).

After that, the curvature clamp needs exactly five reduced-Hessian identities:

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

### Priority 6: regularity interface

The previous priorities address regular finite-gap counterexamples.  The final
proof also needs a regularization statement:

\[
\textbf{Lemma R:}\quad
\text{every minimizing counterexample can be approximated by regular
finite-gap counterexamples,}
\]

without increasing \(|E_\mu|\) past the \(M_*\) threshold; otherwise the
sequence must already degenerate to a covered lower-genus branch.

This lemma should be stated as an interface until the finite-gap classification
is complete.  Do not silently assume it has been proved.

## 8. Forum Positioning

Separate the two messages:

1. Finite-certificate progress:

   > Conditional on the standard normalized minimizer reduction, a
   > required-domain 560-block five-atom certificate gives
   > \(L_-\ge1.814600\).

2. Exact route:

   > The corrected endpoint-atom two-interval finite-gap route supports the
   > candidate \(M_*=1.8344304757626617\ldots\), but the proof still needs
   > global interlacing-collapse / finite-gap classification.

Do not write "Erdős 1038 solved."  Do not merge the \(1.814600\) finite
certificate with the exact-value claim.
