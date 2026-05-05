# Erdős 1038: one-step dual certificate setup (infimum, two-interval stage)

**Assumptions used explicitly**:
- **(A1)** Empirical-measure normalization: for a polynomial realization we use the monic empirical measure
  
  \[
  \mu_n := \frac1n\sum_{j=1}^n \delta_{x_j}, \qquad
  P_n(x):=\prod_{j=1}^n (x-x_j).
  \]
- **(A2)** Tao-style structural reduction is available as a conditional ingredient:
  any minimizing configuration for the infimum can be reduced to support in
  \(S := \{-1\}\cup[0,1]\).
- **(A3)** All measures below have finite logarithmic energy and are probability measures.

## 1) Potentials, the set \(E_\mu\), and the measure identity
Define the logarithmic potential

\[
U_\mu(x):=-\int_{\mathbb R} \log|x-t|\,d\mu(t), \qquad x\in\mathbb R,
\]

and the associated level function

\[
E_\mu:=\{x\in\mathbb R:U_\mu(x)>0\}.
\]

For \(\mu_n\),

\[
U_{\mu_n}(x)= -\frac1n \sum_{j=1}^n\log|x-x_j|=-\frac1n\log|P_n(x)|.
\]
So for this normalization

\[
\{x:|P_n(x)|<1\} = \{x:U_{\mu_n}(x)>0\}=E_{\mu_n},
\]

hence immediately

\[
\bigl|\{x:|P_n(x)|<1\}\bigr| = |E_{\mu_n}|_{\mathrm{Leb}}.
\]

When passing to weak limits \(\mu\) of empirical measures, the same correspondence is preserved for the limiting potential and candidate set

\[
\{x:|f_\mu(x)|<1\}=\{x:U_\mu(x)>0\}=E_\mu,
\]

with \(f_\mu=e^{-U_\mu}\) (a multiplicative constant from normalization can be absorbed at \(x=-1\) in the reduced class).

## 2) Reduction to \(S=\{-1\}\cup[0,1]\)
Accepting (A2), all subsequent duality checks are performed for measures \(\mu\) supported on

\[
S := \{-1\}\cup[0,1].
\]

Write

\[
\mathcal M := \{\mu: \mu\ge0,\ \mu(\mathbb R)=1,\ \mathrm{supp}(\mu)\subset S,\ I(\mu)<\infty\},
\]

where \(I\) is the logarithmic energy, and fix candidate sets by \(E_\mu\) as above.

## 3) Duality lemma (for proving non-minimality by one-step certificate)
Define the bilinear form

\[
\langle\mu,\nu\rangle := -\iint \log|x-y|\,d\mu(x)d\nu(y),
\]
where \(I(\mu,\nu)<\infty\), so that
\[
\langle\mu,\nu\rangle=\int U_\nu\,d\mu=\int U_\mu\,d\nu.
\]

**Lemma (dual certificate obstruction).**
Fix \(\mu\in\mathcal M\) and let \(E=E_\mu\). Let \(\nu\ge0\) be a finite measure with \(I(\mu,\nu)<\infty\), \(\nu(\{x\})\mu(\{x\})=0\) for all \(x\in\mathbb R\), and support in \(\mathbb R\setminus E\). If

1. \(U_\nu(x)\ge0\) for every \(x\in S\);
2. \(\nu\neq0\);
3. \(\int_S U_\nu\,d\mu > 0\),

then \(\mu\) cannot be a minimizer for the infimum constrained by \(E_\mu=E\).

*Proof.* Because \(\mathrm{supp}(\nu)\subset E^c\), by definition of \(E\) we have \(U_\mu(x)\le0\) on \(\mathrm{supp}(\nu)\), so

\[
\int U_\mu\,d\nu\le0.
\]

Since \(U_\nu\ge0\) on \(S\) and \(\mu\) is supported on \(S\), condition (3) gives

\[
\int U_\nu\,d\mu>0.
\]

Symmetry of the kernel gives

\[
\int U_\nu\,d\mu = \int U_\mu\,d\nu,
\]

contradicting the two inequalities. Therefore no such \(\nu\) can be excluded only by first-order variation if \(\mu\) were minimizing; equivalently, existence of such \(\nu\) is a valid dual certificate of non-minimality.  ∎

This is the one-step obstruction: once a nonnegative \(\nu\) with the two pointwise sign properties is explicit, the minimizer for a given \(E\) is ruled out.

## 4) Two-interval critical candidate and explicit ansatz for \(\lambda^{(\varepsilon)}\)
Let

\[
E_\varepsilon := (a_\varepsilon,b_\varepsilon)\cup(1-\varepsilon,1),\qquad a_\varepsilon<b_\varepsilon<1-\varepsilon,\ 0<\varepsilon\ll1.
\]

Translate Tao’s ansatz into the generic candidate

\[
\lambda^{(\varepsilon)} = d_\varepsilon\,\delta_1 + \sum_{j=1}^3 c_j^{(\varepsilon)}\,\delta_{x_j^{(\varepsilon)}} + g_\varepsilon(x)\,\mathbf 1_{[\alpha_\varepsilon,\beta_\varepsilon]}(x)\,dx.
\]
with \(x_1^{(\varepsilon)},x_2^{(\varepsilon)},x_3^{(\varepsilon)}\in E_\varepsilon^c\).

Take \(b_\varepsilon\le\alpha_\varepsilon<\beta_\varepsilon\), with \(\beta_\varepsilon:=1-\varepsilon\), and \(\alpha_\varepsilon=b_\varepsilon\) allowed only as the explicit limiting specialization of the exact-route closure, so \(\mathrm{supp}(\lambda^{(\varepsilon)})\subset E_\varepsilon^c\). The endpoint atom at \(1\) is part of the corrected active ansatz. The ac-density is taken from a Cauchy–Stieltjes branch form with square-root structure

\[
R_\varepsilon(z):=\sqrt{(z-a_\varepsilon)(z-b_\varepsilon)(z-\alpha_\varepsilon)(z-\beta_\varepsilon)},
\]

and, on \((\alpha_\varepsilon,\beta_\varepsilon)\),

\[
g_\varepsilon(x)=\frac1\pi\,\Im\left(\frac{A_\varepsilon x+B_\varepsilon}{x+1}\,R_\varepsilon^+(x)\right),\quad A_\varepsilon,B_\varepsilon\in\mathbb R.
\]

No sign-positivity assertion is made for \(g_\varepsilon\) yet; this is precisely what must be checked later.

### Matching equations from \(U_{\lambda^{(\varepsilon)}}=0\) on \([\alpha_\varepsilon,\beta_\varepsilon]\)
Set

\[
\Phi_\varepsilon(z):=\int \frac{d\lambda^{(\varepsilon)}(t)}{z-t}=-\frac{d}{dz}U_{\lambda^{(\varepsilon)}}(z).
\]

The condition \(U_{\lambda^{(\varepsilon)}}(x)=0\) for \(x\in[\alpha_\varepsilon,\beta_\varepsilon]\) gives

\[
\forall x\in(\alpha_\varepsilon,\beta_\varepsilon):\quad \operatorname{Re}\Phi_{\varepsilon,+}(x)=0,
\]

equivalently

\[
\operatorname{PV}\int_{\alpha_\varepsilon}^{\beta_\varepsilon}\frac{g_\varepsilon(t)}{x-t}\,dt+\frac{c_{1,\varepsilon}}{x+1}+\frac{d_{\varepsilon}}{x-1}+\sum_{k\in\{2,3\}}\frac{c_k^{(\varepsilon)}}{x-x_k^{(\varepsilon)}}=0.
\]

By the chosen square-root branch this is equivalent to the algebraic identity

\[
\frac{c_{1,\varepsilon}}{x+1}+\frac{d_{\varepsilon}}{x-1}+\sum_{k\in\{2,3\}}\frac{c_k^{(\varepsilon)}}{x-x_k^{(\varepsilon)}}=
\frac{(A_\varepsilon x+B_\varepsilon)\sqrt{(x-a_\varepsilon)(x-b_\varepsilon)}}{\sqrt{(x-\alpha_\varepsilon)(x-\beta_\varepsilon)}},
\quad x\in(\alpha_\varepsilon,\beta_\varepsilon).
\]

Introduce the meromorphic Stieltjes/Cauchy difference
\[
H_\varepsilon(z):=\frac{c_{1,\varepsilon}}{z+1}+\frac{d_{\varepsilon}}{z-1}+\sum_{k\in\{2,3\}}\frac{c_k^{(\varepsilon)}}{z-x_k^{(\varepsilon)}}-\frac{(A_\varepsilon z+B_\varepsilon)\sqrt{(z-a_\varepsilon)(z-b_\varepsilon)}}{\sqrt{(z-\alpha_\varepsilon)(z-\beta_\varepsilon)}}.
\]
The matching identity \(H_{\varepsilon,+}(x)=0\) for \(x\in(\alpha_\varepsilon,\beta_\varepsilon)\) is imposed here as the finite closure condition for the ansatz; it is not being derived solely from boundary vanishing without a separate analytic continuation argument. Under that additional analytic input, it yields

\[
\frac{c_{1,\varepsilon}}{x+1}+\frac{d_{\varepsilon}}{x-1}+\sum_{k\in\{2,3\}}\frac{c_k^{(\varepsilon)}}{x-x_k^{(\varepsilon)}}=
\frac{(A_\varepsilon x+B_\varepsilon)\sqrt{(x-a_\varepsilon)(x-b_\varepsilon)}}{\sqrt{(x-\alpha_\varepsilon)(x-\beta_\varepsilon)}},
\]
Squaring then yields a finite rational identity whose numerator can be cleared identically:

\[
\left(\frac{c_{1,\varepsilon}}{x+1}+\frac{d_{\varepsilon}}{x-1}+\sum_{k\in\{2,3\}}\frac{c_k^{(\varepsilon)}}{x-x_k^{(\varepsilon)}}\right)^2-
\frac{(A_\varepsilon x+B_\varepsilon)^2(x-a_\varepsilon)(x-b_\varepsilon)}{(x-\alpha_\varepsilon)(x-\beta_\varepsilon)}=0.
\]

This produces an explicit algebraic system in unknowns

\[
\{x_j^{(\varepsilon)},c_j^{(\varepsilon)}\}_{j=1}^3\cup\{d_\varepsilon,\alpha_\varepsilon,a_\varepsilon,b_\varepsilon,A_\varepsilon,B_\varepsilon,C_\varepsilon\}
\]

together with the following independent equations (all are exact symbolic conditions):

1. mass: \(\sum_{j=1}^3 c_j^{(\varepsilon)}+d_\varepsilon+\int_{\alpha_\varepsilon}^{\beta_\varepsilon}g_\varepsilon(t)dt=1\);
2. first moment normalization (depending on chosen affine normalization in Tao reduction):
   \(\sum_{j=1}^3 c_j^{(\varepsilon)}x_j^{(\varepsilon)}+d_\varepsilon+\int_{\alpha_\varepsilon}^{\beta_\varepsilon}t g_\varepsilon(t)dt=0\) (equivalently the fixed affine normalization \(\int_{\mathbb R}x\,d\lambda^{(\varepsilon)}=0\) used for reduction);
3. value constraints on the obstacle boundary:
   \(U_{\lambda^{(\varepsilon)}}(a_\varepsilon)=0\), \(U_{\lambda^{(\varepsilon)}}(b_\varepsilon)=0\), \(U_{\lambda^{(\varepsilon)}}(\beta_\varepsilon^-)=0\);
4. atom locations:
   \(x_1^{(\varepsilon)}=-1\), \(x_2^{(\varepsilon)},x_3^{(\varepsilon)}\in E_\varepsilon^c\), and \(1\in E_\varepsilon^c\);
5. residue matching at each atom:
   \(c_j^{(\varepsilon)} = -\lim_{x\to x_j^{(\varepsilon)}} (x-x_j^{(\varepsilon)})\frac{(A_\varepsilon x+B_\varepsilon)\sqrt{(x-a_\varepsilon)(x-b_\varepsilon)}}{\sqrt{(x-\alpha_\varepsilon)(x-\beta_\varepsilon)}}\) for \(j=1,2,3\), and \(d_\varepsilon\) is the residue at \(z=1\) in the full Cauchy transform;
6. asymptotic matching of \(\Phi_\varepsilon\) at infinity to enforce the probability normalization and the affine normalization inherited from the polynomial setting.

These are the finite algebraic conditions that replace raw numerical matching and can be fed into exact arithmetic verification.

## 5) Concrete next algebraic check list (finite, interval-arithmetic-ready)
To go from numeric candidate parameters to a rigorous proof, check only finitely many signs/intervals:

1. Solve the finite algebraic system in (1)–(6) for each target \(\varepsilon\), obtaining an interval enclosure for all unknowns.
2. Form the cleared polynomial equation obtained from the squared matching identity above; isolate all real roots in each component of \(\mathbb R\setminus[\alpha_\varepsilon,\beta_\varepsilon]\), i.e. stationary points of the potential. This is a finite-root problem.
3. At every endpoint \(x\in\{\alpha_\varepsilon,a_\varepsilon,b_\varepsilon,\beta_\varepsilon,1\}\), compute interval-enclosed bounds for one-sided limits of \(U_{\lambda^{(\varepsilon)}}(x)\), \(\frac{d}{dx}U_{\lambda^{(\varepsilon)}}(x)\).
4. Evaluate \(U_{\lambda^{(\varepsilon)}}\) at representative points and at each stationary point in each complement interval.
5. Verify the dual certificate sign conditions with interval bounds, with \(\nu:=\lambda^{(\varepsilon)}\):
   - \(\nu\ge0\) (all atoms and density nonnegative);
   - \(\mathrm{supp}(\nu)\subset E_\varepsilon^c\);
   - atom support: \(x_1^{(\varepsilon)},x_2^{(\varepsilon)},x_3^{(\varepsilon)}\in E_\varepsilon^c\);
   - \(U_\nu\ge0\) on \(S\);
   - \(\int_S U_\nu\,d\mu>0\) (equivalently \(\int U_\nu\,d\mu>0\) since \(\mu(S)=1\));
   - \(U_{\nu}\) satisfies the sign/normalization checks needed to invoke the duality lemma in §3.

With (4)–(6), the lemma in §3 gives a conditional dual obstruction once the positivity/support/sign checks are verified.

## 6) Task2: explicit \(\varepsilon\)-system closure and parameter reduction

## 7) Task 7: conservative \((-1.7,0)\) forcing grid verifier
已加入一个只用 Python 标准库的确定性 2D 网格检查脚本，按三角域
\(a\in[-1.7,-\sqrt2]\), \(b\in[0,1.82+a]\) 采样，并在 \(\{-1\}\cup[0,1]\)
上对 \(U\) 的端点与二次临界点做数值最小值检查。

这一步仍然只是探索性验证：它可以稳定支持这支二维 forcing family 的数值筛查，
并定位可能的最坏点，但真正的证明仍然需要 box interval arithmetic 来封口。

The old no-endpoint-atom \(\varepsilon\)-closure is retired as an active ansatz; the active exact-route ansatz is the corrected one with an endpoint atom at \(1\), cross-referenced in §11.3.

Set \(\beta_\varepsilon:=1-\varepsilon\) and fix
\[
E_\varepsilon=(a_\varepsilon,b_\varepsilon)\cup(\beta_\varepsilon,1),
\]
with strict order
\[
0<a_\varepsilon<b_\varepsilon<\beta_\varepsilon<1.
\]
\[
b_\varepsilon\le\alpha_\varepsilon<\beta_\varepsilon
\]
Use \(b_\varepsilon\le\alpha_\varepsilon<\beta_\varepsilon\); equality \(\alpha_\varepsilon=b_\varepsilon\) is only an optional limiting specialization, so that the continuous support is disjoint from \((a_\varepsilon,b_\varepsilon)\):
\[
\operatorname{supp}(\lambda^{(\varepsilon)})\subset\{-1,1,x_{2,\varepsilon},x_{3,\varepsilon}\}\cup[\alpha_\varepsilon,\beta_\varepsilon]\subset E_\varepsilon^c,
\]

If your source uses \((b_\varepsilon,a_\varepsilon)\), interpret it as the renaming
\(a_\varepsilon\leftrightarrow b_\varepsilon\); all formulas below use
\(a_\varepsilon<b_\varepsilon\).

Use the reduced support choice \(S=\{-1\}\cup[0,1]\) by setting
\[
x_{1,\varepsilon}=-1,\qquad x_{2,\varepsilon}< -1,\qquad x_{3,\varepsilon}>1.
\]

Then write
\[
\lambda^{(\varepsilon)}=c_{1,\varepsilon}\delta_{-1}+d_{\varepsilon}\delta_1+c_{2,\varepsilon}\delta_{x_{2,\varepsilon}}+c_{3,\varepsilon}\delta_{x_{3,\varepsilon}}+g_\varepsilon(x)\mathbf 1_{[\alpha_\varepsilon,\beta_\varepsilon]}(x)\,dx,
\]
with
\[
g_\varepsilon(x)=
\frac{1}{\pi}\,\Im\left(
\frac{A_\varepsilon x^2+B_\varepsilon x+C_\varepsilon}{x+1}
\frac{\sqrt{(x-a_\varepsilon)(x-b_\varepsilon)}}{\sqrt{(x-\alpha_\varepsilon)(x-\beta_\varepsilon)}}
\right),\quad x\in(\alpha_\varepsilon,\beta_\varepsilon),
\]
with the Cauchy--Stieltjes branch chosen so that \(g_\varepsilon\) is real on \((\alpha_\varepsilon,\beta_\varepsilon)\).
This is now the active exact-route ansatz; the earlier no-endpoint-atom \(\varepsilon\)-closure is retired. Any active closure system must include the endpoint atom at \(1\) (the \(d_\varepsilon\delta_1\) term here); see §11.3.

Define
\[
W_\varepsilon(z):=\int\frac{d\lambda^{(\varepsilon)}(t)}{z-t}
=\frac{c_{1,\varepsilon}}{z+1}+\frac{d_{\varepsilon}}{z-1}+\frac{c_{2,\varepsilon}}{z-x_{2,\varepsilon}}+\frac{c_{3,\varepsilon}}{z-x_{3,\varepsilon}}+\int_{\alpha_\varepsilon}^{\beta_\varepsilon}\frac{g_\varepsilon(t)}{z-t}dt.
\]

Contact condition \(U_{\lambda^{(\varepsilon)}}(x)=0\) on \((\alpha_\varepsilon,\beta_\varepsilon)\) is equivalent to \(U'_{\lambda^{(\varepsilon)}}(x)=0\), hence
\[
\frac{c_{1,\varepsilon}}{x+1}+\frac{d_{\varepsilon}}{x-1}+\sum_{k\in\{2,3\}}\frac{c_{k,\varepsilon}}{x-x_{k,\varepsilon}}+\mathrm{PV}\int_{\alpha_\varepsilon}^{\beta_\varepsilon}\frac{g_\varepsilon(t)}{x-t}dt=0,\qquad x\in(\alpha_\varepsilon,\beta_\varepsilon).
\]

With the Cauchy--Stieltjes branch in \(g_\varepsilon\), this is equivalent to the boundary equation
\[
H_\varepsilon(x):=(x+1)(x-1)\sqrt{(x-\alpha_\varepsilon)(x-\beta_\varepsilon)}\left(\frac{c_{1,\varepsilon}}{x+1}+\frac{d_{\varepsilon}}{x-1}+\sum_{k\in\{2,3\}}\frac{c_{k,\varepsilon}}{x-x_{k,\varepsilon}}\right)-i(A_\varepsilon x^2+B_\varepsilon x+C_\varepsilon)\sqrt{(x-a_\varepsilon)(x-b_\varepsilon)}=0.
\]
Hence the squared branch identity is
\[
\left((x+1)(x-1)\sqrt{(x-\alpha_\varepsilon)(x-\beta_\varepsilon)}\left(\frac{c_{1,\varepsilon}}{x+1}+\frac{d_{\varepsilon}}{x-1}+\sum_{k\in\{2,3\}}\frac{c_{k,\varepsilon}}{x-x_{k,\varepsilon}}\right)\right)^2+ (A_\varepsilon x^2+B_\varepsilon x+C_\varepsilon)^2 (x-a_\varepsilon)(x-b_\varepsilon)=0,
\]
for \(x\in(\alpha_\varepsilon,\beta_\varepsilon)\).

To close this as a finite algebraic system, clear poles at \(x=x_{2,\varepsilon},x_{3,\varepsilon}\):
\[
Q_\varepsilon(x):=(x-x_{2,\varepsilon})^2(x-x_{3,\varepsilon})^2\left[(x+1)^2(x-1)^2(x-\alpha_\varepsilon)(x-\beta_\varepsilon)\left(\frac{c_{1,\varepsilon}}{x+1}+\frac{d_{\varepsilon}}{x-1}+\sum_{k\in\{2,3\}}\frac{c_{k,\varepsilon}}{x-x_{k,\varepsilon}}\right)^2
+(A_\varepsilon x^2+B_\varepsilon x+C_\varepsilon)^2 (x-a_\varepsilon)(x-b_\varepsilon)\right].
\]
Then \(Q_\varepsilon\equiv 0\) is the closure identity in the reduced parameterization; coefficient matching gives finitely many equations in
\[
\Theta_\varepsilon=(\alpha_\varepsilon,\beta_\varepsilon,a_\varepsilon,b_\varepsilon,x_{2,\varepsilon},x_{3,\varepsilon},A_\varepsilon,B_\varepsilon,C_\varepsilon,c_{1,\varepsilon},d_{\varepsilon},c_{2,\varepsilon},c_{3,\varepsilon}).
\]

Practical closed system (explicit equations):

1. Support check (disjointness from \(E_\varepsilon\)):
\[
x_{2,\varepsilon}< -1,\qquad x_{3,\varepsilon}>1,\qquad b_\varepsilon\le\alpha_\varepsilon<\beta_\varepsilon=1-\varepsilon,
\]
This ensures \(\mathrm{supp}(\lambda^{(\varepsilon)})\subset E_\varepsilon^c\) via the support decomposition above.

2. Mass:
\[
\int_{\alpha_\varepsilon}^{\beta_\varepsilon} g_\varepsilon(x)\,dx+c_{1,\varepsilon}+d_{\varepsilon}+c_{2,\varepsilon}+c_{3,\varepsilon}=m_0,
\quad m_0=\left|\lambda^{(\varepsilon)}\right| \; (\text{often }m_0=1).
\]

3. First moment:
\[
\int_{\alpha_\varepsilon}^{\beta_\varepsilon}x g_\varepsilon(x)\,dx-c_{1,\varepsilon}+d_{\varepsilon}+c_{2,\varepsilon}x_{2,\varepsilon}+c_{3,\varepsilon}x_{3,\varepsilon}=m_1^{\mathrm{fix}}.
\]

4. Stieltjes infinity matching (correct scaling):
\[
\lim_{|z|\to\infty} zW_\varepsilon(z)=m_0,
\quad
\lim_{|z|\to\infty}\left(z^2W_\varepsilon(z)-m_0 z\right)=m_1.
\]
Equivalently,
\[
z^2W_\varepsilon(z)=m_0 z+m_1+o(1).
\]
where
\[
m_0=\left|\lambda^{(\varepsilon)}\right| \; (\text{often }m_0=1),\qquad
m_1=\int t\,d\lambda^{(\varepsilon)}(t)=\int_{\alpha_\varepsilon}^{\beta_\varepsilon}x g_\varepsilon(x)\,dx-c_{1,\varepsilon}+d_{\varepsilon}+c_{2,\varepsilon}x_{2,\varepsilon}+c_{3,\varepsilon}x_{3,\varepsilon}.
\]

5. Contact-value closure on active edges (or equivalent finite-point normalization):
\[
U_{\lambda^{(\varepsilon)}}(a_\varepsilon)=0,\quad
U_{\lambda^{(\varepsilon)}}(b_\varepsilon)=0,\quad
U_{\lambda^{(\varepsilon)}}(\beta_\varepsilon^-)=0,\quad
U_{\lambda^{(\varepsilon)}}(0)=\kappa_\varepsilon \text{ (normalization constant)}.
\]

6. Residue-at-atom extraction from \(W_\varepsilon\):
\[
\operatorname{Res}_{z=x_{2,\varepsilon}} W_\varepsilon(z)=c_{2,\varepsilon},\qquad
\operatorname{Res}_{z=x_{3,\varepsilon}} W_\varepsilon(z)=c_{3,\varepsilon},\qquad
\operatorname{Res}_{z=-1}W_\varepsilon(z)=c_{1,\varepsilon},\qquad
\operatorname{Res}_{z=1}W_\varepsilon(z)=d_{\varepsilon}.
\]

This is an explicit closed \(\varepsilon\)-system once the reduction convention is fixed; the remaining step is to solve it with interval arithmetic and feed the output to the sign checks in §5.

## 7) Task3: ε→0 的有限维延拓 + 弱扰动稳定性框架

将 Task2 的未知量记为
\[
\Theta_\varepsilon=
(a_\varepsilon,b_\varepsilon,x_{2,\varepsilon},x_{3,\varepsilon},
A_\varepsilon,B_\varepsilon,C_\varepsilon,
c_{1,\varepsilon},d_\varepsilon,c_{2,\varepsilon},c_{3,\varepsilon},\alpha_\varepsilon).
\]
记
\[
F(\varepsilon,\Theta_\varepsilon)=
\left(\text{Task2 的 1--6 方程左端}\right)\in\mathbb R^N,
\]
其中 \(N\) 为所选独立等式条目的总数（可与方程冗余一并由数值消去）。在可行区域
\[
\mathcal U:=\{a<b,\ b\le\alpha<\beta=1-\varepsilon,\ x_2<-1,\ x_3>1,\ \beta\in(0,1)\}
\]
中，\(F\) 由有理函数与根号组成，故对 \((\varepsilon,\Theta)\) 为 \(C^1\)（实际实现时用固定主值分支固定符号）。

设极限参数
\[
\Theta_0=(a_0,b_0,x_{2,0},x_{3,0},A_0,B_0,C_0,c_{1,0},d_0,c_{2,0},c_{3,0},\alpha_0)
\]
so the limit system is the \(\varepsilon\to0\) specialization of the active four-atom ansatz.
满足
\[
F(0,\Theta_0)=0.
\]

【非退化条件】
取 \(N=\dim\Theta_\varepsilon\) 个独立闭包方程（若原方程组冗余，先删去冗余行），要求
\[
\det D_{\Theta}F(0,\Theta_0)\neq0
\]
（或等价秩条件）则由隐函数定理得
\[
\Theta_\varepsilon=\Phi(\varepsilon),\qquad |\varepsilon|<\varepsilon_1,
\]
且 \(\Phi\) 为 \(C^1\)。于是 \(\Theta_\varepsilon\to\Theta_0\), 并有
\[
x_{2,\varepsilon}<-1,\quad x_{3,\varepsilon}>1,\quad a_\varepsilon<b_\varepsilon,\quad b_\varepsilon\le\alpha_\varepsilon<\beta_\varepsilon.
\]
More concretely for the exact route, keep \(b_\varepsilon\le\alpha_\varepsilon<\beta_\varepsilon\); equality \(\alpha_\varepsilon=b_\varepsilon\) is only an optional limiting specialization if one chooses that reduced closure.
对应对偶测度记作
\[
\lambda^{(\varepsilon)}=\lambda_{\Theta_\varepsilon},\qquad U_\varepsilon:=U_{\lambda^{(\varepsilon)}}.
\]
在 \(S\setminus\{-1,0,1\}\) 的每个紧集 \(K\subset S\setminus\{-1,0,1\}\) 上，参数光滑性给出
\[
\sup_{x\in K}|U_\varepsilon(x)-U_0(x)|\le C_K|\varepsilon|.
\]

【稳定命题（远离临界边界）】
若 \(K\subset S\setminus\{-1,0,1\}\) 且 \(\delta_K:=\inf_{x\in K}U_0(x)>0\)，则对足够小的 \(\varepsilon\),
\[
\inf_{x\in K}U_\varepsilon(x)\ge\delta_K/2>0.
\]
该命题把“基准非退化正裕度”传递到小 \(\varepsilon\)。

【边界/临界点修正】
临界区仅在有限点集和其邻域内可能出现 \(U_0=0\)，包括 \(\{a_0,b_0,\beta_0\}\) 附近及 \(\mathcal R_0:=\{x\in(\alpha_0,\beta_0):U_0'(x)=0\}\)（可由 \(Q_0\) 的临界方程给出）。对这些点需改为有限验收：
1. 计算展开
\[
U_\varepsilon(x)=U_0(x)+\varepsilon\,\dot U_0(x)+O(\varepsilon^2),
\]
并在每个临界点给出一阶项下界；
2. 检查
\[
U_\varepsilon(a_\varepsilon),\ U_\varepsilon(b_\varepsilon),\ U_\varepsilon(\beta_\varepsilon^-)\ge0;
\]
3. 在每个间隙区间里，枚举 \(\mathcal R_\varepsilon\) 的根并检验 \(U_\varepsilon\ge0\)（根由 \(H_\varepsilon\) 的有界阶代数方程给出，故只需有限根隔离）。

同时保持原子非负
\[
c_{1,\varepsilon},d_\varepsilon,c_{2,\varepsilon},c_{3,\varepsilon}\ge0.
\]
若 (1)-(3) 成立，得到
\[
\lambda^{(\varepsilon)}\ge0,\quad
\mathrm{supp}(\lambda^{(\varepsilon)})\subset E_\varepsilon^c,\quad
U_{\lambda^{(\varepsilon)}}\ge0\ \text{on }S.
\]
然后由 §3 的对偶引理可排除对应 \(E_\varepsilon\) 为真最小值候选。

【失败信号与反例分支】
若边界展开或驻点检查中出现
\[
\inf_{x\in S\setminus E_\varepsilon}U_\varepsilon(x)<0
\]
沿任一闭包支路成立，则 two-interval 对偶方案在该方向上失败，应切换到反例构造，直接用对应 \(\mu_\varepsilon\) 给出 \(|E_{\mu_\varepsilon}|<M_*\) 的候选序列。

### Task4（下一步、可验）
对 \(\varepsilon\in(0,\varepsilon_1]\) 做区间算术版可执行清单：
1. 解 \(F(\varepsilon,\Theta)=0\)，给出 \(\Theta_\varepsilon\) 的区间包络；
2. 验证每个 \(\Theta_\varepsilon\) 满足有序性与支撑分离；
3. 在 \(S\) 的各固定段上，检查 \(U_{\lambda^{(\varepsilon)}}\) 的端点和驻点值下界及其单调性；
4. 检查 \(g_\varepsilon\ge0\) 与 \(c_{k,\varepsilon}\ge0\)；
5. 得到
\[
\nu=\lambda^{(\varepsilon)}\ge0,\quad
\mathrm{supp}(\nu)\subset E_\varepsilon^c,\quad
U_\nu\ge0\ \text{on }S,\quad
\int_S U_\nu\,d\mu>0.
\]
即得到 \(E_\varepsilon\) 的对偶否定；若第五步在某区间失败，记录失败参数以推进反例分支。

#### Task4 子任务拆解（直接落执行）
Task4a. 取 \(\varepsilon\)-网格 \(0<\varepsilon_1<\cdots<\varepsilon_M=\varepsilon_0\)，在每个小段上固定 \(\beta_\varepsilon=1-\varepsilon\)。

Task4b. 在每个 \(\varepsilon\)-小段内，用 Newton+区间包 (interval Newton/Krawczyk) 求解
\[
F(\varepsilon,\Theta)=0
\]
并输出 \(\Theta_\varepsilon\) 在该段内的 \(C^0\) 包络，必要时再给出 \(\partial_\varepsilon \Theta_\varepsilon\) 包络。

Task4c. 计算
\[
U_{\lambda^{(\varepsilon)}}(x)=U_0(x)+(\varepsilon-\varepsilon_*)\dot U_{\varepsilon_*}(x)+R_{\varepsilon_*}(x)
\]
并用区间法严格界定 \(\sup_x|R_{\varepsilon_*}(x)|\)；在稳定区给出 \(\delta/2\) 边界。

Task4d. 对临界集合
\[
\mathcal K_{\varepsilon}= \{-1,0,1,a_\varepsilon,b_\varepsilon,\alpha_\varepsilon,\beta_\varepsilon\}\cup\mathcal R_\varepsilon
\]
做符号判定与根隔离，输出每点/每段的 \(U_{\lambda^{(\varepsilon)}}\) 下界。

完成 a-d 后自动化产出对偶证书不等式；若失败，切到反例构造子任务。

## Current status / exact next task
**Current status:** two-interval/IFT 路线有意义，但不是当前最小成本主线。它是 exact infimum 的长期路线；短期 forum-ready 成果已经从固定三原子 \(1.7877\) 和 \(1.8\) 路线推进到 §14.4 的五原子 \(1.8063\) certificate-backed package。

**Parked exact-route task:** 若重新启动 exact inf 路线，应先把 ansatz 的独立方程块、基准参数 \(\Theta_0\)、Jacobian 非退化检查和数值初值固定下来，再做 Task4a--d。现在直接做 \(\varepsilon\)-网格/Krawczyk 会过早，因为 \(F(\varepsilon,\Theta)\) 仍未完全锁定成可执行系统。

**Current active priority:** 
1. 若继续 lower-bound 方向，优先尝试把 §14.4 的五原子 \(1.8063\) 再推到 \(1.8064\) 或证明当前模板在 \(1.8064\) 失败；
2. 并行可研究 comments 中变量权重三原子约 \(1.7902\) 的严格 interval certificate；
3. exact infimum 主线仍回到本 §7/Task4：修正后的 endpoint-atom two-interval ansatz、Jacobian 非退化与 \(U_\lambda\ge0\) 的解析验证。

对偶目标仍为
\[
\nu\ge0,\qquad \mathrm{supp}(\nu)\subset E_\varepsilon^c,\qquad U_\nu\ge0\text{ on }S,\qquad \int_S U_\nu\,d\mu>0.
\]
然后直接由 §3 的对偶引理得出：若 \(\mu\) 满足 \(E_\mu=E_\varepsilon\)，则该候选不可能是最小化解（因对偶矛盾）。 

## 8) A closed three-atom lower-bound certificate: \(L_-\ge 1.7875\)

This section is independent of the two-interval exact-infimum program above. It uses the same logarithmic-potential duality, but in a simpler covering form. It gives a certificate-backed lower-bound statement, conditional on the standard Tao/natso reduction to
\[
\mu(\{-1\})\ge\frac12,\qquad \operatorname{supp}\mu\subseteq \{-1\}\cup[0,1].
\]

Set
\[
M=\frac{143}{80}=1.7875,\quad
A=\frac{25507}{20000}=1.27535,\quad
B=\frac{34971}{100000}=0.34971,\quad
D=\frac{136711}{50000}=2.73422.
\]

### Lemma 8.1: the forced base interval

If \(p=\mu(\{-1\})\ge1/2\) and \(\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1]\), then
\[
(-\sqrt2,0)\subseteq E_\mu.
\]

Indeed, for \(x\in(-\sqrt2,0)\) and \(0\le t\le1\),
\[
\log\frac1{|x-t|}\ge \log\frac1{|x-1|}.
\]
Since \(|x-1|>|x+1|\), the lower bound is increasing in \(p\), hence
\[
U_\mu(x)\ge
\frac12\log\frac1{|x+1|}
+\frac12\log\frac1{|x-1|}
=\frac12\log\frac1{|x^2-1|}>0.
\]

### Lemma 8.2: three-atom forcing

For each \(a\in[-M,-\sqrt2]\), define
\[
\nu_a=\delta_a+A\delta_{a+M}+B\delta_{a+D}.
\]
Then
\[
U_{\nu_a}(x)>0,\qquad -1\le x\le1.
\]

Writing \(y=x-a\), this reduces to
\[
V(y):=\log\frac1{|y|}
+A\log\frac1{|y-M|}
+B\log\frac1{|y-D|}>0
\]
on
\[
[\sqrt2-1,1+M]=[\sqrt2-1,2.7875].
\]
The only singularities in this interval are \(y=M,D\), where \(V(y)\to+\infty\). On the smooth pieces, critical points satisfy
\[
1312530000y^2-4316957051y+2443709125=0,
\]
with
\[
r_1\in(0.72658138,0.72658139),\qquad
r_2\in(2.56245357,2.56245358).
\]
Interval evaluation gives
\[
V(\sqrt2-1)>0.1825,\quad
V(r_1)>2.5\cdot10^{-4},\quad
V(r_2)>2.4\cdot10^{-4},\quad
V(1+M)>2.7\cdot10^{-4}.
\]
Therefore \(V>0\) on the full interval.

### Lemma 8.3: covering step

Let
\[
I=(-M,-\sqrt2),\qquad F=E_\mu\setminus(-\sqrt2,0).
\]
For each \(a\in I\), Lemma 8.2 gives \(U_{\nu_a}>0\) on \(\operatorname{supp}\mu\). If none of
\[
a,\quad a+M,\quad a+D
\]
belonged to \(E_\mu\), then
\[
\int U_\mu\,d\nu_a\le0
\]
while by kernel symmetry
\[
\int U_\mu\,d\nu_a=\int U_{\nu_a}\,d\mu>0,
\]
a contradiction. Thus at least one of the three points belongs to \(E_\mu\).

The three translated intervals are
\[
I_0=I,\qquad
I_1=I+M=(0,M-\sqrt2),\qquad
I_2=I+D=(D-M,D-\sqrt2).
\]
They are pairwise disjoint and disjoint from \((-\sqrt2,0)\). Hence
\[
|I|\le |F\cap I_0|+|F\cap I_1|+|F\cap I_2|\le |F|.
\]
Using Lemma 8.1,
\[
|E_\mu|\ge \sqrt2+|I|=\sqrt2+(M-\sqrt2)=M.
\]

### Conclusion

Under the standard reduced-minimizer hypothesis,
\[
\boxed{|E_\mu|\ge 1.7875.}
\]
Consequently, for the original polynomial problem after applying the Tao/natso reduction,
\[
\boxed{L_-\ge1.7875.}
\]

This is a closed lower-bound certificate. The earlier two-interval sections remain the route toward the conjectural exact value \(1.8344304757\ldots\); they are not needed for this \(1.7875\) bound.

### Forum-strength fixed-parameter upgrade candidate: \(M=1.7877\) (reproducible high-precision finite certificate PASS; formal directed logs still pending for a written-proof upgrade)

The same three-atom covering template is the forum-strength upgrade candidate at the fixed rational parameters
\[
M=\frac{17877}{10000},\qquad
A=\frac{127383}{100000},\qquad
B=\frac{34979}{100000},\qquad
D=\frac{136718}{50000}.
\]
For each \(a\in[-M,-\sqrt2]\), define
\[
\nu_a=\delta_a+A\delta_{a+M}+B\delta_{a+D}.
\]
Writing \(y=x-a\) reduces the positivity check to
\[
V(y)=\log\frac1{|y|}+A\log\frac1{|y-M|}+B\log\frac1{|y-D|}>0
\]
on
\[
[\,\sqrt2-1,1+M\,]=\Bigl[\,\sqrt2-1,\frac{27877}{10000}\Bigr].
\]

The finite check is still the right one:

1. endpoints \(y=\sqrt2-1\) and \(y=1+M\);
2. the two critical points of \(V\), given by the quadratic derivative numerator
   \[
   Q(y)=\frac{131181}{50000}y^2-\frac{43152446909}{5000000000}y+\frac{1222053843}{250000000};
   \]
   equivalently,
   \[
   N(y)=13118100000\,y^2-43152446909\,y+24441076860,
   \]
   after multiplying by \(5000000000\);
3. the singularities at \(y=M\) and \(y=D\), where \(V(y)\to+\infty\).

A tighter rational root-isolation bracket that reduces the proof to finitely many point checks is
\[
r_1\in\Bigl[\frac{72710566}{100000000},\frac{72710567}{100000000}\Bigr],
\qquad
r_2\in\Bigl[\frac{256242916}{100000000},\frac{256242917}{100000000}\Bigr],
\]
since \(N(72710566/100000000)>0\) and \(N(72710567/100000000)<0\), while \(N(256242916/100000000)<0\) and \(N(256242917/100000000)>0\). This is enough to isolate the two real roots by IVT once a directed interval pass is run.

The current conservative lower bounds are:
\[
V(\sqrt2-1)>\frac{1827}{10000},
\]
\[
V\text{ on the }r_1\text{ bracket}>\frac{223}{10000000},
\]
\[
V\text{ on the }r_2\text{ bracket}>\frac{103}{2500000},
\]
\[
V(1+M)>\frac{26}{625000}.
\]
These are conservative interval-style bounds checked by the reproducible one-variable verifier; they are not yet a formal proof-assistant derivation. The smallest margin is still only about \(223/10000000\), so the remaining written-proof step is to accept/formalize directed log bounds for the two brackets and the endpoints.

Status: reproducible high-precision finite certificate PASS with explicit brackets; the rigorous written bound remains \(1.7875\) until the directed log bounds are accepted/formalized in the written proof. If those directed log bounds are accepted, this subsection supports upgrading the written lower bound to \(1.7877\).

## 9) Four-atom verifier-PASS positivity block for the forum \(1.8\) route

This is the fixed positivity block used in the forum claim fragment
\[
\lambda_a=\delta_a+1.08\,\delta_{a+1.8}+0.2107\,\delta_{a+2.66996}+0.1326\,\delta_{a+2.79},
\qquad a\in[-1.8,-1.708).
\]
It does **not** by itself prove \(\inf\ge1.8\). The remaining route-level dependency is a rigorous proof of
\[
[-1.708,0]\subset E_\mu.
\]
Once that inclusion is available, this block supplies the fixed \(a\in[-1.8,-1.708)\) positivity piece for the \(1.8\) covering argument.

Set \(y=x-a\). For \(a\in[-1.8,-1.708)\) and \(x\in[-1,1]\), the exact image is
\[
y\in(0.708,2.8],
\]
and for a uniform check we may close it to \([0.708,2.8]\). Define
\[
V(y)=\log\frac1{y}
+ 1.08\log\frac1{|y-1.8|}
+ 0.2107\log\frac1{|y-2.66996|}
+ 0.1326\log\frac1{|y-2.79|}.
\]
Then \(U_{\lambda_a}(x)=V(x-a)\).

On the smooth pieces of \([0.708,2.8]\setminus\{1.8,2.66996,2.79\}\),
\[
V'(y)=-\left(\frac1y+\frac{1.08}{y-1.8}+\frac{0.2107}{y-2.66996}+\frac{0.1326}{y-2.79}\right).
\]
Clearing denominators gives the cubic critical polynomial
\[
N(y)=757281250\,y^3-4598920780\,y^2+8443012914\,y-4190168475.
\]
So \(V'(y)=0\iff N(y)=0\).

Numerical bracketing gives one real root in each smooth subinterval:
\[
r_1\in(0.7966012797426844,\,0.7966012797426845),\qquad
r_2\in(2.5200500980156706,\,2.5200500980156707),\qquad
r_3\in(2.7562849058218866,\,2.7562849058218867).
\]
No further critical point lies in \((2.79,2.8]\).

The corresponding numerical lower bounds are:
\[
V(0.708)\approx0.0110200211,\qquad
V(r_1)\gtrsim3.5234655\times10^{-7},
\]
\[
V(r_2)\approx0.00392244715,\qquad
V(r_3)\gtrsim1.8919957\times10^{-5},\qquad
V(2.8)\approx0.0108358573.
\]
On this floating-point check, the smallest margin is at \(r_1\). This block has now passed the reproducible one-variable verifier and should therefore be read as a verifier-PASS finite certificate, not merely raw numerical evidence; the remaining route-level gap is the separate 2D conservative forcing family.

Thus the verifier-PASS block gives \(V(y)>0\) on \((0.708,2.8]\), so \(U_{\lambda_a}(x)>0\) for every \(a\in[-1.8,-1.708)\) and \(x\in[-1,1]\) at the finite-certificate level.

This is the forum four-atom positivity block only. The global \(L_-\ge1.8\) route still needs the separate 2D conservative forcing family, i.e. the rigorous interval inclusion \([-1.708,0]\subset E_\mu\).

## 10) Task B: the \([-1.708,0]\) forcing bottleneck

Forum family under discussion:
\[
\nu_{a,b}=\delta_a+(1.395-b)\delta_b+C(a,b)\,\delta_{1.071-b},
\qquad
a\in[-1.708,-\sqrt2],\quad b\in[0,1.836+a].
\]
Write
\[
w_2:=1.395-b,\qquad c:=1.071-b.
\]
The normalization \(U_{\nu_{a,b}}(-1)=10^{-4}\) is
\[
-\log(-1-a)-w_2\log(1+b)-C(a,b)\log(2.071-b)=10^{-4},
\]
so the coefficient is explicitly
\[
C(a,b)=\frac{-10^{-4}-\log(-1-a)-(1.395-b)\log(1+b)}{\log(2.071-b)}.
\]
On the whole domain \(D=\{(a,b):a\in[-1.708,-\sqrt2],\, b\in[0,1.836+a]\}\),
\[
-1-a\in[0.41421356,0.708],\qquad
w_2\in[0.973,1.395],\qquad
c\in[0.649,1.071],
\]
and \(\log(2.071-b)>0\), so the family is well-defined. A coarse grid scan over \(D\) found
\[
C(a,b)\in[0.28997,1.21049],
\]
with no sign failure for the coefficient itself.

For fixed \((a,b)\), the potential on \(x\in[0,1]\setminus\{b,c\}\) is
\[
U_{\nu_{a,b}}(x)= -\log|x-a| - w_2\log|x-b| - C(a,b)\log|x-c|.
\]
Its derivative is rational:
\[
U'_{\nu_{a,b}}(x)
=-\left(\frac1{x-a}+\frac{w_2}{x-b}+\frac{C(a,b)}{x-c}\right)
=-\frac{Q_{a,b}(x)}{(x-a)(x-b)(x-c)},
\]
where \(Q_{a,b}\) is the quadratic
\[
Q_{a,b}(x)
=(1+w_2+C)x^2-\bigl[(b+c)+w_2(a+c)+C(a+b)\bigr]x+\bigl[bc+w_2ac+C\,ab\bigr].
\]
Therefore positivity on \(\{-1\}\cup[0,1]\) reduces, for each fixed \((a,b)\), to checking:
\[
U_{\nu_{a,b}}(-1)=10^{-4},
\]
and the values of \(U_{\nu_{a,b}}\) at the endpoints and at the at-most-two real roots of \(Q_{a,b}\) in each subinterval of \([0,1]\setminus\{b,c\}\). This is a finite semi-algebraic/logarithmic check in principle, but the forum argument as stated does not supply the required interval-arithmetic enclosure over the full two-parameter domain \(D\). So the present status is **numerical only**, not certified.

Dense sampling over \(D\) did not find a counterexample. On a \(401\times401\) scan, the smallest observed value on \(\{-1\}\cup[0,1]\) was the forced
\[
U_{\nu_{a,b}}(-1)=10^{-4},
\]
and the smallest observed value on \([0,1]\) was about
\[
1.2606765\times10^{-3},
\]
occurring at \(x=1\) near
\[
a\approx-1.6933106781,\qquad b\approx0.1426893219.
\]
So the family looks valid numerically throughout \(D\), but the missing piece is exactly a rigorous interval certificate for Task B.

Consequence for the \(1.8\) route: if this Task B block were interval-certified and the §9 four-atom block were also certified, then the forum argument would close to \(\inf\ge1.8\). At the moment, the route is still blocked by Task B itself; §9 is now verifier-PASS and no longer the bottleneck.

## 11) Review of the stronger external \(1.8\) proposal

The external proposal improves the forum route in three ways:

1. Replace the \([-1.708,0]\) forcing target by the more conservative \((-1.7,0)\subset E_\mu\).
2. Replace the old four-atom block by a higher-margin four-atom block.
3. Correct the two-interval Cauchy-transform ansatz by adding the endpoint atom at \(1\).

### 11.1 Conditional selector lemma for the conservative \((-1.7,0)\) forcing family

Let
\[
D:=\{(a,b): a\in[-1.7,-\sqrt2],\ b\in[0,1.82+a]\}.
\]
Define
\[
w=1.395-b,\qquad c=1.071-b,
\]
and
\[
\nu_{a,b}=\delta_a+w\,\delta_b+C(a,b)\,\delta_c,
\]
where \(C(a,b)>0\) is fixed by the normalization
\[
U_{\nu_{a,b}}(-1)=10^{-4}.
\]
With the convention \(U=-\sum \text{weights}\cdot \log(\text{distance})\), this gives
\[
C(a,b)=\frac{-10^{-4}-\log(-1-a)-(1.395-b)\log(1+b)}{\log(2.071-b)}.
\]
Numerically, the controller already checked that
\[
C(a,b)\in[0.3173,1.2105]
\]
on \(D\), and a dense grid gives
\[
\min_{x\in[0,1]}U_{\nu_{a,b}}(x)\approx 0.028557
\]
near \(a=-1.7,\ b=0,\ x\approx0.8340656689\). The minimum on \(\{-1\}\cup[0,1]\) is the forced \(10^{-4}\) at \(x=-1\).

Now assume the conditional positivity certificate:
\[
U_{\nu_{a,b}}(x)>0\qquad \text{for all }x\in\{-1\}\cup[0,1]\text{ and all }(a,b)\in D.
\]

#### Selector step
Fix \(a_0\in[-1.7,-\sqrt2]\) and assume \((a_0,0)\subset E_\mu\) with \(U_\mu(a_0)=0\). Set
\[
L:=1.82+a_0.
\]
For each \(b\in[0,L]\), consider \(\nu_{a_0,b}\). By the duality relation already recorded in §3, the positivity certificate implies
\[
\int U_{\nu_{a_0,b}}\,d\mu>0.
\]
Suppose for contradiction that both \(b\notin E_\mu\) and \(c=1.071-b\notin E_\mu\). Then, since \(U_\mu\le 0\) on \(E_\mu^c\),
\[
U_\mu(b)\le 0,\qquad U_\mu(c)\le 0.
\]
The normalization \(U_\mu(a_0)=0\) and the fact that the weights \(w=1.395-b\) and \(C(a_0,b)\) are positive force the duality contribution from the three atoms to be nonpositive unless at least one of \(b,c\) lies in \(E_\mu\), contradicting \(\int U_{\nu_{a_0,b}}\,d\mu>0\). Hence for every \(b\in[0,L]\),
\[
b\in E_\mu\quad\text{or}\quad c=1.071-b\in E_\mu.
\]

#### Disjoint image intervals
The map \(b\mapsto c=1.071-b\) sends \([0,L]\) to \([1.071-L,1.071]\). Since
\[
L=1.82+a_0\le 1.82-\sqrt2<0.406<0.5355=\frac{1.071}{2},
\]
the intervals
\[
[0,L]\quad\text{and}\quad [1.071-L,1.071]
\]
are disjoint. Therefore the selector above contributes at least \(L\) units of positive-side measure inside \([0,1]\). Combining this with the already assumed interval \((a_0,0)\subset E_\mu\), we obtain
\[
|E_\mu|\ge -a_0+L=-a_0+(1.82+a_0)=1.82,
\]
which contradicts \(|E_\mu|<1.8\).

Thus, conditional on the positivity certificate for \(\nu_{a,b}\) over \(D\), the conservative route forces
\[
(-1.7,0)\subset E_\mu.
\]

Status: this is still only conditional on a directed interval-arithmetic verification of the family positivity over \(D\); no overclaim is intended. The remaining work is to certify \(U_{\nu_{a,b}}>0\) on \(\{-1\}\cup[0,1]\) box by box, with \(C(a,b)\), \(w\), and \(c\) enclosed rigorously and the quadratic critical roots isolated on each parameter box.

### 11.2 Higher-margin four-atom block

Assume \(({-1.7},0)\subset E_\mu\). For \(a\in[-1.8,-1.7]\), consider
\[
\lambda_a=\delta_a
+\frac{2457}{2000}\delta_{a+18003/10000}
+\frac{767}{5000}\delta_{a+26628/10000}
+\frac{1749}{10000}\delta_{a+557/200}.
\]
With \(y=x-a\), the potential increment is
\[
V(y)=\log\frac1{|y|}
+\frac{2457}{2000}\log\frac1{|y-18003/10000|}
+\frac{767}{5000}\log\frac1{|y-26628/10000|}
+\frac{1749}{10000}\log\frac1{|y-557/200|},
\qquad y\in[7/10,14/5].
\]
The exact denominator-cleared derivative numerator is
\[
P(y)=319600000000 y^3-1928087938750 y^2+3492695976477 y-1668855146175.
\]
Its root brackets and sign directions are:
\[
r_1\in\Big[\frac{74916852}{100000000},\frac{74916853}{100000000}\Big],\qquad
P(\text{left})<0,\ P(\text{right})>0;
\]
\[
r_2\in\Big[\frac{254570327}{100000000},\frac{254570328}{100000000}\Big],\qquad
P(\text{left})>0,\ P(\text{right})<0;
\]
\[
r_3\in\Big[\frac{273794401}{100000000},\frac{273794402}{100000000}\Big],\qquad
P(\text{left})<0,\ P(\text{right})>0.
\]
Equivalently,
\[
r_1\in(7/10,18003/10000),\quad
r_2\in(18003/10000,26628/10000),\quad
r_3\in(26628/10000,557/200),
\]
and there is no critical root in \((557/200,14/5]\). Since
\[
V(y)\to+\infty
\]
at each pole \(y=18003/10000,\ 26628/10000,\ 557/200\), the minimum on each smooth component occurs only at a finite endpoint or at one of these roots. The finite certificate therefore reduces to the five endpoint/interval checks
\[
V(7/10)>7/1000,\qquad
V\big|_{r_1\text{ bracket}}>9/2500,\qquad
V\big|_{r_2\text{ bracket}}>7/1250,
\]
\[
V\big|_{r_3\text{ bracket}}>7/2000,\qquad
V(14/5)>99/10000.
\]

This four-atom one-variable block is mechanically intervalizable and numerically high-margin, but a rigorous proof still requires directed log bounds. Conditional route consequence: if \(({-1.7},0)\subset E_\mu\) and for each \(a\in[-1.8,-1.7]\) one of
\[
a,\quad a+1.8003,\quad a+2.6628,\quad a+2.7850
\]
lies in \(E_\mu\), then the swept intervals outside \(({-1.7},0)\) are

\[
[-1.8,-1.7],\quad [0.0003,0.1003],\quad [0.8628,0.9628],\quad [0.985,1.085],
\]
which are pairwise disjoint and force at least \(0.1\) additional measure. Thus Task 3 plus this block yields
\[
|E_\mu|\ge1.7+0.1=1.8,
\]
but only conditionally, pending the directed log bounds and Task 3 certification.

### 11.3 Endpoint atom in the two-interval ansatz

For
\[
F(z)=
\frac{z+A}{(z-\ell)(z-r)(z-1)}
\sqrt{(z-\alpha)(z-\beta)},
\qquad \beta=1-\varepsilon,
\]
with the branch \(\sqrt{(z-\alpha)(z-\beta)}\sim z\), the pole at \(z=1\) has residue
\[
m_1=
\frac{(1+A)\sqrt{(1-\alpha)\varepsilon}}{(1-\ell)(1-r)}.
\]
In the small-\(\varepsilon\) regime \(\ell<-1<r<\alpha<\beta<1\) and \(A>1\), this residue is positive. Therefore the Cauchy-transform measure must contain \(m_1\delta_1\). The no-\(\delta_1\) version of this ansatz is incomplete unless the degenerate cancellation \(A=-1\) is imposed, which is incompatible with the intended positive-measure regime.

With \(1<A<-\ell\), the atom residues at \(\ell,r,1\) and the continuous density on \([\alpha,\beta]\) have the expected positive signs. In this corrected ansatz, the sign chart of \(F\) reduces positivity on \([-1,1]\) to the scalar checks \(U_\lambda(\alpha)=0\) and \(U_\lambda(-1)\ge0\), provided the parameter inequalities and branch choices above hold.

Status: the endpoint-atom correction is mathematically sound and should replace the earlier informal two-atom-plus-density ansatz.

### 11.4 Current verdict

The strengthened \(1.8\) proposal is plausible and numerically supported, but it is not yet a proof as written. The next proof-producing task is:

1. intervalize the conservative \((-1.7,0)\) forcing family;
2. intervalize the higher-margin four-atom block;
3. then combine the two covering steps to state \(L_-\ge1.8\) under the standard Tao/natso reduction.

### 11.3 Reproducible one-variable verifier

Added `1038/verify_one_variable_certificates.py`, a standard-library-only `Decimal` verifier that lower-bounds each positive log term on a closed bracket by the farther endpoint distance. This upgrades the two finite certificates from raw floating evidence to reproducible high-precision finite certificate PASS results, but it is still not a formal proof assistant; a fully formal writeup still needs acceptance/formalization of directed `Decimal` log bounds.

Observed `PASS` results at `Decimal` precision 100:

- fixed three-atom forum candidate `M=1.7877`: `V(sqrt2-1) ≈ 0.182726776421551552`, `V(r1 bracket) ≈ 0.000022339452066803`, `V(r2 bracket) ≈ 0.000041221596433925`, `V(1+M) ≈ 0.000041658548912946`;
- section 11.2 four-atom block: `V(7/10) ≈ 0.007291646820090421`, `V(r1 bracket) ≈ 0.003635292525274415`, `V(r2 bracket) ≈ 0.005684389915462059`, `V(r3 bracket) ≈ 0.003509632047703050`, `V(14/5) ≈ 0.009978413703700006`.

Overall verifier status: `PASS`.
## 12. Finite interval-box certificate for the 1.8 forcing family

This section upgrades the conservative two-parameter forcing family from grid
evidence to a finite interval-box certificate.

The family is

\[
a\in[-1.7,-\sqrt2],\qquad b\in[0,1.82+a],
\]

\[
w=1.395-b,\qquad c=1.071-b,
\]

and

\[
\nu_{a,b}=\delta_a+w\delta_b+C(a,b)\delta_c,
\]

where \(C(a,b)\) is fixed by

\[
U_{\nu_{a,b}}(-1)=10^{-4}.
\]

Equivalently,

\[
C(a,b)=
\frac{
-10^{-4}-\log(-1-a)-(1.395-b)\log(1+b)
}{
\log(2.071-b)
}.
\]

The certificate uses the rectangular parametrisation

\[
b=s(1.82+a),\qquad s\in[0,1],
\]

so that the original triangular domain is covered by

\[
(a,s,x)\in[-1.7,-\sqrt2]\times[0,1]\times[0,1].
\]

On each interval box \(B\), it proves a direct lower bound for

\[
U_{\nu_{a,b}}(x)
=-\log|x-a|-w\log|x-b|-C(a,b)\log|x-c|.
\]

For each atom \(t\), the elementary estimate is

\[
\log\frac1{|x-t|}
\ge
-\log\left(\max_B |x-t|\right).
\]

The \(b\)-atom is always nonnegative on \([0,1]\), because \(b,x\in[0,1]\)
imply \(|x-b|\le1\).  The \(c\)-atom may be negative when \(c>1\), so the
certificate uses the upper interval bound for \(C\) whenever
\(-\log(\max_B|x-c|)<0\).  Singularities at \(x=b\) or \(x=c\) are harmless:
the proof ignores the \(+\infty\) gain and only uses the farthest-distance
lower bound.

The verifier is:

```text
1038/verify_conservative_forcing_interval.py
```

It has two modes:

```text
python3 1038/verify_conservative_forcing_interval.py --export-json 1038/conservative_forcing_interval_certificate.json
python3 1038/verify_conservative_forcing_interval.py --check-json 1038/conservative_forcing_interval_certificate.json
```

The first mode searches the recursive subdivision and exports the terminal
boxes.  The second mode treats the exported file as a fixed finite certificate:
it recomputes every box lower bound, checks metadata consistency, checks every
leaf is contained in the full domain, checks there is no positive-volume overlap
between leaves, and checks that the total leaf volume equals the full
\((a,s,x)\)-domain volume.

This is a strong engineering certificate for the trusted exported leaf list,
not yet a Lean-level proof of recursive partition soundness.  A proof-assistant
version should encode the split tree or otherwise prove exact coverage inside
Lean.

Current fixed certificate:

```text
1038/conservative_forcing_interval_certificate.json
```

The Lean numeric checker also mirrors this interval-box algorithm:

```text
1038/LeanCertificates.lean
```

Current Lean run:

```text
C. Conservative forcing family interval-box numeric check
certified boxes=926, split boxes=925, max depth=19
worst lower bound=0.000032
conservative interval check: PASS

OVERALL LEAN NUMERIC CHECK: PASS
```

It certifies all boxes with safety margin \(10^{-6}\).  The current run gives:

```text
certified boxes: 926
split boxes: 925
max depth: 19
worst certified lower bound: 0.00003201866299599745925916150423353071748526016312194491632257771951416804933771
status: PASS
```

The fixed JSON certificate check gives the same output:

```text
checked certificate: 1038/conservative_forcing_interval_certificate.json
status: PASS
```

Therefore

\[
U_{\nu_{a,b}}(x)>0
\qquad
\forall x\in[0,1],
\quad
\forall a\in[-1.7,-\sqrt2],
\quad
\forall b\in[0,1.82+a].
\]

Together with the normalization \(U_{\nu_{a,b}}(-1)=10^{-4}\), this proves

\[
U_{\nu_{a,b}}>0
\qquad\text{on } \{-1\}\cup[0,1].
\]

Consequently the selector argument in Section 11.1 is now certificate-backed:
if \(a_0\in[-1.7,-\sqrt2]\) is the left endpoint of the maximal interval
\((a_0,0)\subset E_\mu\) containing \((-\sqrt2,0)\), then for each
\(b\in[0,1.82+a_0]\), duality forces

\[
b\in E_\mu
\qquad\text{or}\qquad
1.071-b\in E_\mu.
\]

Since the intervals

\[
[0,L],\qquad [1.071-L,1.071],
\qquad L=1.82+a_0<0.406,
\]

are disjoint, the positive side contributes at least \(L\).  Hence

\[
|E_\mu|\ge -a_0+L=1.82,
\]

contradicting \(|E_\mu|<1.8\).  Thus under the standard reduction,

\[
|E_\mu|<1.8
\quad\Longrightarrow\quad
(-1.7,0)\subset E_\mu.
\]

Combining this with the high-margin four-atom block in Section 11.2 gives the
conditional theorem

\[
\boxed{|E_\mu|\ge1.8}
\]

for every normalized minimizer satisfying

\[
\mu(\{-1\})\ge\frac12,\qquad
\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1].
\]

Thus, accepting the Tao/natso standard reduction as an external lemma, the
current lower bound is now

\[
\boxed{L_-\ge1.8.}
\]

Remaining formalization gap: the interval-box script is a finite numerical
certificate with explicit safety padding.  To make it proof-assistant-grade,
one should port the logarithm lower-bound step to Lean/Mathlib or replace each
logged distance bound by a rational Taylor/atanh certificate.

The proof-chain formalization is in:

```text
1038/FormalSkeleton.lean
```

It proves only the conditional pipeline

\[
\text{Short18 counterexample}
\Rightarrow
\text{normalized baseline}
\Rightarrow
\text{TwoDForced or FourAtomForced}
\Rightarrow
\bot.
\]

This file intentionally treats the standard reduction, the two-dimensional
forcing certificate, and the four-atom certificate as external assumptions.
It compiles under local Lean 4.30 + Std.

## 13. Closing the proof-chain gaps around the 1.8 route

The interval-box certificate proves the analytic positivity input.  The
remaining handwritten proof must avoid two common shortcuts:

1. Do not invoke a finite-energy bilinear identity for \(\mu\), because the
   reduced minimizer may have an atom at \(-1\).
2. Do not hide the good singularities at \(b\) and \(c\), because these atoms
   often lie inside \([0,1]\).

The correct proof chain is as follows.

### 13.1 Truncated duality lemma

For \(R>0\), define the truncated kernel

\[
K_R(x,t)=\min\left(\log\frac1{|x-t|},R\right).
\]

All supports appearing here lie in a fixed bounded interval, for instance
\([-1.8,1.1]\).  Hence the logarithmic kernel has a uniform lower bound

\[
\log\frac1{|x-t|}\ge -\log(2.9)
\]

on the relevant cross-products, except at the diagonal where it is \(+\infty\).
Thus \(K_R+\log(2.9)\) is nonnegative and increases pointwise to
\(\log(1/|x-t|)+\log(2.9)\).  The additive constant cancels from both sides of
the bilinear identity, but it makes the monotone-convergence step literal.

Also, \(K_R\) is bounded and symmetric, so for any probability measure \(\mu\)
on \(\{-1\}\cup[0,1]\) and any finite atomic positive measure

\[
\nu=\sum_{j=1}^m c_j\delta_{y_j},
\qquad c_j>0,
\]

one has the exact identity

\[
\int\!\int K_R(x,t)\,d\mu(t)\,d\nu(x)
=
\int\!\int K_R(x,t)\,d\nu(x)\,d\mu(t).
\]

Let

\[
U_{\mu,R}(x)=\int K_R(x,t)\,d\mu(t),
\qquad
U_{\nu,R}(t)=\int K_R(x,t)\,d\nu(x).
\]

If no atom \(y_j\) of \(\nu\) is an atom of \(\mu\), then

\[
U_{\mu,R}(y_j)\to U_\mu(y_j)
\]

for each \(j\).  Since \(\nu\) is finite atomic,

\[
\int U_{\mu,R}\,d\nu\to \int U_\mu\,d\nu.
\]

On the other side, \(U_{\nu,R}(t)\uparrow U_\nu(t)\) pointwise in the extended
sense.  In the applications below the interval certificate gives

\[
U_\nu(t)\ge m>0
\qquad (t\in\{-1\}\cup[0,1])
\]

away from the harmless \(+\infty\) singularities, and in particular the negative
part is absent.  Therefore monotone convergence gives

\[
\int U_{\nu,R}\,d\mu\to\int U_\nu\,d\mu.
\]

Thus

\[
\boxed{\int U_\mu\,d\nu=\int U_\nu\,d\mu}
\]

whenever the atoms of \(\nu\) do not coincide with atoms of \(\mu\).

If some atom \(y_j\) of \(\nu\) is also an atom of \(\mu\), then

\[
U_\mu(y_j)=+\infty,
\]

so \(y_j\in E_\mu\) automatically.  In the forcing argument this is already the
desired conclusion.  Hence the truncated lemma covers all cases.

### 13.2 Singularity and critical-point lemma

For fixed admissible \(a,b\), the potential

\[
U_{\nu_{a,b}}(x)
=-\log|x-a|-w\log|x-b|-C\log|x-c|
\]

is smooth on every component of

\[
[0,1]\setminus\{b,c\}.
\]

Because \(w>0\) and \(C>0\), the one-sided limits at \(b\) and \(c\) are
\(+\infty\).  Therefore a finite minimum on \([0,1]\) can only occur at
\[
x=0,\qquad x=1,
\]

or at an interior point satisfying

\[
U'_{\nu_{a,b}}(x)=0.
\]

Since

\[
U'_{\nu_{a,b}}(x)
=-\frac1{x-a}-\frac{w}{x-b}-\frac{C}{x-c},
\]

multiplying by \((x-a)(x-b)(x-c)\) reduces the critical-point equation to a
quadratic polynomial in \(x\).  This justifies the endpoint/critical-point
logic used by the exploratory grid verifier.

The interval-box verifier in Section 12 uses a stronger route: it lower-bounds
\(U_{\nu_{a,b}}(x)\) directly on boxes in \((a,s,x)\), so it does not need root
isolation for the two-parameter family.

### 13.3 Selector lemma

Assume the standard reduction

\[
\mu(\{-1\})\ge\frac12,\qquad
\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1].
\]

Let \(a\in[-1.7,-\sqrt2]\), \(b\in[0,1.82+a]\), and let \(\nu_{a,b}\) be the
forcing measure above.  The certificate gives

\[
U_{\nu_{a,b}}>0
\qquad\text{on }\{-1\}\cup[0,1].
\]

Suppose neither \(b\) nor \(c=1.071-b\) belongs to \(E_\mu\), and suppose also
that \(a\notin E_\mu\).  If any of \(a,b,c\) is a \(\mu\)-atom, it is already in
\(E_\mu\), so we may assume there is no shared atom and apply the truncated
duality lemma:

\[
\int U_\mu\,d\nu_{a,b}
=
\int U_{\nu_{a,b}}\,d\mu.
\]

The right side is strictly positive because \(U_{\nu_{a,b}}>0\) on
\(\operatorname{supp}\mu\).  The left side is nonpositive because all atoms
of \(\nu_{a,b}\) were assumed outside \(E_\mu=\{U_\mu>0\}\).  Contradiction.

Therefore, whenever \(a\notin E_\mu\),

\[
\boxed{b\in E_\mu\quad\text{or}\quad 1.071-b\in E_\mu.}
\]

### 13.4 Boundary and covering lemma

We already know

\[
(-\sqrt2,0)\subset E_\mu.
\]

Also \(E_\mu=\{U_\mu>0\}\) is open on the line: away from atoms this follows
from continuity of the logarithmic potential, and at atoms \(U_\mu=+\infty\).
If \((-1.7,0)\not\subset E_\mu\), choose the left boundary
\(a_0\in[-1.7,-\sqrt2]\) of the maximal interval \((a_0,0)\subset E_\mu\)
containing \((-\sqrt2,0)\), so that

\[
(a_0,0)\subset E_\mu,\qquad a_0\notin E_\mu.
\]

For every

\[
b\in[0,L],
\qquad L=1.82+a_0,
\]

the selector lemma gives

\[
b\in E_\mu
\qquad\text{or}\qquad
1.071-b\in E_\mu.
\]

The two swept intervals are

\[
[0,L],
\qquad
[1.071-L,1.071].
\]

They are disjoint because

\[
L\le 1.82-\sqrt2<0.406<\frac{1.071}{2}.
\]

Therefore the positive side contributes at least \(L\) length.  The negative
component contributes \(-a_0\), and hence

\[
|E_\mu|
\ge -a_0+L
=-a_0+(1.82+a_0)
=1.82.
\]

Thus any counterexample with \(|E_\mu|<1.8\) must satisfy

\[
(-1.7,0)\subset E_\mu.
\]

The high-margin four-atom block in Section 11.2 then forces an additional
\(0.1\) length outside \((-1.7,0)\).  Hence, under the standard reduction,

\[
\boxed{|E_\mu|\ge1.8.}
\]

## 14. Stronger finite-atom upgrades: \(1.8035\), \(1.804\), \(1.805\), \(1.806\), and \(1.8063\)

After installing a local optimization environment in `.venv`, I searched for a
stronger finite-atom block while keeping the same forcing threshold
\((-1.7,0)\).

The key observation is that Section 12 actually proves a stronger alternative:
if \((-1.7,0)\not\subset E_\mu\), then

\[
|E_\mu|\ge 1.82.
\]

Therefore this forcing branch is still enough for any target below \(1.82\).
To improve \(1.8\), it suffices to replace the old final four-atom block on
\([-1.8,-1.7]\) by a block on \([-1.803,-1.7]\).

The new block is:

\[
\lambda_a
=
\delta_a
+\frac{6107}{5000}\delta_{a+180321/100000}
+\frac{15563}{100000}\delta_{a+266713/100000}
+\frac{4293}{25000}\delta_{a+278795/100000},
\]

for

\[
a\in[-1.803,-1.7].
\]

Writing \(y=x-a\), the verification reduces to

\[
V(y)>0
\qquad
(0.7\le y\le2.803),
\]

where

\[
\begin{aligned}
V(y)=&
\log\frac1{|y|}
+\frac{6107}{5000}\log\frac1{|y-180321/100000|}
\\
&+\frac{15563}{100000}\log\frac1{|y-266713/100000|}
+\frac{4293}{25000}\log\frac1{|y-278795/100000|}.
\end{aligned}
\]

The critical equation is the cubic

\[
\begin{aligned}
P(y)=&
2548750000000000 y^3
-15403293727600000 y^2
\\
&+27962858408259841 y
-13408354148818035.
\end{aligned}
\]

The verifier brackets the three roots by

\[
\begin{aligned}
r_1&\in[0.75277143,0.75277144],\\
r_2&\in[2.54863247,2.54863248],\\
r_3&\in[2.74206592,2.74206593].
\end{aligned}
\]

The exact integer sign checks are:

\[
P(0.75277143)<0<P(0.75277144),
\]

\[
P(2.54863247)>0>P(2.54863248),
\]

\[
P(2.74206592)<0<P(2.74206593).
\]

The conservative Decimal lower bounds are:

```text
V(7/10)        > 0.0049
V(r1 bracket) > 0.0008
V(r2 bracket) > 0.00078
V(r3 bracket) > 0.00078
V(2803/1000)  > 0.0008
```

Both verifiers pass:

```text
python3 1038/verify_one_variable_certificates.py
lean --run 1038/LeanCertificates.lean
```

The swept intervals for \(a\in[-1.803,-1.7]\) are

\[
[-1.803,-1.7],
\]

\[
[0.00021,0.10321],
\]

\[
[0.86413,0.96713],
\]

\[
[0.98495,1.08795].
\]

They are pairwise disjoint and avoid \((-1.7,0)\).  Hence, if
\((-1.7,0)\subset E_\mu\), the stronger block contributes at least

\[
1.803-1.7=0.103
\]

additional length outside \((-1.7,0)\).  Therefore

\[
|E_\mu|\ge1.7+0.103=1.803.
\]

Combining the two branches:

1. If \((-1.7,0)\not\subset E_\mu\), Section 12 gives
   \[
   |E_\mu|\ge1.82>1.803.
   \]
2. If \((-1.7,0)\subset E_\mu\), the stronger four-atom block gives
   \[
   |E_\mu|\ge1.803.
   \]

Thus, under the same standard reduction,

\[
\boxed{|E_\mu|\ge1.803.}
\]

This four-atom line can be pushed a little further.  With

\[
\lambda^{(4)}_a
=
\delta_a
+\frac{1214075}{1000000}\delta_{a+18037/10000}
+\frac{78647}{500000}\delta_{a+1333789/500000}
+\frac{85271}{500000}\delta_{a+1394283/500000},
\]

for \(a\in[-1.8035,-1.7]\), the same one-variable certificate gives

\[
\boxed{|E_\mu|\ge1.8035}
\]

on the long-interval branch.  The critical roots are bracketed by

\[
[0.75523882,0.75523883],\quad
[2.54795697,2.54795698],\quad
[2.74299881,2.74299882],
\]

and the conservative lower bounds are all positive, the smallest being above
\(2.5\cdot10^{-4}\).  The Decimal verifier and Lean numeric checker both pass.

Search then shows \(1.8038\) is already negative for this four-atom line, while
a refined four-atom certificate at \(1.8036\) still passes.  Thus the current
four-atom certificate-backed endpoint is \(1.8036\).

The bound was then improved further by allowing one additional shifted atom.

### 14.1 Five-atom block for \(1.804\)

The stronger block is:

\[
\begin{aligned}
\Lambda_a
=&\delta_a
+\frac{1180333}{1000000}\delta_{a+9021/5000}
+\frac{3543}{125000}\delta_{a+2571118/1000000}
\\
&+\frac{117723}{1000000}\delta_{a+2684011/1000000}
+\frac{179033}{1000000}\delta_{a+2788213/1000000},
\end{aligned}
\]

for

\[
a\in[-1.804,-1.7].
\]

Writing \(y=x-a\), the positivity check is

\[
W(y)>0\qquad(0.7\le y\le2.804).
\]

The derivative numerator is the quartic

\[
\begin{aligned}
Q(y)=&
1252716500000000000000000y^4
-10827386081756000000000000y^3
\\
&+33456188332790152991500000y^2
-42486572502897050553224221y
\\
&+17357490281503157606495400.
\end{aligned}
\]

Its four real critical roots in the interval are bracketed by

\[
\begin{aligned}
s_1&\in[0.76702920,0.76702921],\\
s_2&\in[2.52493236,2.52493237],\\
s_3&\in[2.60961793,2.60961794],\\
s_4&\in[2.74154611,2.74154612].
\end{aligned}
\]

The conservative Decimal certificate gives:

```text
V(7/10)        > 0.0094
V(s1 bracket) > 0.0028
V(s2 bracket) > 0.0028
V(s3 bracket) > 0.0028
V(s4 bracket) > 0.0028
V(701/250)    > 0.0028
```

The exact integer sign checks and the Float mirror both pass in Lean:

```text
lean --run 1038/LeanCertificates.lean
```

The swept intervals for \(a\in[-1.804,-1.7]\) are

\[
[-1.804,-1.7],
\]

\[
[0.0002,0.1042],
\]

\[
[0.767118,0.871118],
\]

\[
[0.880011,0.984011],
\]

\[
[0.984213,1.088213].
\]

They are pairwise disjoint and avoid \((-1.7,0)\).  Hence, if
\((-1.7,0)\subset E_\mu\), this block contributes at least

\[
1.804-1.7=0.104
\]

additional length outside \((-1.7,0)\), giving

\[
|E_\mu|\ge1.7+0.104=1.804.
\]

The other branch is unchanged: if \((-1.7,0)\not\subset E_\mu\), the
two-parameter forcing certificate gives

\[
|E_\mu|\ge1.82>1.804.
\]

Therefore, under the same standard reduction,

\[
\boxed{|E_\mu|\ge1.804.}
\]

### 14.2 Five-atom block for \(1.805\)

The same method gives one more improvement.  The new block is

\[
\begin{aligned}
\Omega_a
=&\delta_a
+\frac{117735}{100000}\delta_{a+9026/5000}
+\frac{13473}{500000}\delta_{a+257054/100000}
\\
&+\frac{23869}{200000}\delta_{a+134199/50000}
+\frac{89427}{500000}\delta_{a+278919/100000},
\end{aligned}
\]

for

\[
a\in[-1.805,-1.7].
\]

The one-variable interval is now

\[
0.7\le y\le 2.805.
\]

The derivative numerator is the quartic

\[
\begin{aligned}
R(y)=&
12512475000000000000y^4
-108165263291250000000y^3
\\
&+334311904176703995000y^2
-424736454351386263563y
\\
&+173690901891803689848.
\end{aligned}
\]

The four critical roots are bracketed by

\[
\begin{aligned}
t_1&\in[0.76842878,0.76842879],\\
t_2&\in[2.52553845,2.52553846],\\
t_3&\in[2.60824271,2.60824272],\\
t_4&\in[2.74238380,2.74238381].
\end{aligned}
\]

The conservative Decimal lower bounds are:

```text
V(7/10)        > 0.0084
V(t1 bracket) > 0.0016
V(t2 bracket) > 0.0016
V(t3 bracket) > 0.0016
V(t4 bracket) > 0.00159
V(561/200)    > 0.0016
```

The exact integer signs and the Float mirror pass in Lean:

```text
lean --run 1038/LeanCertificates.lean
```

The swept intervals for \(a\in[-1.805,-1.7]\) are

\[
[-1.805,-1.7],
\]

\[
[0.0002,0.1052],
\]

\[
[0.76554,0.87054],
\]

\[
[0.87898,0.98398],
\]

\[
[0.98419,1.08919].
\]

They are pairwise disjoint and avoid \((-1.7,0)\).  Thus the long-interval
branch gives

\[
|E_\mu|\ge1.7+(1.805-1.7)=1.805.
\]

The complementary branch remains

\[
|E_\mu|\ge1.82>1.805.
\]

Therefore, under the same standard reduction,

\[
\boxed{|E_\mu|\ge1.805.}
\]

### 14.3 Five-atom block for \(1.806\)

The current strongest block is

\[
\begin{aligned}
\Xi_a
=&\delta_a
+\frac{29348}{25000}\delta_{a+9031/5000}
+\frac{2657}{100000}\delta_{a+25707/10000}
\\
&+\frac{5887}{50000}\delta_{a+2683635/1000000}
+\frac{180873}{1000000}\delta_{a+2789842/1000000},
\end{aligned}
\]

for

\[
a\in[-1.806,-1.7].
\]

The one-variable interval is

\[
0.7\le y\le 2.806.
\]

The derivative numerator is

\[
\begin{aligned}
S(y)=&
62477575000000000000y^4
-540197265796625000000y^3
\\
&+1670105544400391395000y^2
-2122904930985962560404y
\\
&+869081088441491719695.
\end{aligned}
\]

The four critical roots are bracketed by

\[
\begin{aligned}
u_1&\in[0.76998681,0.76998682],\\
u_2&\in[2.52599663,2.52599664],\\
u_3&\in[2.60818086,2.60818087],\\
u_4&\in[2.74209420,2.74209421].
\end{aligned}
\]

The conservative Decimal lower bounds are:

```text
V(7/10)        > 0.0075
V(u1 bracket) > 0.00041
V(u2 bracket) > 0.00041
V(u3 bracket) > 0.00041
V(u4 bracket) > 0.00041
V(1403/500)   > 0.00042
```

This is more delicate than the \(1.805\) block, but it still passes both
the Decimal verifier and the Lean numeric checker.

The swept intervals for \(a\in[-1.806,-1.7]\) are

\[
[-1.806,-1.7],
\]

\[
[0.0002,0.1062],
\]

\[
[0.7647,0.8707],
\]

\[
[0.877635,0.983635],
\]

\[
[0.983842,1.089842].
\]

They are pairwise disjoint and avoid \((-1.7,0)\).  Hence the long-interval
branch gives

\[
|E_\mu|\ge1.7+(1.806-1.7)=1.806.
\]

The narrowest separation is between the last two positive intervals:

\[
\frac{2789842}{1000000}-\frac{2683635}{1000000}-\frac{106}{1000}
=
\frac{207}{1000000}>0.
\]

The complementary branch remains

\[
|E_\mu|\ge1.82>1.806.
\]

Therefore, under the same standard reduction,

\[
\boxed{|E_\mu|\ge1.806.}
\]

### 14.4 Five-atom block for \(1.8063\)

The previous \(1.806\) block can be pushed a little further.  The strongest
certificate-backed block currently in this repository is

\[
\begin{aligned}
\Psi_a
=&\delta_a
+\frac{1174168821}{1000000000}\delta_{a+180650001/100000000}
+\frac{25921118}{1000000000}\delta_{a+257053197/100000000}
\\
&+\frac{118647936}{1000000000}\delta_{a+268367709/100000000}
+\frac{180553554}{1000000000}\delta_{a+279017717/100000000},
\end{aligned}
\]

for

\[
a\in[-1.8063,-1.7].
\]

Writing \(y=x-a\), the one-variable interval is

\[
0.7\le y\le 2.8063.
\]

The derivative numerator is the quartic

\[
\begin{aligned}
T(y)=&
833097143000000000000000000000000y^4
-7203426448779519290000000000000000y^3
\\
&+22271344049495468164668367700000000y^2
-28310680823455635363669075998162907y
\\
&+11590489097511299183527530554428470.
\end{aligned}
\]

The four critical roots are bracketed by

\[
\begin{aligned}
v_1&\in[0.77003805,0.77003806],\\
v_2&\in[2.52642600,2.52642601],\\
v_3&\in[2.60759965,2.60759966],\\
v_4&\in[2.74249871,2.74249872].
\end{aligned}
\]

The conservative Decimal lower bounds are:

```text
V(7/10)          > 0.0072
V(v1 bracket)   > 0.000059
V(v2 bracket)   > 0.000058
V(v3 bracket)   > 0.000058
V(v4 bracket)   > 0.000057
V(28063/10000)  > 0.000059
```

This is a thin certificate, but it is still strictly positive after rational
rounding and endpoint-based log lower bounds.

The swept intervals for \(a\in[-1.8063,-1.7]\) are

\[
[-1.8063,-1.7],
\]

\[
[0.00020001,0.10650001],
\]

\[
[0.76423197,0.87053197],
\]

\[
[0.87737709,0.98367709],
\]

\[
[0.98387717,1.09017717].
\]

They are pairwise disjoint and avoid \((-1.7,0)\).  The tightest separation is
between the last two positive intervals:

\[
0.98387717-0.98367709=0.00020008>0.
\]

Therefore the long-interval branch gives

\[
|E_\mu|\ge1.7+(1.8063-1.7)=1.8063.
\]

The complementary branch remains

\[
|E_\mu|\ge1.82>1.8063.
\]

Therefore, under the same standard reduction,

\[
\boxed{|E_\mu|\ge1.8063.}
\]

This is now the strongest local certificate-backed conditional lower bound in
the repository.  It is stronger than the finite-atom \(1.8\) lower-bound
baseline in the comments, but it is not a full proof of the conjectural
infimum \(1.8344304757\ldots\).  It remains dependent on the standard
minimizer reduction and on the finite log certificates.

## 15. Active exact route: corrected two-interval finite-gap certificate

The strongest route toward the exact infimum is no longer to add more finite
atoms.  The finite-atom work in §14 is now a lower-bound bootstrap.  The exact
route should follow Tao's Cauchy-transform ansatz, with the missing endpoint
atom included.

For the two-interval obstruction

\[
E_\varepsilon=(x_L+\varepsilon,x_R)\cup(1-\varepsilon,1),
\]

write

\[
\ell=x_L+\varepsilon,\qquad r=x_R,\qquad \beta=1-\varepsilon.
\]

The corrected ansatz is

\[
F(z)=
\frac{z+A}{(z-\ell)(z-r)(z-1)}
\sqrt{(z-\alpha)(z-\beta)},
\qquad
\sqrt{(z-\alpha)(z-\beta)}\sim z
\quad(z\to\infty).
\]

The Cauchy convention is fixed as

\[
F(z)=\int\frac{d\lambda(t)}{z-t},
\qquad
U_\lambda'(x)=-F(x)
\]

off the support of \(\lambda\).

With this convention, the measure extracted from \(F\) is

\[
\lambda
=m_\ell\delta_\ell+m_r\delta_r+m_1\delta_1
+g(x)\mathbf 1_{[\alpha,\beta]}(x)\,dx,
\]

where

\[
m_\ell=
\frac{(\ell+A)R(\ell)}{(\ell-r)(\ell-1)},\qquad
m_r=
\frac{(r+A)R(r)}{(r-\ell)(r-1)},\qquad
m_1=
\frac{(1+A)R(1)}{(1-\ell)(1-r)},
\]

and

\[
g(x)=
-\frac1\pi
\frac{x+A}{(x-\ell)(x-r)(x-1)}
\sqrt{(x-\alpha)(\beta-x)}
\qquad(\alpha<x<\beta).
\]

The endpoint atom is not optional.  Since \(\beta<1\), \(F\) has a simple pole
at \(1\), with

\[
m_1=
\frac{(1+A)\sqrt{(1-\alpha)\varepsilon}}{(1-\ell)(1-r)}.
\]

Thus the no-\(\delta_1\) version is retired as an active ansatz.

### 15.1 Correct sign chart in the actual two-interval geometry

The relevant small-\(\varepsilon\) geometry is

\[
\ell<-1<r<\alpha<\beta<1,\qquad 1<A<-\ell.
\]

Under these inequalities the extracted measure is automatically positive.
Indeed, for \(t<\alpha\),
\[
R(t)=-\sqrt{(\alpha-t)(\beta-t)}<0.
\]
At \(t=\ell\), one has \(\ell+A<0\) and
\((\ell-r)(\ell-1)>0\), hence \(m_\ell>0\).  At \(t=r\), one has
\(r+A>0\), \(R(r)<0\), and \((r-\ell)(r-1)<0\), hence \(m_r>0\).  At
\(t=1\),
\[
m_1=
\frac{(1+A)\sqrt{(1-\alpha)(1-\beta)}}{(1-\ell)(1-r)}>0.
\]
For \(\alpha<x<\beta\), the factors satisfy
\[
x+A>0,\quad x-\ell>0,\quad x-r>0,\quad x-1<0,
\]
so the displayed formula for \(g(x)\) gives \(g(x)>0\).  Thus the measure
positivity part of the certificate reduces to the same two parameter
inequalities \(1<A<-\ell\) and \(\ell<-1<r<\alpha<\beta<1\); no numerical
sampling is needed for signs.

For \(x<\alpha\), the chosen branch satisfies

\[
R(x)=-\sqrt{(\alpha-x)(\beta-x)}.
\]

Hence:

- On \([-1,r)\), the denominator
  \((x-\ell)(x-r)(x-1)\) is positive and \(R(x)<0\), so
  \(F(x)<0\) and \(U_\lambda'(x)>0\).
- On \((r,\alpha)\), the denominator is negative and \(R(x)<0\), so
  \(F(x)>0\) and \(U_\lambda'(x)<0\).
- On \((\alpha,\beta)\), \(F_+(x)\) is purely imaginary, so
  \(U_\lambda\) is constant.
- On \((\beta,1)\), \(R(x)>0\) while the denominator is negative, so
  \(F(x)<0\) and \(U_\lambda'(x)>0\).

Therefore, once the parameter inequalities and positivity of the measure are
proved, the global positivity check on the reduced support

\[
S=\{-1\}\cup[0,1]
\]

reduces to the scalar contact checks

\[
U_\lambda(\alpha)=0,\qquad U_\lambda(-1)\ge0.
\]

For the sharp two-interval branch it is natural to impose the stronger two
equations

\[
U_\lambda(\alpha)=0,\qquad U_\lambda(-1)=0.
\]

This is the finite-dimensional system now used by the executable diagnostic
solver.

### 15.2 Executable small-\(\varepsilon\) diagnostic

The script

```text
1038/solve_two_interval_finite_gap.py
```

solves the corrected two-equation system numerically for the small-\(\varepsilon\)
branch.  It is not a proof certificate; it is a parameter generator and sign
chart diagnostic.

Running

```text
.venv/bin/python 1038/solve_two_interval_finite_gap.py
```

gives a valid sign-chart branch for

\[
\varepsilon=0.02,\ 0.01,\ 0.005,\ 0.002,\ 0.001,\ 0.0005.
\]

An abridged branch output is:

```text
epsilon = 0.02
  A alpha ell r beta = 1.378777322385 0.909389333809 -1.788107368099 0.026323107664 0.980000000000
  masses ell r 1 density total = 0.221103554722 0.729876597776 0.037302169547 0.011717677955 1.000000000000
  sign_chart_valid = True

epsilon = 0.01
  A alpha ell r beta = 1.336307929157 0.883938833284 -1.798107368099 0.026323107664 0.990000000000
  masses ell r 1 density total = 0.247371454202 0.697345793937 0.029214221018 0.026068530842 1.000000000000
  sign_chart_valid = True

epsilon = 0.005
  A alpha ell r beta = 1.300257941860 0.864578464547 -1.803107368099 0.026323107664 0.995000000000
  masses ell r 1 density total = 0.267905632959 0.671089826076 0.021930615040 0.039073925924 1.000000000000
  sign_chart_valid = True

epsilon = 0.002
  A alpha ell r beta = 1.262718769662 0.845277744819 -1.806107368099 0.026323107664 0.998000000000
  masses ell r 1 density total = 0.288145908677 0.644489012615 0.014568096960 0.052796981748 1.000000000000
  sign_chart_valid = True

epsilon = 0.001
  A alpha ell r beta = 1.241527550108 0.834482901929 -1.807107368099 0.026323107664 0.999000000000
  masses ell r 1 density total = 0.299195669832 0.629682626005 0.010550951467 0.060570752696 1.000000000000
  sign_chart_valid = True

epsilon = 0.0005
  A alpha ell r beta = 1.225547932088 0.826320275470 -1.807607368099 0.026323107664 0.999500000000
  masses ell r 1 density total = 0.307382773822 0.618588697817 0.007586566665 0.066441961696 1.000000000000
  sign_chart_valid = True
```

The current script also prints the limiting system, equation residuals, sampled
minimums, finite-difference determinants, scaled \(\sqrt\varepsilon\) deltas,
and the final status line

```text
OVERALL SIGN-CHART STATUS: PASS
```

This gives concrete evidence that the corrected finite-gap ansatz has the
right small-\(\varepsilon\) branch.  It also explains why the endpoint atom must
be handled theoretically: \(m_1\) decreases on the order of \(\sqrt\varepsilon\),
and the narrow interval \((1-\varepsilon,1)\) is exactly the scale at which
dense sampling can miss the endpoint interaction.

### 15.3 Limiting system and singular parameter branch

The diagnostic solver now also solves the \(\varepsilon=0\) limiting system.
Let

\[
L=x_L,\qquad R=x_R.
\]

As \(\varepsilon\to0\), the finite-gap transform becomes

\[
F_0(z)=
\frac{z+A_0}{(z-L)(z-R)}
\sqrt{\frac{z-a}{z-1}},
\qquad
\sqrt{\frac{z-a}{z-1}}\to1
\quad(z\to\infty).
\]

The pole at \(1\) disappears in the limit, but leaves an inverse-square-root
endpoint singularity in the density:

\[
g_0(x)=
\frac{x+A_0}{\pi(x-L)(x-R)}
\sqrt{\frac{x-a}{1-x}},
\qquad a<x<1.
\]

The limiting equations are

\[
U_0(a;A_0,a)=0,\qquad U_0(-1;A_0,a)=0.
\]

Numerically the solution is

```text
epsilon = 0 limiting system
  A alpha = 1.183353601765 0.804461769731
  masses ell r density total = 0.328499465873 0.589507218686 0.081993315441 1.000000000000
  residuals U(alpha), U(-1) = 8.521e-15 2.061e-15
```

The limiting \(\alpha\) is the same endpoint \(a\approx0.8044618\) seen in the
one-cut candidate.  This is strong evidence that the two-interval dual branch
is the correct degeneration of the conjectural extremal curve.

The endpoint atom has the scale

\[
m_1(\varepsilon)
=
\frac{(1+A_\varepsilon)\sqrt{(1-\alpha_\varepsilon)\varepsilon}}
{(1-\ell_\varepsilon)(1-r)}
=
D\sqrt{\varepsilon}+o(\sqrt{\varepsilon}),
\]

where

\[
D=
\frac{(1+A_0)\sqrt{1-a}}{(1-L)(1-R)}.
\]

Thus the natural small parameter is

\[
\eta=\sqrt{\varepsilon}.
\]

The diagnostic data gives evidence for Puiseux-type behavior, but this is not
yet a proved expansion:

```text
epsilon = 0.0005
  scaled deltas (A-A0)/sqrt(eps), (alpha-alpha0)/sqrt(eps)
  = 1.886987817327 0.977542094378
```

and smaller \(\varepsilon\) samples continue drifting toward finite limiting
slopes.  These numbers should be read as branch-location diagnostics for the
next interval-Newton step, not as proof of an asymptotic theorem.

There is also a warning: the Jacobian of the two limiting equations in
\((A,\alpha)\) is numerically nearly singular at \(\varepsilon=0\), while for
positive \(\varepsilon\) the finite-difference determinant is nonzero and
scales like \(\sqrt{\varepsilon}\):

```text
epsilon = 0.001   finite-difference det DG = -1.005613e-02
epsilon = 0.0005  finite-difference det DG = -6.976718e-03
```

So the branch should not be presented as a naive ordinary IFT at
\(\varepsilon=0\).  The proof target is a singular/interval IFT in
\(\eta=\sqrt{\varepsilon}\), or an interval Newton proof on explicit boxes for
each small \(\eta\)-range.

More precisely, finite differences for the limiting equations give

```text
DG0 approx =
  [ 0.70633353  -1.34435749 ]
  [-0.15032495   0.28611195 ]
```

The two rows are proportional to high numerical accuracy:

```text
row2 / row1 ≈ -0.21282431.
```

Thus \(DG_0\) is numerically rank one.  Its null direction satisfies

\[
\frac{\delta A}{\delta\alpha}\approx1.90328991.
\]

The observed small-\(\varepsilon\) branch has

```text
(A-A0)/(alpha-alpha0) ≈ 1.93, 1.92, 1.91
```

on the smallest sampled \(\varepsilon\)'s, drifting toward the same null
direction.  This is evidence for a singular rank-one degeneration, but by
itself it is not yet a theorem.  In a generic rank-one perturbation a
\(\sqrt\varepsilon\) forcing in the cokernel could produce an
\(\varepsilon^{1/4}\) displacement.  The required next lemma is therefore a
compatibility statement: the cokernel projection of the perturbation at
\((A_0,\alpha_0)\) must be \(O(\varepsilon)\), not \(O(\sqrt\varepsilon)\).

Using the approximate left-null vector \(w\approx(0.21282431,1)\), the script
now checks this cancellation at several scales:

```text
epsilon = 1e-3   w^T G_epsilon(A0,alpha0) / epsilon ≈ 0.221930361041
epsilon = 1e-4   w^T G_epsilon(A0,alpha0) / epsilon ≈ 0.222186986259
epsilon = 1e-5   w^T G_epsilon(A0,alpha0) / epsilon ≈ 0.222212630598
```

This is still diagnostic evidence.  The proof version must bound the projected
forcing uniformly on an \(\eta=\sqrt\varepsilon\) interval, either by an
analytic boundary-layer expansion or by a rigorous interval evaluation of the
projected residual.

The second derivative of the limiting system along the right-null direction
has projected curvature

```text
1/2 w^T D_x^2G_0[v,v] ≈ -0.20007.
```

Thus the reduced scalar equation is predicted to have the diagnostic form

\[
0.22221\,\varepsilon-0.20007\,t^2+\cdots=0,
\]

which predicts

\[
t\approx1.054\,\sqrt{\varepsilon},\qquad
\delta A\approx1.90329\,t\approx2.006\,\sqrt{\varepsilon}.
\]

This matches the observed scaled deltas and motivates a Lyapunov-Schmidt
ansatz of the form

\[
A_\varepsilon=A_0+c_A\eta+O(\eta^2),\qquad
\alpha_\varepsilon=\alpha_0+c_\alpha\eta+O(\eta^2),
\qquad
\eta=\sqrt{\varepsilon},
\]

with \((c_A,c_\alpha)\) close to the right-null direction of \(DG_0\).  The
scalar amplitude should be determined by the first nonzero projected equation
at the next order.  Proving this requires either a Lyapunov-Schmidt argument
with interval-certified constants or an interval-Newton/Krawczyk proof on
explicit boxes centered at the predicted branch.

The diagnostic script now prints exactly this first predicted center.  With
\[
A_{\rm pred}=A_0+2.005860607479\sqrt\varepsilon,\qquad
\alpha_{\rm pred}=\alpha_0+1.053891261372\sqrt\varepsilon,
\]
the observed errors satisfy

```text
epsilon = 0.002   (A-Apred)/eps, (alpha-alphapred)/eps = -5.169822768823 -3.157737468879
epsilon = 0.001   (A-Apred)/eps, (alpha-alphapred)/eps = -5.256933541936 -3.305835722371
epsilon = 0.0005  (A-Apred)/eps, (alpha-alphapred)/eps = -5.316152789096 -3.414438548460
```

This is the next certification target: for a dyadic range
\(\varepsilon\in[2^{-k-1},2^{-k}]\), prove that the true root lies in a box of
the form
\[
|A-A_{\rm pred}|\le C_A\varepsilon,\qquad
|\alpha-\alpha_{\rm pred}|\le C_\alpha\varepsilon,
\]
then use an interval Krawczyk contraction (interval nonsingularity plus residual
inclusion) to certify existence and uniqueness, while preserving all sign-chart
inequalities.
The present diagnostic run satisfies the conservative sample box
\[
|A-A_{\rm pred}|\le6\varepsilon,\qquad
|\alpha-\alpha_{\rm pred}|\le4\varepsilon
\]
for every tested \(\varepsilon\in\{0.02,0.01,0.005,0.002,0.001,0.0005\}\).

Following the review note, the solver also reports the Lyapunov-Schmidt
rescaled variables
\[
A=A_0+\eta(\nu\tau+B),\qquad
\alpha=a_0+\eta\tau,\qquad \eta=\sqrt\varepsilon,\quad
\nu\approx1.903289913295,
\]
and the rescaled system
\[
K_1=\eta^{-1}G_1,\qquad
K_2=\eta^{-2}(w_1G_1+G_2).
\]
At the actual numerical roots:

```text
epsilon = 0.002   B, tau; K residuals; det DK = 0.037577887294 0.912672948612; 3.103e-15 7.829e-15; -3.266000e-01
epsilon = 0.001   B, tau; K residuals; det DK = 0.032730530165 0.949351556842; -1.422e-13 -1.082e-12; -3.180026e-01
epsilon = 0.0005  B, tau; K residuals; det DK = 0.026441809275 0.977542094378; -4.096e-14 -4.037e-13; -3.120083e-01
```

This is the better Newton object: the original determinant in \((A,\alpha)\)
vanishes like \(\sqrt\varepsilon\), while the determinant of \(D_{(B,\tau)}K\)
is numerically bounded away from zero.  The proof version should certify
boxes in \((B,\tau)\), then map them back to boxes for \((A,\alpha)\).
The script now also prints the full finite-difference \(D_{(B,\tau)}K\) matrix
and step-size sensitivity.  For example:

```text
epsilon = 0.001
  DK rows = [0.691182690, -0.114070073] [-0.027821294, -0.455493246]
  det sensitivity h=1e-4,5e-5 = -3.180026e-01 -3.180026e-01
```

This table is only a diagnostic for choosing Krawczyk boxes; the proof still
requires interval enclosures for \(K\), \(D K\), and an approximate inverse.
The sampled Krawczyk diagnostic is already very far from the boundary:

```text
epsilon = 0.001
  radii B,tau = 1e-2, 1e-2
  correction = 1.844e-13, 2.364e-12
  inclusion  = 4.771821705383822e-06, 0.0001160680377195088
  margin     = 0.009995228178294617, 0.009883931962280492
  contraction = 0.01160680353556675
```

This is not a proof because \(DK\) is sampled rather than interval-enclosed,
but it shows the local Newton object is well conditioned.  The remaining
technical replacement is clear: evaluate \(K\) and \(DK\) with certified
quadrature/closed forms on the \((B,\tau)\)-box and check the same Krawczyk
inclusion inequalities.
The diagnostic sampler now also enlarges the sampling grid by the finite
difference stencil width, so the reported finite-difference \(DK\) values are
at least tested on the box plus the stencil halo.  This still does not replace
interval derivatives, but it removes the misleading impression that boundary
stencils were ignored.

The same data is exported as
`1038/two_interval_branch_certificate_skeleton.json`.  This file records the
limit parameters, each sampled \(\varepsilon\), the branch box, the
\((B,\tau)\)-Krawczyk box, the rescaled residuals, the sampled Jacobian, and
the sign margins.  It is intentionally a skeleton: every field has the right
mathematical role, but the proof version must replace sampled floating values
by outward-rounded interval enclosures.

2026-05-02 continuation.  The branch skeleton has been extended from the single
\(\varepsilon=0.001\) row to six small-\(\varepsilon\) rows:

```text
0.002, 0.001, 0.0005, 0.0002, 0.0001, 0.00005.
```

A separate checker now verifies the exported skeleton without rerunning the
nonlinear root search:

```text
.venv/bin/python 1038/verify_two_interval_branch_skeleton.py
.venv/bin/python 1038/verify_two_interval_branch_skeleton.py --arb-primitive-check
.venv/bin/python 1038/verify_two_interval_branch_skeleton.py --quiet --self-test-tamper
.venv/bin/python 1038/verify_two_interval_branch_skeleton.py --quiet --arb-primitive-check --self-test-tamper
.venv/bin/python 1038/verify_two_interval_branch_skeleton.py --quiet --arb-primitive-check --arb-center-residual-check --arb-box-uminus-check --arb-box-uminus-derivative-check --arb-box-contact-derivative-check --arb-box-dk-check --arb-interval-krawczyk-check --arb-box-dk-subdivisions 7,7 --self-test-tamper
```

The checker recomputes the masses, stored contact residuals, rescaled
\((B,\tau)\)-coordinates, analytic \(D_{(B,\tau)}K\), finite-difference
comparison, sampled Krawczyk inclusion/margin/contraction, branch/sign-chart
margins, and the stored residue-log path-separation metadata.  With
`--arb-primitive-check` it also recomputes the reduced Arb residue-log
primitive diagnostics.  With `--arb-center-residual-check` it additionally
computes an Arb/Acb ball for \(U(-1)\), combines it with the residue-log Arb
ball for \(U(-1)-U(\alpha)\), and checks the center \(K\)-residuals without
directly integrating the contact logarithmic singularity at \(\alpha\).  The
new `--arb-box-uminus-check` mode encloses \(U(-1)\) over each full local
Krawczyk parameter box.  For this box check the integral is evaluated in the
boundary-layer variable \(u=\sin(\theta/2)\), so

\[
t=\beta-2h u^2,\qquad t-1=-\varepsilon-2h u^2.
\]

This removes the spurious `nan` failure that the original \(\theta\)-coordinate
produced for the two smallest \(\varepsilon\)-rows, where automatic complex
neighbourhoods could cross the nearby pole at \(1\).  The same
boundary-layer primitive now encloses the \(U(-1)\) directional derivatives
with respect to the local \(B\) and \(\tau\) coordinates over each Krawczyk
box.  The verifier also has a diagnostic Arb/Acb full-box enclosure for the
contact derivatives of \(U(\alpha)\) in the same local \(B,\tau\) directions.
It uses the \(u=\sin(\theta/2)\) chart on the beta side, the
\(v=\cos(\theta/2)\) chart on the contact side, and a conservative real Arb
tail ball near \(v=0\), where the log kernel has its endpoint singularity.
The verifier now assembles these primitives into a diagnostic Arb interval
\(D_{(B,\tau)}K\) matrix and checks that each interval entry contains the center
analytic Jacobian entry.  The unsubdivided \(1\times1\) full-box Krawczyk
defect-action diagnostic is too wide in the \(\tau\) component; row 0 reports
defect \(4.135115\cdot10^{-2}\), radius \(10^{-2}\), margin
\(-3.135115\cdot10^{-2}\), and max \(DK\)-entry radius \(1.367222\).
The verifier now has a separate `--arb-interval-krawczyk-check` mode.  It
computes the center correction as an Arb upper bound for
\(|C K_{\mathrm{center}}|\), where \(C\) is the inverse of the analytic center
Jacobian converted to Arb constants, rather than using the stored floating
`krawczyk["correction"]` field.  Subdividing each local Krawczyk box into
\(7\times7\) Arb \(DK\) boxes then makes the diagnostic pass the componentwise
condition
\[
\operatorname{correction}_i+\max_{\text{subbox}}\|(I-CDK_{\text{subbox}})r\|_i<r_i.
\]
The worst passing component is at \(\varepsilon=0.001\), \(\tau\), with defect
\(5.836580\cdot10^{-3}\) and remaining margin \(4.163420\cdot10^{-3}\); here
the defect term, not the Arb center correction, is the dominant budget term.
The current fixed skeleton passes these modes:

Abbreviated status, suppressing the per-row margin and sign-margin fields:

```text
eps in {0.002, 0.001, 0.0005, 0.0002, 0.0001, 0.00005}: PASS
det ranges from -3.266000e-01 to -3.022843e-01
contraction ranges from 1.242655e-02 to 1.004098e-02
OVERALL TWO-INTERVAL SKELETON CHECK: PASS (6 rows)
```

The same checker now has an in-memory tamper self-test.  It deep-copies the
JSON payload, corrupts critical stored fields, and verifies that the checker
rejects them.  Without Arb recomputation it covers sampled margin, sampled
contraction, stored residual corruption, and branch-box sign corruption; with
`--arb-primitive-check` it also flips the stored Arb `contains_zero` boolean:

```text
OVERALL TWO-INTERVAL SKELETON CHECK: PASS
(6 rows; tamper self-test PASS 4 cases; verifier integrity only, not a math proof)

OVERALL TWO-INTERVAL SKELETON CHECK: PASS
(6 rows; tamper self-test PASS 5 cases; verifier integrity only, not a math proof)

OVERALL TWO-INTERVAL SKELETON CHECK: PASS
(6 rows; tamper self-test PASS 6 cases; verifier integrity only, not a math proof)
```

This is a real improvement in reproducibility, but it is still not the full
two-interval proof.  The sampled center correction has now been replaced in
this local diagnostic by an Arb center correction, while the remaining hard
replacement is to connect the outward-rounded primitives, sign/support
conditions, and parameter branch theorem into the full proof chain.  The Arb
center-residual, derivative box, subdivided \(DK\), and interval-Krawczyk checks
prove only the corresponding diagnostic local inclusion; they do not yet prove
the full two-interval branch or \(L_-\ge1.83\).

The same run now records the sign-chart margins for both the predicted branch
box and the local Krawczyk box.  At \(\varepsilon=0.001\):

```text
branch-box sign margins min, A>1, A<-ell, r<alpha, alpha<beta =
1.000000e-03 2.407845e-01 5.543229e-01 8.074656e-01 1.572113e-01

Krawczyk-box sign margins min, A>1, A<-ell, r<alpha, alpha<beta =
1.000000e-03 2.406094e-01 5.646617e-01 8.078436e-01 1.642009e-01
```

The minimum is only the trivial \(\beta<1\) margin \(=\varepsilon\).  The
structural inequalities needed for positivity of the extracted measure have
large margins.

Two additional standalone verifiers now split the branch skeleton into
independently checkable pieces:

```text
.venv/bin/python 1038/verify_two_interval_sign_box.py --quiet
.venv/bin/python 1038/verify_two_interval_sign_box.py --quiet --self-test-tamper
.venv/bin/python 1038/verify_two_interval_krawczyk_grid.py --quiet
.venv/bin/python 1038/verify_two_interval_krawczyk_grid.py --quiet --obligation-report
.venv/bin/python 1038/verify_two_interval_krawczyk_grid.py --quiet --refine-grid-sizes 11,21,41
.venv/bin/python 1038/verify_two_interval_krawczyk_grid.py --quiet --refine-grid-sizes 11,21,41 --obligation-report
```

The sign-box checker verifies the §15.1 sign chart on both the exported branch
box and the local Krawczyk box for all six \(\varepsilon\)-rows.  It checks the
ordering \(1<A<-\ell\), \(\ell<-1<r<\alpha<\beta<1\), the endpoint atom signs,
the continuous-density sign condition on \([\alpha,\beta]\), and that each
stored solution center lies in the corresponding exported box.  It also checks
that stored `sign_margins` fields match Decimal recomputation.  Its tamper
self-test corrupts a solution coordinate, a branch endpoint, a Krawczyk center
coordinate, and a stored sign margin to verify that these checks are live.  The
current certificate passes:

```text
OVERALL TWO-INTERVAL SIGN-BOX CHECK: PASS (6 rows, 12 boxes)
OVERALL TWO-INTERVAL SIGN-BOX CHECK: PASS
(6 rows, 12 boxes; tamper self-test PASS 4 cases; verifier integrity only, not a math proof)
```

The Krawczyk-grid checker samples the full \((B,\tau)\)-box on a deterministic
tensor grid, recomputes \(K\), analytic \(D_{(B,\tau)}K\), the center inverse,
the defect action \(|I-CDK|r\), and the inclusion margin.  It also rejects any
non-finite arithmetic before a `PASS` can be printed.  With the default
\(11\times11\) grid:

```text
OVERALL TWO-INTERVAL KRAWCZYK GRID STRESS CHECK: PASS (6 rows, grid=11x11,
worst_margin=9.876968e-03 at row 0, worst_contraction=1.230325e-02)
```

The same checker now has an explicit refinement/stability mode.  It repeats
the full-box Krawczyk stress check on several increasing tensor grids, reports
the drift between successive grids for each row, and rejects a refinement list
with fewer than two grid sizes so that a single grid cannot be mislabeled as a
stability test.  With grids \(11,21,41\):

```text
OVERALL TWO-INTERVAL KRAWCZYK GRID REFINEMENT STRESS CHECK: PASS (6 rows,
grids=[11,21,41], worst_margin=9.876968e-03 at row 0 grid=11x11,
worst_contraction=1.230325e-02, max_refinement_drift=0.000000e+00,
row_drifts=[0:0.000000e+00,1:0.000000e+00,2:0.000000e+00,
3:0.000000e+00,4:0.000000e+00,5:0.000000e+00],
caveat=deterministic sampled stress evidence, not outward-rounded interval proof)
```

The checker also has an intervalization-budget report.  It does not prove any
interval enclosure; it translates the unused sampled Krawczyk margin into a
target budget for the next proof-grade primitives.  With a conservative split
that reserves half of the margin for enclosing \(K\) at the center and half for
enclosing \(D_{(B,\tau)}K\) over the full box, the current six-row skeleton gives

```text
TWO-INTERVAL KRAWCZYK INTERVALIZATION BUDGET
(rows=6, margin_split=centerK:0.5,DK:0.5,
worst_margin=9.876968e-03 at row 0,
min_uniform_center_K_radius=2.110507e-03 at row 5,
min_uniform_DK_entry_radius=1.055254e-01 at row 5,
caveat=budget for future outward-rounded primitives, not a proof)
```

This gives the next implementation target a numerical scale: the
outward-rounded center residual primitive must enclose \(K(x_0)\) in rescaled
coordinates substantially below \(2\cdot10^{-3}\), and the interval
Jacobian primitive must enclose each \(DK\) entry, beyond the sampled envelope,
comfortably below \(10^{-1}\).  These are generous enough that the line is not
blocked by local conditioning; the real work is still certified evaluation of
the logarithmic/endpoint-singular integrals.

This sampled stress evidence has now been superseded, for the stored finite
\(\varepsilon\)-range recorded below, by proof-grade interval winding
certificates.  The sampled grid remains useful as an independent conditioning
diagnostic, but it is no longer the branch-existence evidence for these slabs.

### 15.3.1 Current branch closure: proof-grade winding certificate on \([0.00005,0.002]\)

This subsection records exactly what has now been connected back to the current
two-interval branch.  The first proof-grade closure was obtained on
\([0.0002,0.0005]\); the remaining stored slabs have now been promoted to the
same interval-winding certificate status.  Let
\[
\eta=\sqrt{\varepsilon},\qquad
(A,\alpha)=(A_0,\alpha_0)+\eta(B+\nu\tau,\tau),
\]
where \((A_0,\alpha_0)\), \(\nu\), and the left weight \(w\) are the constants
exported in `1038/two_interval_branch_certificate_top_split.json`.  Define the
rescaled branch map
\[
K(B,\tau,\eta)
=
\left(
\frac{U_{\lambda^{(\varepsilon)}}(\alpha)}{\eta},
\frac{w\,U_{\lambda^{(\varepsilon)}}(\alpha)+U_{\lambda^{(\varepsilon)}}(-1)}
{\eta^2}
\right).
\]

For the initial slab
\[
\varepsilon\in[0.0002,0.0005],
\]
the current certificate covers the tube
\[
(B,\tau)=(B_c(\eta),\tau_c(\eta))
       +[-0.00029,0.00029]^2,
\]
where \((B_c,\tau_c)\) is the affine interpolation between the two exported
endpoint rows.  The interval verifier subdivides the \(\eta\)-range into
1024 slices and each tube boundary into 8 boxes per side, with adaptive
subdivision depth 2 where the angle enclosure is too wide.

The proof-grade command is:

```bash
.venv/bin/python 1038/verify_two_interval_continuation_tube.py \
  1038/two_interval_branch_certificate_top_split.json \
  --config 0.0002:0.0005:0.00029,0.00029:16,1 \
  --eta-interval-dk-kernel residue-log \
  --interval-boundary-value-kernel residue-log-mv \
  --interval-boundary-winding 1024,8 \
  --interval-boundary-winding-adaptive-depth 2 \
  --max-weighted-defect 10
```

For wall-clock reasons the full run was executed on `hkgai-studio`
(`100.72.237.101`) as 1024 half-open eta slices
`--interval-boundary-winding-eta-slice i:i+1`, with 20 workers.  The final
checked artifact for commit `914ec72` gives:

```text
remote_final logs=1024 pass=1024 fail=0
min_origin=1.178783e-05
max_angle=1.535505
```

The remaining stored slabs were then run with the same certification kernel,
the same winding boundary split (`ETA,8`), and adaptive depth 2, using the
diagnostic radii recorded in §16.3.  The remote run on `hkgai-studio`
(`100.72.237.101`) split every eta subdivision as an individual half-open
slice and used 20 workers.  It returned:

```text
0.00005:0.0001   radius=0.0003  eta=224   pass=224/224   fail=0
                 min_origin=9.443237e-05  max_angle=0.3061034
0.0001:0.0002    radius=0.0003  eta=224   pass=224/224   fail=0
                 min_origin=7.015515e-05  max_angle=0.4437094
0.0005:0.001     radius=0.0006  eta=1344  pass=1344/1344 fail=0
                 min_origin=1.566601e-04  max_angle=0.3207439
0.001:0.00125    radius=0.0002  eta=224   pass=224/224   fail=0
                 min_origin=5.013406e-05  max_angle=0.4173290
0.00125:0.0015   radius=0.0002  eta=224   pass=224/224   fail=0
                 min_origin=5.429313e-05  max_angle=0.3893125
0.0015:0.00175   radius=0.0002  eta=224   pass=224/224   fail=0
                 min_origin=4.912411e-05  max_angle=0.4545586
0.00175:0.002    radius=0.0002  eta=224   pass=224/224   fail=0
                 min_origin=5.765748e-05  max_angle=0.3794442
```

Thus the complete stored finite range now has proof-grade branch-existence
coverage:

```text
[0.00005,0.0001]  union [0.0001,0.0002] union [0.0002,0.0005]
union [0.0005,0.001] union [0.001,0.00125] union [0.00125,0.0015]
union [0.0015,0.00175] union [0.00175,0.002].
```

Representative slice outputs are:

```text
eta=0:   interval_boundary_winding_status=proof
         interval_boundary_winding_degree_abs=1
         interval_boundary_winding_min_origin=1.198808e-04

eta=512: interval_boundary_winding_status=proof
         interval_boundary_winding_degree_abs=1
         interval_boundary_winding_min_origin=1.179814e-05

eta=1023: interval_boundary_winding_status=proof
          interval_boundary_winding_degree_abs=1
          interval_boundary_winding_min_origin=1.231885e-04
```

The logical use is the standard planar degree argument.  For each fixed
\(\eta\)-slice, the interval boundary image avoids the origin and its ordered
angle sectors close with winding number \(1\).  Therefore \(K(\cdot,\cdot,\eta)\)
has a zero inside the certified \((B,\tau)\)-tube.  The strict sign margins
reported by the same run ensure the corresponding \((A,\alpha)\)-box stays in
the two-interval sign regime
\[
1<A<-\ell,\qquad \ell<-1<r<\alpha<\beta<1.
\]

The `residue-log-mv` kernel is the certification kernel here.  It evaluates
the residue-log primitive at the midpoint and encloses the full box by Arb
mean-value inflation, including removable-factor eta-variation kernels for
both
\[
U(\alpha)/\eta
\quad\text{and}\quad
\bigl(wU(\alpha)+U(-1)\bigr)/\eta^2.
\]
The older `sampled-lipschitz` mode is explicitly diagnostic-only and is not
used for this proof certificate.

What is now closed:

1. the local branch-existence certificate on
   \(\varepsilon\in[0.00005,0.002]\), split into the eight stored slabs above;
2. the proof-grade replacement of the sampled center correction for this finite
   stored range;
3. a reproducible command package and remote parallel verification record;
4. orientation-correct adaptive boundary splitting and strict eta-slice
   coverage checks.

### 15.3.2 Global positivity from the sign chart on the stored finite range

The next bridge is now implemented as
`1038/verify_two_interval_global_positivity.py`.  It verifies the sign-chart
theorem that turns the local branch equation into the global dual sign
condition on
\[
S=\{-1\}\cup[0,1].
\]

For the corrected two-interval ansatz, outside the cut \([\alpha,\beta]\),
\[
U'(x)=-F(x),\qquad
F(x)=\frac{(x+A)R(x)}{(x-\ell)(x-r)(x-1)}.
\]
The verifier checks, over every certified tube slice in the stored finite
range, that
\[
1<A<-\ell,\qquad \ell<-1<r<\alpha<\beta<1
\]
and the accompanying residue/density sign margins hold.  These inequalities
force
\[
F<0\quad\text{on }[-1,r),\qquad
F>0\quad\text{on }(r,\alpha),\qquad
F<0\quad\text{on }(\beta,1).
\]
Since the winding certificate supplies a zero of the branch map in each tube,
that zero has \(U(\alpha)=0\) and \(U(-1)=0\); the ansatz identity gives the
flat-zero interval on \([\alpha,\beta]\).  Therefore \(U\ge0\) on
\(\{-1\}\cup[0,1]\) for each certified branch point in the stored finite range.

The command is:

```bash
.venv/bin/python 1038/verify_two_interval_global_positivity.py \
  --self-test-tamper
```

Local and remote runs both return:

```text
TWO-INTERVAL GLOBAL POSITIVITY: PASS
configs=8
worst_margin=5.000000e-05
worst_slab=5e-05:0.0001
worst_margin_name=beta<1
```

The tamper self-test deliberately moves one tube outside the safe sign chart
and is rejected before the normal certificate is checked.

What is not yet closed:

1. the singular range \(0<\varepsilon<0.00001\), which needs a small-\(\eta\)
   theorem rather than another finite row sampling run;
2. a direct interval lower-bound audit of \(U(x)\) on all real segments; this
   is no longer the main positivity proof for the stored branch, but remains a
   useful independent proof artifact;
3. the global reduction from arbitrary candidate sets \(E\) to this
   two-interval obstruction family;
4. the matching upper construction needed for the exact infimum.

### 15.4 Correct next proof theorem

The endpoint boundary layer is useful for deriving the \(\eta\)-expansion, but
it is not the main positivity bottleneck.  Once the sign chart and contact
equations are proved, the interval \((\beta,1)\) is already handled by
monotonicity:

\[
U_\lambda(\beta)=0,\qquad U'_\lambda(x)>0\quad(\beta<x<1).
\]

Therefore the next theorem should be the parameter-branch theorem:

There exists \(\varepsilon_0>0\) such that for every
\(0<\varepsilon\le\varepsilon_0\), the system

\[
G_\varepsilon(A,\alpha)
:=
\bigl(U_{\lambda^{(\varepsilon)}}(\alpha),
U_{\lambda^{(\varepsilon)}}(-1)\bigr)
=
(0,0)
\]

has a solution satisfying

\[
1<A<-\ell,\qquad \ell<-1<r<\alpha<\beta<1,
\]

and the extracted residues and density are nonnegative.  The equality
\(U(-1)=0\) selects the sharp/equioscillating branch; for positivity alone
\(U(-1)\ge0\) would suffice.

Once this theorem is proved, the two-interval dual certificate follows from
the sign chart in §15.1 and the duality lemma.  The remaining exact-infimum
gap would then be the global reduction from arbitrary candidate sets \(E\) to
the one-interval/two-interval obstruction family.

### 15.5 Why interval-enclosed analytic \(DK\) is the next hard target

The current diagnostic Krawczyk table already uses the analytic
\(D_{(B,\tau)}K\), with finite differences retained only as an independent
comparison.  It is still not certification-grade because the analytic
derivative is evaluated at floating sample points rather than enclosed on the
whole two-dimensional box, and it does not control quadrature, truncation, or
roundoff.  The next proof step is to replace the sampled floating evaluations
of \(K\), \(DK\), and the approximate inverse action by outward-rounded
interval enclosures.

Write the potential of the extracted measure as

\[
U(x;p)=
\sum_{q\in\{\ell,r,1\}} m_q(p)\log\frac1{|x-q|}
+\int_{\alpha}^{\beta} g(t;p)\log\frac1{|x-t|}\,dt,
\]

where \(p=(\eta,A,\alpha)\), \(\ell=L+\eta^2\), \(\beta=1-\eta^2\), and

\[
g(t;p)=
-\frac{t+A}{\pi(t-\ell)(t-r)(t-1)}
\sqrt{(t-\alpha)(\beta-t)}.
\]

Use the fixed substitution

\[
t=\frac{\alpha+\beta}{2}+\frac{\beta-\alpha}{2}\cos\theta,\qquad
0\le\theta\le\pi.
\]

Then

\[
\sqrt{(t-\alpha)(\beta-t)}\,dt
=
\left(\frac{\beta-\alpha}{2}\right)^2\sin^2\theta\,d\theta,
\]

up to orientation.  Taking absolute orientation gives a smooth fixed-interval
integral.  For \(x\notin[\alpha,\beta]\) the integrand is smooth.  For the
contact value \(x=\alpha\), the only singularity is integrable of type
\(\sin^2\theta\log(1-\cos\theta)\).

Thus \(DK\) should be computed by differentiating this fixed-interval formula,
not by finite differences.  The differentiated integrands are rational
functions of \(t\), endpoint factors already absorbed into \(\sin^2\theta\),
and logarithms.  They can be enclosed by interval quadrature or further reduced
to closed-form logarithm/arctangent expressions.

The proof-grade replacement for the current script is:

1. Enclose \(K(B,\tau,\eta)\) at the chosen center with interval arithmetic.
2. Enclose the full matrix \(D_{(B,\tau)}K\) on the \((B,\tau,\eta)\)-box using
   analytic derivative formulas, not finite differences.
3. Use the floating inverse \(C\approx DK(x_0)^{-1}\) with outward-rounded
   interval entries and verify
\[
|C K(x_0)|+\sup_X |I-C\,DK(X)|\,r < r.
\]
4. Verify the same parameter box implies
\[
1<A<-\ell,\qquad \ell<-1<r<\alpha<\beta<1.
\]

This proves the small-\(\varepsilon\) two-interval branch on a certified
\(\eta\)-range.  Repeating this on dyadic ranges and matching to the limiting
Lyapunov-Schmidt expansion is the route to all sufficiently small
\(\varepsilon\).

The stable derivative formulas for the fixed-\(\theta\) representation are as
follows.  Put
\[
D(t)=(t-\ell)(t-r)(t-1),\qquad
H(\theta;p)=
-\frac{h^2\sin^2\theta}{\pi}\frac{t+A}{D(t)}.
\]
For fixed \(\eta\),
\[
\partial_B=\eta\,\partial_A,\qquad
\partial_\tau=\eta(\nu\partial_A+\partial_\alpha),
\]
where \(\nu\) is the right-null slope.  Also
\[
t_\alpha=\frac{1-\cos\theta}{2},\qquad h_\alpha=-\frac12.
\]
The kernel derivatives are
\[
H_A=-\frac{h^2\sin^2\theta}{\pi D(t)},
\]
and
\[
H_\alpha=
\frac{\sin^2\theta}{\pi}
\left[
h\,\frac{t+A}{D(t)}
-h^2 t_\alpha\frac{D(t)-(t+A)D'(t)}{D(t)^2}
\right].
\]

For the fixed evaluation point \(x=-1\),
\[
\partial_s U(-1;p)
=
\sum_q m_{q,s}\log\frac1{|-1-q|}
+\int_0^\pi
\left[
H_s\log\frac1{|-1-t|}
+H\,\frac{t_s}{-1-t}
\right]d\theta .
\]
For the contact value \(U(\alpha;p)\), differentiate the moving endpoint value
directly:
\[
\partial_s U(\alpha;p)
=
\sum_q
\left[
m_{q,s}\log\frac1{|\alpha-q|}
-m_q\frac{\alpha_s}{\alpha-q}
\right]
+\int_0^\pi
\left[
H_s\log\frac1{|\alpha-t|}
+\frac{\alpha_s}{2h}H
\right]d\theta .
\]
The identity
\[
\frac{t_s-\alpha_s}{\alpha-t}=\frac{\alpha_s}{2h}
\]
is the important cancellation at the contact endpoint; computing
\(\partial_sU(\alpha;p)\) as separate singular pieces \(U_s+\alpha_sU_x\)
would be numerically and analytically unstable.

This analytic \(DK\) formula has now been implemented numerically and compared
against finite differences.  The agreement is at the \(10^{-10}\) level:

```text
epsilon = 0.001
  analytic DK rows; det; max|analytic-fd| =
  [0.691182690, -0.114070073] [-0.027821294, -0.455493246];
  -3.180026e-01; 1.845e-10
```

The Krawczyk diagnostic itself now uses this analytic \(DK\).  Finite
differences remain only as an external comparison line.  So the next interval
implementation can follow the same derivative path and replace only the
floating integrations by interval enclosures.

There is a further simplification for the second scalar equation.  Instead of
evaluating both \(U(\alpha)\) and \(U(-1)\) by log-kernel integrals, write
\[
F_{\rm cont}(x)=
F(x)-\frac{m_\ell}{x-\ell}-\frac{m_r}{x-r}-\frac{m_1}{x-1}.
\]
The pole at \(x=r\) is removable; its value is the regular part of \(F\) at
\(r\):
\[
\left.\frac{d}{dx}\left(
\frac{(x+A)R(x)}{(x-\ell)(x-1)}
\right)\right|_{x=r}
-\frac{m_\ell}{r-\ell}-\frac{m_1}{r-1}.
\]
Then
\[
U(-1)-U(\alpha)
=
\sum_{q\in\{\ell,r,1\}}m_q
\left(
\log\frac1{|-1-q|}-\log\frac1{|\alpha-q|}
\right)
+\int_{-1}^{\alpha}F_{\rm cont}(x)\,dx.
\]
This replaces one log-kernel integral by an algebraic integral of
\(F_{\rm cont}\).  Numerically, after inserting the removable value at \(r\),
the identity checks at the root:

```text
epsilon = 0.001
  U(-1)-U(alpha): direct, F-cont integral, abs diff =
  -6.939e-17 -4.469e-15 4.399e-15
```

So a proof-grade checker can use \(U(\alpha)=0\) plus this difference equation,
reducing the amount of interval log-kernel quadrature.

Using the Joukowski coordinate
\[
z=c+k(w+w^{-1}),\qquad R=k(w-w^{-1}),
\]
with \(c=(\alpha+\beta)/2\) and \(k=(\beta-\alpha)/4\), the differential
\[
F_{\rm cont}(z(w))\,z'(w)\,dw
\]
is a rational function of \(w\).  Thus
\[
\int_{-1}^{\alpha}F_{\rm cont}(x)\,dx
\]
can be evaluated as a finite sum of residue-log terms between the two real
preimages \(w(-1)<-1\) and \(w(\alpha)=-1\).  A high-precision numerical
check at \(\varepsilon=0.001\) gives

```text
residue-log primitive = -0.177978719152816778137103086864
direct F_cont integral = -0.17797871915281696
absolute difference ≈ 2e-16
```

This is the preferred certification route for the difference equation:
isolate the finitely many poles in \(w\), enclose the residues and logarithms,
and avoid quadrature altogether.

Engineering note: a direct `acb_poly.roots()` call on the unreduced
floating-coefficient denominator failed to converge, likely because the
Joukowski denominator still contains removable or nearly repeated factors after
the pole subtraction.  This is not a mathematical obstruction; the certificate
should first squarefree/cancel the rational function exactly in the chosen
parameter box, or use isolated SymPy roots as starting data and then refine
with Arb balls.

This has now been resolved at the fixed-parameter diagnostic level.  Instead
of using the unreduced `cancel` expression, forming the rational function with
`together` and then explicitly cancelling the removable physical preimage of
\(r\) gives a degree \(5/6\) rational function in \(w\).  On this reduced
form, `acb_poly.roots(tol=2^{-120}, maxprec=512)` succeeds and the
residue-log primitive gives Arb real balls.  The remaining poles are separated
from the integration path by a large margin:

```text
epsilon = 0.002
[-0.160321625721710773668570991785890441113002350681877376235011440499163686 +/- 2.99e-73]
path separation ≈ 0.9572774

epsilon = 0.001
[-0.177978719152763789865257351646441823004380971905459153238491310975847379 +/- 3.20e-73]
path separation ≈ 0.9537101

epsilon = 0.0005
[-0.190726171114993411860062559849132796270165700003052824823968125159783864 +/- 3.67e-73]
path separation ≈ 0.9510497
```

The imaginary ball is large because of complex logarithm branch choices, but
the real part is the certified real integral value needed for
\(\int_{-1}^{\alpha}F_{\rm cont}(x)\,dx\).  This is the first working Arb
version of the difference-equation certificate at fixed parameter points.  It
still has to be lifted from point parameters to parameter boxes for the
Krawczyk proof.

### 15.6 Boundary-layer expansion needed for the branch theorem

The finite small-\(\eta\) band has now been pushed below the previous stored
endpoint.  A fresh certificate generated by

```bash
.venv/bin/python 1038/solve_two_interval_finite_gap.py \
  --epsilons 1e-5,2e-5,5e-5 \
  --write-json 1038/two_interval_small_eta_certificate.json
```

adds endpoint rows at
\[
\varepsilon=10^{-5},\quad 2\cdot10^{-5},\quad 5\cdot10^{-5}.
\]
On `hkgai-studio`, the same proof-grade winding verifier was run on the two
adjacent slabs with 20 workers:

```text
0.00001:0.00002  radius=0.01  eta=224  pass=224/224  fail=0
                 min_origin=0.004211969  max_angle=0.2061609
0.00002:0.00005  radius=0.01  eta=224  pass=224/224  fail=0
                 min_origin=0.004201194  max_angle=0.2059112
```

The command shape was:

```bash
.venv/bin/python 1038/verify_two_interval_continuation_tube.py \
  1038/two_interval_small_eta_certificate.json \
  --config EPS_LOW:EPS_HIGH:0.01,0.01:16,1 \
  --eta-interval-dk-kernel residue-log \
  --interval-boundary-value-kernel residue-log-mv \
  --interval-boundary-winding 224,8 \
  --interval-boundary-winding-adaptive-depth 2 \
  --interval-boundary-winding-eta-slice i:i+1 \
  --max-weighted-defect 100
```

Here `--max-weighted-defect 100` is used because the weighted Krawczyk defect
is only a conditioning diagnostic in the winding proof.  With the old
diagnostic threshold 10 the small-\(\eta\) slabs were rejected solely by
`weighted_defect`, while the winding boundary proof itself remained the
relevant certificate gate.

The sign-chart/global-positivity bridge also passes on the new small-\(\eta\)
certificate:

```bash
.venv/bin/python 1038/verify_two_interval_global_positivity.py \
  1038/two_interval_small_eta_certificate.json \
  --config 0.00001:0.00002:0.01,0.01:224,1 \
  --config 0.00002:0.00005:0.01,0.01:224,1
```

with:

```text
TWO-INTERVAL GLOBAL POSITIVITY: PASS
configs=2
worst_margin=1.000000e-05
worst_slab=1e-05:2e-05
worst_margin_name=beta<1
```

Thus the finite certified branch range is now
\[
10^{-5}\le\varepsilon\le 0.002.
\]
The next tiny-\(\eta\) push uses
`1038/two_interval_tiny_eta_certificate.json`, generated at
\[
\varepsilon=10^{-8},\quad 10^{-6},\quad 10^{-5}.
\]
The standard winding proof still works if the weighted DK-defect diagnostic is
disabled.  That diagnostic becomes numerically non-finite in the tiny band, but
it is not the proof gate; the proof gate is boundary winding plus sign margins.
The verifier now has an explicit `--skip-weighted-defect` switch for this
purpose.

The remote split run on `hkgai-studio` gives:

```text
0.00000001:0.000001  radius=0.01  eta=4096  pass=4096/4096  fail=0
                    min_origin=0.004193370  max_angle=0.2304717
0.000001:0.00001    radius=0.01  eta=1024  pass=1024/1024  fail=0
                    min_origin=0.004198067  max_angle=0.2069766
```

The global positivity bridge also passes:

```text
TWO-INTERVAL GLOBAL POSITIVITY: PASS
configs=2
worst_margin=1.000000e-08
worst_slab=1e-08:1e-06
worst_margin_name=beta<1
```

Thus the finite certified branch range is now
\[
10^{-8}\le\varepsilon\le0.002.
\]
The remaining genuinely singular gap is
\[
0<\varepsilon<10^{-8}.
\]

The limiting target for that final transfer is now isolated by
`1038/verify_two_interval_small_eta_limit.py`.  In the fold coordinates, the
\(\eta=0\) normal form is
\[
K_0(B,\tau)=\bigl(J_{00}B,\ f+c\tau^2\bigr),
\]
with \(J_{00}>0\), forcing \(f>0\), and curvature \(c<0\).  The verifier checks
the rectangle
\[
B\in[-0.01,0.01],\qquad
\tau\in[\tau_0-0.05,\tau_0+0.05],
\quad
\tau_0=\sqrt{-f/c},
\]
and returns:

```text
TWO-INTERVAL SMALL-ETA LIMIT: PASS
degree_abs=1
min_origin=7.063335e-03
bottom_k2=2.058479813419e-02
top_k2=-2.158513698957e-02
min_structural_margin=1.833536e-01
```

So the remaining theorem has a precise target: prove a uniform remainder bound
on \(K_\eta-K_0\) over this rectangle, for
\(0<\eta<10^{-4}\), small enough not to change the limiting winding.

The first diagnostic implementation of this comparison is
`1038/verify_two_interval_small_eta_remainder.py`.  It compares the positive
\(\eta\) residue-log map against the full quadratic limiting map
\[
K_0(B,\tau)=
\bigl(J_{00}B,\ f+q_{20}B^2+q_{11}B\tau+q_{02}\tau^2\bigr)
\]
on the boundary rectangle.  This is not yet a proof artifact.  On the current
sampled test over \(10^{-8}\le\eta\le10^{-4}\), the worst remainder/min-origin
ratio is about \(97\), with the worst point at \(\eta=10^{-8}\).  Therefore the
finite proof-grade winding is closed down to \(10^{-8}\), but the final
singular gap still needs a stronger joint \(\eta=0\) residual kernel or a
sharper analytic cancellation before it can become a continuum theorem.

The next diagnostic cut identifies the bad term.  With solver debug algebra
enabled, the worst point contains

```text
limit_layer_joint_identity:combined_limit = -6.872079e-9
limit_layer_joint_analytic_limit_over_eta:combined = -0.6872079
```

This single leftover \(O(\eta)\) joint-limit term accounts for essentially all
of the failed ratio.  If the diagnostic subtracts that removable joint-limit
layer before comparing with \(K_0\), the same sampled box gives:

```text
TWO-INTERVAL SMALL-ETA REMAINDER: PASS-DIAGNOSTIC
max_remainder=1.690799e-04
limiting_min_origin=7.063335e-03
ratio=2.393769e-02
```

This is still not a proof.  It says the promising next proof kernel is not more
epsilon slicing; it is a joint residual-level expression in which the
limit-layer \(O(\eta)\) term is cancelled before the final eta division.  A
direct finite-value check also shows that raw direct, paired, and renormalized
K2 values differ off branch, while they agree to zero on the solved branch.
Thus the immediate blocker is to define the exact residual map used for the
continuum winding and prove its equivalence to the original equations, rather
than only tuning the existing diagnostic.

The solver now exposes this as an explicit experimental kernel:
`regularize_joint_limit_layer=True`, and
`verify_two_interval_continuation_tube.py` has the matching
`--regularize-joint-limit-layer` switch.  This removes the debug-label
post-processing from the diagnostic and makes the next kernel test reproducible.
The initial continuation test exposed an implementation bug: the regularized
midpoint value in the residue-log-mv kernel was evaluated on the whole eta box
instead of at the eta midpoint, so the midpoint K2 ball carried a spurious
radius of about \(5.35\cdot10^{-3}\).  After changing that midpoint evaluation
to a point Arb value, the regularized kernel passes the same finite tiny-slab
winding checks:

```text
small-eta remainder with --renormalize-limit-layer:
  ratio=2.393769e-02  PASS-DIAGNOSTIC

regularized tiny-slab continuation, remote:
  [1e-8,1e-6]  pass=4096/4096  fail=0
                min_origin=0.004166323  max_angle=0.2085875
  [1e-6,1e-5]  pass=1024/1024  fail=0
                min_origin=0.004204536  max_angle=0.2066907
```

So the regularized kernel now fixes the sampled \(K_\eta-K_0\) comparison and
also behaves stably on the already-certified positive finite tiny slabs.  It is
still not closure of \(0<\varepsilon<10^{-8}\): the missing theorem is the
equivalence/regularity lemma saying that the regularized residual map has the
same zero set as the original equations and admits uniform Arb remainder bounds
as \(\eta\to0\).

The finite-eta consistency part of that lemma is now checked by
`1038/verify_two_interval_regularized_equivalence.py`.  It solves the branch
at selected epsilons and compares:

1. the original rescaled residual;
2. the regularized residual;
3. the finite-difference Jacobian determinants and orientation signs.

Default run:

```text
TWO-INTERVAL REGULARIZED EQUIVALENCE: PASS-DIAGNOSTIC
rows=7
worst_original=3.505319e-08
worst_regularized=3.340711e-07
min_abs_det_original=2.998338e+04
min_abs_det_regularized=2.998339e+04
max_condition_regularized=8.231365e+00
orientation_mismatches=0
```

With `--arb-fd-det`, the same checker also evaluates the regularized
finite-difference Jacobian determinant as an Arb ball.  This is still not the
analytic derivative theorem, but it removes floating-point ambiguity from the
determinant nonzero check:

```text
TWO-INTERVAL REGULARIZED EQUIVALENCE: PASS-DIAGNOSTIC
rows=7
min_arb_fd_det_abs_lower=2.998339e+04
arb_fd_det_contains_zero=0
```

An extra near-singular diagnostic down to \(\varepsilon=3\cdot10^{-10}\) also
keeps the Jacobian non-singular and orientation-consistent, but residuals rise
to about \(5.7\cdot10^{-5}\), which is the current double/quadrature accuracy
floor rather than a proof artifact.  The proof-grade version still needs Arb
interval equations for the equivalence identity and an analytic derivative
formula giving a uniform lower bound for the regularized Jacobian determinant.

`1038/verify_two_interval_regularized_difference.py` records one implementation
hazard that matters for the proof package: raw K2 and regularized K2 should not
be mixed casually inside the same process.  Calling the raw grouped K2 path
before the regularized path can perturb the subsequent regularized evaluation
through shared Arb/context state.  The diagnostic therefore evaluates the
canonical regularized path first and treats the regularized kernel as the proof
object.  In that order, the branch and finite/tiny grid checks report no
raw-minus-regularized discrepancy on the certified finite slabs; the separate
small-\(\eta\) remainder comparison still shows that the canonical regularized
kernel is the one matching the limiting \(K_0\) normal form.

This means the next artifact should not try to prove equivalence by comparing
two implementation paths.  It should define the regularized residual directly,
then prove:

1. \(K_1=U(\alpha)/\eta\) is unchanged;
2. the regularized K2 equation is the correctly cancelled expression for
   \((wU(\alpha)+U(-1))/\eta^2\);
3. the regularized Jacobian has a uniform nonzero determinant as
   \(\eta\to0\).

To prove the parameter-branch theorem uniformly as \(\varepsilon\to0\), the
endpoint layer should still be analyzed with

\[
s=\frac{1-x}{\varepsilon}.
\]

For \(x=1-\varepsilon s\), the endpoint atom contributes

\[
-m_1\log(\varepsilon s)
=-m_1\log\varepsilon-m_1\log s.
\]

Since

\[
m_1=
\frac{(1+A)\sqrt{(1-\alpha)\varepsilon}}{(1-\ell)(1-r)},
\]

the leading boundary-layer contribution is of size

\[
\sqrt{\varepsilon}\,|\log\varepsilon|.
\]

The proof should subtract the contact value \(U_\lambda(\beta)=0\) when studying
local positivity.  But for branch existence the more important use is to prove
that

\[
G_\varepsilon(A,\alpha)
=
G_0(A,\alpha)
+\sqrt{\varepsilon}\,G_1(A,\alpha)
+O(\varepsilon|\log\varepsilon|)
\]

or a comparable rigorous enclosure.  If one also wants an explicit local
positivity profile, it should be formulated as

\[
U_{\lambda^{(\varepsilon)}}(1-\varepsilon s)
=
\sqrt{\varepsilon}\,P_0(s)
+\text{controlled remainder},
\qquad 0<s\le1,
\]

and the remainder is smaller than the positive margin of \(P_0\) away from
\(s=1\), while a separate Taylor/monotonicity argument handles the contact
region near \(s=1\).

The endpoint-layer proof must be split into:

1. \(s\in(0,s_0]\), where the endpoint atom dominates through
   \(-\log s\);
2. \(s\in[s_0,1-\delta]\), where the leading profile is certified by interval
   quadrature and tail bounds;
3. \(s\in[1-\delta,1]\), where a Taylor/monotonicity certificate at
   \(s=1\) is required.

The finite-gap exact route now has a concrete next bottleneck:

\[
\boxed{\text{prove the small-}\varepsilon\text{ parameter branch theorem for }
G_\varepsilon(A,\alpha)=0.}
\]

Until this is done, §15 is a strong exact-route program and a working parameter
generator, not a proof of the exact infimum.

## Task5. New finite-certificate lower bound from the stronger forcing branch

This is a small but rigorous increment on the finite-atom lower-bound side.  It is **not** the final Tao finite-gap route and it does not approach the conjectural value \(1.8344304757\ldots\).  Its purpose is to record a concrete certificate produced by combining a stronger forcing interval with the existing five-atom tail block.

### Statement

Assuming the standard Tao/natso reduction
\[
\mu(\{-1\})\ge \frac12,\qquad \operatorname{supp}\mu\subseteq \{-1\}\cup[0,1],
\]
one obtains
\[
|\{U_\mu>0\}|\ge 1.806304.
\]
Hence, under the same reduction,
\[
L_-\ge 1.806304.
\]

### Certificate structure

1. The stronger forcing branch is certified on
\[
a\in[-1.708,-\sqrt2],\qquad b\in[0,1.836+a]
\]
for the three-atom family
\[
\nu_{a,b}=\delta_a+(1.395-b)\delta_b+C(a,b)\delta_{1.071-b},
\]
where \(C(a,b)>0\) is chosen by \(U_{\nu_{a,b}}(-1)=10^{-4}\).

The interval-box verifier gives:

```text
PASS
certified_boxes 5955
split_boxes 5954
worst_lower_bound 0.0000027692109390833507690739
max_depth 35
```

Thus if \(|E_\mu|<1.836\), the component containing \((-\sqrt2,0)\) must in fact contain \((-1.708,0)\).  Since \(1.806304<1.836\), this forcing step applies to the target bound below.

2. For the tail block take, for \(a\in[-1.806304,-1.708]\),
\[
\lambda_a=
\delta_a
+1.174168821\,\delta_{a+1.80650001}
+0.025921118\,\delta_{a+2.57053197}
+0.118647936\,\delta_{a+2.68367709}
+0.180553554\,\delta_{a+2.79017717}.
\]

Writing \(y=x-a\), the required positivity is
\[
V(y)>0\qquad(0.708\le y\le2.806304),
\]
where
\[
\begin{aligned}
V(y)={}&\log\frac1{|y|}
+1.174168821\log\frac1{|y-1.80650001|}
+0.025921118\log\frac1{|y-2.57053197|}\\
&+0.118647936\log\frac1{|y-2.68367709|}
+0.180553554\log\frac1{|y-2.79017717|}.
\end{aligned}
\]

The derivative numerator has degree 4.  Sturm/root-count verification gives exactly four critical points in the domain, one in each of the following brackets:

```text
[0.77003805, 0.77003806]
[2.52642600, 2.52642601]
[2.60759965, 2.60759966]
[2.74249871, 2.74249872]
```

Decimal interval lower bounds at endpoints and critical brackets are:

```text
V(0.708)        > 0.001
V(r1 bracket)   > 0.000005
V(r2 bracket)   > 0.000005
V(r3 bracket)   > 0.000005
V(r4 bracket)   > 0.000005
V(2.806304)     > 0.000003
```

The actual conservative lower bound at the high endpoint is approximately
\(4.054663365147\times10^{-6}\).  This is why the certificate is only recorded at \(M=1.806304\); the same fixed tail block fails at \(M=1.806305\).

3. The swept intervals from \(a\in[-1.806304,-1.708]\) are disjoint and avoid \((-1.708,0)\):
\[
[-1.806304,-1.708],
\]
\[
[0.00019601,0.09850001],
\]
\[
[0.76422797,0.86253197],
\]
\[
[0.87737309,0.97567709],
\]
\[
[0.98387317,1.08217717].
\]
By the duality identity, for every \(a\) in the moving interval at least one of these five atom locations lies in \(E_\mu\).  Therefore outside \((-1.708,0)\) the set \(E_\mu\) has measure at least
\[
1.806304-1.708=0.098304.
\]
Combining with \((-1.708,0)\subset E_\mu\) gives
\[
|E_\mu|\ge 1.708+0.098304=1.806304.
\]

### Audit note

This is a genuine lower-bound certificate, but it is a small finite-atom improvement only.  Searches at \(M=1.807,1.808,1.810,1.815\) with five to seven shifted atoms did not produce a positive tail certificate.  The current bottleneck is the tail block, not the stronger forcing branch.

### Task5 formalization update: Mathlib layer

A local Lake/Mathlib setup has been added at the workspace root using the same toolchain as the Frankl project:

```text
leanprover/lean4:v4.30.0-rc2
mathlib rev v4.30.0-rc2
```

New files:

```text
lakefile.toml
lake-manifest.json
1038/FiveAtom1806304Formal.lean
1038/FiveAtom1806304Mathlib.lean
```

Validated commands:

```bash
lake exe cache get
cd .lake/packages/proofwidgets && lake build
lake env lean 1038/FiveAtom1806304Formal.lean
lake env lean 1038/FiveAtom1806304Mathlib.lean
```

`FiveAtom1806304Formal.lean` is the exact-arithmetic kernel certificate for:

- quartic critical-bracket signs for the five-atom derivative numerator;
- swept-interval disjointness;
- length arithmetic `1.708 + 0.098304 = 1.806304`;
- compatibility with the stronger forcing threshold `1.806304 < 1.836`.

`FiveAtom1806304Mathlib.lean` imports Mathlib and defines the actual real-log one-variable potential

\[
V(y)=\log |y|^{-1}
+1.174168821\log |y-1.80650001|^{-1}
+0.025921118\log |y-2.57053197|^{-1}
+0.118647936\log |y-2.68367709|^{-1}
+0.180553554\log |y-2.79017717|^{-1}.
\]

It proves, without Float and without `sorry`, the Mathlib tail-layer facts that follow once the exact log positivity theorem

\[
\forall y\in[0.708,2.806304],\quad V(y)>0
\]

is supplied.  The remaining formal gap is precisely this `Real.log` interval-positivity theorem.  The current Decimal checker verifies it externally with minimum endpoint margin about

\[
4.054663365147\times10^{-6}.
\]

This should be described publicly as:

> Mathlib formalization of the exact arithmetic and sweep layer is complete; the `Real.log` interval inequality is still certified by an external Decimal interval checker, not yet by a fully internal Mathlib proof.

It should **not** be described as a full Lean proof of \(L_-\ge1.806304\) until the `Real.log` interval bounds and the Tao/natso analytic reduction are also internalized.

#### Internalized `Real.log` endpoint check

The Mathlib layer now also proves the weakest endpoint check internally:

```lean
theorem V_yHi_positive_internal : 0 < V yHi
```

This theorem proves \(V(2.806304)>0\) using Mathlib's atanh-series log bounds:

```lean
Real.sum_range_le_log_div
Real.log_div_le_sum_range_add
```

No Float, no external Decimal arithmetic, and no `sorry` are used for this endpoint theorem.  The proof uses rational Taylor bounds with:

```text
negative log term: upper bound with n = 30
positive log terms: lower bounds with n = 150
```

The remaining internal Mathlib work is to repeat this for the four critical brackets and the lower endpoint, then connect it to a formal monotonicity/root-count argument for the quartic derivative numerator.

#### Internalized all six five-atom log checks

The five-atom one-variable numerical checks have now been internalized in Mathlib.  The file

```text
1038/FiveAtom1806304Mathlib.lean
```

contains the theorem

```lean
theorem all_five_atom_log_checks_internal :
    0 < V yLo ∧
    (∀ y : ℝ, y ∈ Icc (q 77003805 100000000) (q 77003806 100000000) → 0 < V y) ∧
    (∀ y : ℝ, y ∈ Icc (q 252642600 100000000) (q 252642601 100000000) → 0 < V y) ∧
    (∀ y : ℝ, y ∈ Icc (q 260759965 100000000) (q 260759966 100000000) → 0 < V y) ∧
    (∀ y : ℝ, y ∈ Icc (q 274249871 100000000) (q 274249872 100000000) → 0 < V y) ∧
    0 < V yHi
```

This covers:

```text
V(0.708) > 0
V([0.77003805,0.77003806]) > 0
V([2.52642600,2.52642601]) > 0
V([2.60759965,2.60759966]) > 0
V([2.74249871,2.74249872]) > 0
V(2.806304) > 0
```

The proof uses only Mathlib real logarithms and rational Taylor/atanh bounds via:

```lean
Real.sum_range_le_log_div
Real.log_div_le_sum_range_add
```

No Float and no `sorry` are used in these checks.

Validated command:

```bash
lake env lean 1038/FiveAtom1806304Mathlib.lean && lake env lean 1038/FiveAtom1806304Formal.lean
```

Remaining non-internalized parts of the full problem are not numeric-log issues anymore; they are the analytic bridge from these finite checks to global 1038: derivative/root-count monotonicity over the full one-variable domain, the two-parameter forcing branch in Lean, the duality lemma, and the Tao/natso minimizer reduction.

## 16. Bridge ledger for the \(1.83\) / exact-value route

This section is the current control ledger for connecting the two-interval
finite-gap branch to a \(1.83\) lower-bound theorem, and eventually to the
candidate exact value
\[
M_* = 1.8344304757626617\ldots
\]
It is deliberately written as a gap ledger: no line below should be read as a
claim that \(L_-\ge1.83\) is already proved.

### 16.1 Target theorem shape

The desired lower-bound theorem has the following conditional structure:

> Under the Tao/natso minimizer reduction to
> \(S=\{-1\}\cup[0,1]\), every candidate minimizer with
> \(|E_\mu|<M\), for \(M\) near \(1.83\) and ultimately \(M_*\), admits a
> nonnegative dual certificate \(\nu\) supported in \(E_\mu^c\) such that
> \(U_\nu\ge0\) on \(S\).  Therefore the duality lemma in §3 rules out such a
> minimizer.

The matching exact-value theorem would then add an upper construction:

> There is an admissible sequence of monic real-root polynomials, or an
> approximable limiting measure, with
> \(|E|\to M_*\).

Thus the exact theorem needs both:

1. lower side: global dual exclusion up to \(M_*\);
2. upper side: a construction attaining \(M_*\).

The current repository has not closed either global endpoint.  It has closed
one important local lower-side branch certificate.

### 16.2 Artifact status table

| Object | Current status | Files / commands | What it proves |
|---|---|---|---|
| Conditional finite-atom lower bound \(1.806304\) | strongest closed local lower-bound package | `FiveAtom1806304Mathlib.lean`, `FiveAtom1806304Formal.lean`, five-atom Decimal/Lean checks | A separate finite-atom lower-bound route; useful but not close to \(1.83\). |
| Two-interval sign regime | proof-grade for exported boxes as an external verifier | `.venv/bin/python 1038/verify_two_interval_sign_box.py --quiet --self-test-tamper` | Checks \(1<A<-\ell\), \(\ell<-1<r<\alpha<\beta<1\), atom residue signs, and density sign on exported branch/Krawczyk boxes. |
| Two-interval branch on \([0.00005,0.002]\) | proof-grade interval winding certificate for all stored slabs | `verify_two_interval_continuation_tube.py` with `residue-log-mv`; remote split runs `1024/1024 PASS` on \([0.0002,0.0005]\) and `2688/2688 PASS` on the remaining slabs | For each certified eta slice, \(K(B,\tau,\eta)\) has a zero in the tube by winding degree \(1\). |
| Two-interval small-\(\eta\) branch on \([0.00001,0.00005]\) | proof-grade interval winding certificate for the generated small-\(\eta\) slabs | `two_interval_small_eta_certificate.json`; remote split run `448/448 PASS` with `--max-weighted-defect 100` | Extends the local branch and positivity certificate down to \(\varepsilon=10^{-5}\). |
| Two-interval tiny-\(\eta\) branch on \([0.00000001,0.00001]\) | proof-grade interval winding certificate with DK diagnostic skipped | `two_interval_tiny_eta_certificate.json`; remote split run `5120/5120 PASS` with `--skip-weighted-defect` | Extends the local branch and positivity certificate down to \(\varepsilon=10^{-8}\). |
| Global positivity on \(S\) for the stored two-interval branch | closed by sign-chart verifier, conditional on the winding zero in each tube | `.venv/bin/python 1038/verify_two_interval_global_positivity.py --self-test-tamper`; local and remote PASS | Uses \(U'=-F\), the checked sign chart, \(U(-1)=U(\alpha)=0\), and flatness on \([\alpha,\beta]\) to prove \(U_\lambda\ge0\) on \(\{-1\}\cup[0,1]\). |
| Singular range \(0<\varepsilon<0.00000001\) | open | limiting winding target and diagnostic remainder script | Needs an asymptotic/small-\(\eta\) theorem, not finite row sampling. |
| Direct interval lower-bound audit of \(U_\lambda\) | optional independent artifact | none yet | Would evaluate endpoint/stationary-point lower bounds directly; the stored branch currently uses the sign-chart proof instead. |
| Global reduction from arbitrary \(E\) | open | only recorded as a required Tao/natso/global lemma | Must show any relevant candidate set reduces to one/two-interval obstruction or receives another dual certificate. |
| Upper construction at \(M_*\) | open in this repo | Tao one-cut candidate endpoints recorded, but no full construction proof | Needs an admissible approximating polynomial/measure sequence with \(|E|\to M_*\). |

### 16.3 Epsilon coverage status

The original stored proof-grade branch-existence certificate covers
\[
\varepsilon\in[0.00005,0.002],
\]
split across the endpoint rows in
`1038/two_interval_branch_certificate_top_split.json`.
Together with the generated small-\(\eta\) and tiny-\(\eta\) certificates in §15.6, the certified
finite branch range is now
\[
\varepsilon\in[0.00000001,0.002].
\]

The proof-grade winding settings are:

```text
0.00005:0.0001   radius=0.0003   eta subdivisions=224    PASS 224/224
0.0001:0.0002    radius=0.0003   eta subdivisions=224    PASS 224/224
0.0002:0.0005    radius=0.00029  eta subdivisions=1024   PASS 1024/1024
0.0005:0.001     radius=0.0006   eta subdivisions=1344   PASS 1344/1344
0.001:0.00125    radius=0.0002   eta subdivisions=224    PASS 224/224
0.00125:0.0015   radius=0.0002   eta subdivisions=224    PASS 224/224
0.0015:0.00175   radius=0.0002   eta subdivisions=224    PASS 224/224
0.00175:0.002    radius=0.0002   eta subdivisions=224    PASS 224/224
```

The command shape for each slab is:

```bash
.venv/bin/python 1038/verify_two_interval_continuation_tube.py \
  1038/two_interval_branch_certificate_top_split.json \
  --config EPS_LOW:EPS_HIGH:R,R:16,1 \
  --eta-interval-dk-kernel residue-log \
  --interval-boundary-value-kernel residue-log-mv \
  --interval-boundary-winding ETA,8 \
  --interval-boundary-winding-adaptive-depth 2 \
  --max-weighted-defect 10
```

For expensive full runs, split with:

```text
--interval-boundary-winding-eta-slice i:i+1
```

and run the slices on `hkgai-studio` with up to 20 workers.

The finite range still will not cover \(0<\varepsilon<0.00000001\).  That range
requires the separate small-\(\eta\) theorem:

\[
K_\eta(B,\tau)=K_0(B,\tau)+O(\eta|\log\eta|)
\]
or the stronger Lyapunov-Schmidt expansion already outlined in §15.6, with
interval remainders strong enough to keep the winding degree stable near the
limiting branch.

### 16.4 Positivity/support gap

The sign-box verifier already checks the algebraic sign regime on exported
boxes:

```bash
.venv/bin/python 1038/verify_two_interval_sign_box.py --quiet --self-test-tamper
```

This gives positivity of the extracted measure, provided the branch root lies
inside those boxes.  In the sign chart of §15.1, this reduces measure
positivity to:

\[
1<A<-\ell,\qquad \ell<-1<r<\alpha<\beta<1.
\]

What remains is different: global potential positivity.  The target theorem is:

\[
U_{\lambda^{(\varepsilon)}}(x)\ge0
\quad\text{for every }x\in S=\{-1\}\cup[0,1].
\]

The sign chart reduces much of this check, but a proof artifact still has to
record interval lower bounds on each required real component.  A useful next
verifier should:

1. use the residue-log value primitive rather than singular quadrature;
2. isolate all real roots of \(U'_\lambda=-F\) on each component of
   \(S\setminus[\alpha,\beta]\);
3. evaluate \(U_\lambda\) at endpoints and isolated critical brackets;
4. prove the endpoint/contact equalities \(U(\alpha)=0\) and \(U(-1)\ge0\), or
   \(U(-1)=0\) on the sharp branch;
5. export a finite certificate with all interval lower bounds.

This is the next mathematical kernel after extending the winding certificate.

### 16.5 Global candidate-set gap

Even a complete two-interval branch theorem would still not prove
\(L_-\ge1.83\) by itself.  The global theorem must also say why every relevant
candidate set \(E\) with \(|E|<1.83\), or eventually \(|E|<M_*\), is covered by
one of the certified obstruction mechanisms.

At present the required global lemma is still only a target:

> Every normalized minimizing candidate below \(M\) either reduces to the
> one-interval obstruction, reduces to the two-interval obstruction
> \(E_\varepsilon=(x_L+\varepsilon,x_R)\cup(1-\varepsilon,1)\), or admits a
> finite-gap dual certificate of the same square-root rational type.

This is the actual Tao-level gap.  It is not a coding problem alone.  The likely
route is a finite-gap theorem for finite unions of intervals: for a candidate
finite union \(E\), construct a Cauchy transform with rational square-root
structure, certify measure positivity, and prove \(U_\nu\ge0\) on \(S\).

The current two-interval verifier is therefore best viewed as the first
certified instance of that finite-gap program.

### 16.6 Upper-side gap

The number
\[
M_* = x_R-x_L
=0.02632310766384517-(-1.8081073680988165)
=1.8344304757626617\ldots
\]
comes from the one-cut candidate in Tao's notes.  The lower-side dual
certificate program cannot by itself prove exactness.  The upper side needs an
admissible construction:

1. define the candidate limiting measure or polynomial sequence;
2. prove it is approximable by monic real-root polynomials in the original
   problem class;
3. prove the associated set has length tending to \(M_*\).

Until this upper construction is written, the current route can at most support
lower-bound statements such as \(L_-\ge1.83\), not the exact equality
\(L_-=M_*\).

### 16.7 Current priority order

The next work should be done in this order:

1. **Prove the small-\(\eta\) branch theorem** for
   \(0<\varepsilon<0.00000001\).
2. **Formulate the global finite-gap reduction lemma** precisely enough that it
   can be attacked or refuted.
3. **Separate the upper construction** into its own proof note, so the lower
   and upper sides do not get conflated.
4. **Optionally add a direct interval lower-bound audit** of \(U_\lambda\) as an
   independent check of the sign-chart proof.

The previous first items, extending proof-grade winding coverage and then
closing global positivity on \(S\) for the stored branch, are now closed.  The
new first item is the small-\(\eta\) theorem.  The finite-gap reduction item is
the hardest mathematical gap.
