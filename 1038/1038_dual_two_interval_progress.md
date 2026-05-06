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

This is still sampled stress evidence, not an interval Krawczyk proof.  The
next proof-grade replacement is to export outward-rounded interval enclosures
for the same \(K\), \(D_{(B,\tau)}K\), sign chart, residues, and density signs
instead of relying on floating samples.

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

### 15.7 Eta-divided Taylor model for the singular DK entry

The current interval obstruction in the small-\(\eta\) branch is the
\((K_2,\tau)\) derivative entry.  The bad enclosure comes from forming

\[
\frac{f(\eta)-f(0)}{\eta}
\]

by evaluating \(f(\eta)\) and \(f(0)\) as two unrelated interval balls.  This
destroys the first-order cancellation.  The proof-grade replacement is the
integral Taylor identity

\[
\boxed{
\frac{f(\eta)-f(0)}{\eta}
=
\int_0^1 f'(t\eta)\,dt.
}
\]

For a paired residue-log contribution of the form

\[
f(\eta)=S(\eta)\log|x-\rho(\eta)|,
\]

where \(S\) is the paired residue sum and \(\rho\) is the paired pole location,
the divided term should be enclosed as

\[
\boxed{
\int_0^1
\left[
S'(s)\log|x-\rho(s)|
-S(s)\frac{\rho'(s)}{x-\rho(s)}
\right]_{s=t\eta}
dt.
}
\]

This keeps \(S,\rho,\log|x-\rho|\) on the same \(s=t\eta\) dependency track and
should remove the artificial radius seen in
\(((a_\ell+a_r)-(a_{\ell0}+a_{r0}))/\eta\).

Thus the small-\(\eta\) singular gap has a precise next theorem:

\[
\boxed{
\text{For each paired residue-log term, derive rational formulas for }
S'(s)\text{ and }\rho'(s),\text{ and enclose the above }t\text{-integral on
the first eta slab.}
}
\]

If this theorem is established, the \(DK[1,1]\) enclosure should contract
toward the true value near \(-0.43\) instead of the current artificial
\([-1.74,1.74]\)-scale interval.  This is the most direct route to a
continuum-grade small-\(\eta\) branch certificate.

The first diagnostic after this reformulation separates numerical evidence
from proof-grade interval evidence.  At the smallest row,

```text
diagnose_k2_tau_derivative.py --grid 5 --eta-values 5e-5 --h 1e-4

worst_derivative = 3.153712e-05
worst_curvature  = 7.783704e-05
PASS-DIAGNOSTIC
```

so the sampled Taylor mechanism is small.  But the direct interval curvature
box remains unusable:

```text
--interval-curvature-box-test --interval-subboxes 2
worst_bound = 1.556219e+10
FAIL-DIAGNOSTIC
```

and the eta-uniform secant wrapper on \([5\cdot10^{-5},10^{-4}]\) is still far
too wide:

```text
--grid 9 --eta-values 5e-5,1e-4 --secant-certificate
worst_secant_bound = 3.530171e-02
candidate_lipschitz = 2.000000e-04
FAIL-DIAGNOSTIC
```

This confirms the diagnosis.  The small-\(\eta\) singular gap is not a sampled
failure; it is an interval-dependency failure.  The proof-grade closure must
differentiate the paired residue-log terms analytically on the shared
\(s=t\eta\) variable, rather than relying on finite-difference or secant
enclosures.

The same conclusion appears from the regularized joint-limit-layer branch.  At
a first-slab point,

```text
eta=sqrt(5e-5), B=0.01, tau=1.103891261372
limit_layer_joint_identity:combined_limit ≈ -6.872077647e-9
limit_layer_joint_regularized_second:combined
  = -0.03365209117925416539...  with radius about 8e-53
```

The contact and minus-one constants cancel to about \(7\cdot10^{-9}\), and the
regularized second term is sharply enclosed.  But on the first eta slab the
same code gives

```text
eta in [sqrt(5e-5),sqrt(1e-4)]
limit_layer_joint_regularized_second:combined = [+/- 39.1]
```

So the analytic identity is good at points, but the whole-slab `Div2` interval
model is still too coarse.  The next closure attempt must use a true
\(s=t\eta\) derivative enclosure for the regularized joint layer, not a
whole-slab second-divided algebra with repeated eta dependencies.

## 16. Mathematical proof ledger for the exact-value route

This section records the current paper-level proof chain for the conjectural
exact value

\[
M_* = x_R-x_L = 1.8344304757626617\ldots,
\]

where

\[
x_L=-1.8081073680988165,\qquad x_R=0.02632310766384517.
\]

The purpose of this section is to separate the mathematics from the later
certificate/implementation work.  It is not a claim that the exact value is
already proved.  It states which parts of the proof chain are now reduced to
standard finite-gap arguments and which part remains the hard global gap.

### 16.1 Upper-bound construction

The one-cut primal candidate has the form

\[
\mu_a=A(a)\delta_{-1}+f_a(x)\mathbf 1_{[a,1]}(x)\,dx,
\]

with

\[
f_a(x)=
\frac{x+1-A(a)\sqrt{2(1+a)}}
{\pi(x+1)\sqrt{(1-x)(x-a)}}
\]

and

\[
A(a)=
\frac{\log \frac4{1-a}}
{\log\frac{3+a+2\sqrt{2(1+a)}}{1-a}}.
\]

For this measure, the finite Hilbert-transform calculation gives

\[
U_{\mu_a}(x)=0\qquad (a\le x\le1).
\]

At the parameter

\[
a_*=0.804461769730796\ldots,
\]

the exterior potential has two additional zeros

\[
U_{\mu_{a_*}}(x_L)=0,\qquad U_{\mu_{a_*}}(x_R)=0.
\]

The sign pattern of the one-cut potential is

\[
U_{\mu_{a_*}}>0\quad\text{on }(x_L,x_R),
\qquad
U_{\mu_{a_*}}\le0\quad\text{off }(x_L,x_R),
\]

so

\[
E_{\mu_{a_*}}=(x_L,x_R)
\]

and therefore

\[
\boxed{L_-\le M_*.}
\]

The remaining work in this upper-bound block is not conceptual: one should
write \(a_*\) as the unique solution of the two exterior-contact equations, or
equivalently give a short interval enclosure for \(a_*,x_L,x_R\).  This is an
upper construction, not the hard part of the exact-value proof.

### 16.2 First-variation lower-bound mechanism

For the lower bound, assume for contradiction that a regular minimising
candidate satisfies

\[
|E_\mu|<M_*.
\]

Using the standard normalization and collapse inputs, one may work under

\[
\operatorname{supp}\mu\subset\{-1\}\cup[0,1],
\qquad
(-1,0)\subset E_\mu,
\]

and every connected component of \(E_\mu\) contains exactly one atom of
\(\mu\).

The regular first-variation argument produces a nonzero positive dual measure
\(\lambda\) supported on \(\partial E_\mu\cup Z_0\), where

\[
Z_0=\{U_\mu=0\}\setminus\partial E_\mu,
\]

such that

\[
U_\lambda\ge0\quad\text{on }[-1,1]
\]

and, on any continuous active support of \(\mu\),

\[
U_\lambda=0.
\]

Thus a full lower-bound proof can be phrased as a global dual-covering theorem:

\[
\boxed{
|E_\mu|<M_* \Longrightarrow
\exists\,\lambda\ge0,\ 
\operatorname{supp}\lambda\subset E_\mu^c,\ 
U_\lambda\ge0\text{ on }[-1,1],
}
\]

with the usual mutual-energy contradiction against minimality.  This is the
precise mathematical target for the exact route.

### 16.3 Local one-cut/two-interval finite-gap reduction

Suppose the active zero set of the dual problem has one interval

\[
Z_0=[\alpha,\beta],
\]

and the boundary atoms of the dual measure are at

\[
\ell,\ r,\ 1,
\qquad
\ell<-1<r<\alpha<\beta<1.
\]

Write

\[
F(z)=\int\frac{d\lambda(t)}{z-t}.
\]

Because \(U_\lambda=0\) on \([\alpha,\beta]\), one has

\[
\operatorname{Re}F_+(x)=0\qquad(\alpha<x<\beta).
\]

With

\[
R(z)=\sqrt{(z-\alpha)(z-\beta)},\qquad R(z)\sim z,
\]

the quotient \(F(z)/R(z)\) has no jump across the cut.  Its only possible
poles are at \(\ell,r,1\), so it must have the finite-gap form

\[
F(z)=
\frac{z+A}{(z-\ell)(z-r)(z-1)}
\sqrt{(z-\alpha)(z-\beta)}.
\]

The extracted measure is

\[
\lambda=m_\ell\delta_\ell+m_r\delta_r+m_1\delta_1
+g(x)\mathbf1_{[\alpha,\beta]}(x)\,dx,
\]

where

\[
m_\ell=
\frac{(\ell+A)R(\ell)}{(\ell-r)(\ell-1)},\quad
m_r=
\frac{(r+A)R(r)}{(r-\ell)(r-1)},\quad
m_1=
\frac{(1+A)R(1)}{(1-\ell)(1-r)}
\]

and

\[
g(x)=
-\frac1\pi
\frac{x+A}{(x-\ell)(x-r)(x-1)}
\sqrt{(x-\alpha)(\beta-x)}.
\]

Under

\[
1<A<-\ell,
\qquad
\ell<-1<r<\alpha<\beta<1,
\]

all three atoms and the density are positive.  The real-axis sign chart then
shows that the global condition \(U_\lambda\ge0\) on \([-1,1]\) reduces to the
two contact equations

\[
U_\lambda(\alpha)=0,\qquad U_\lambda(-1)=0.
\]

This proves the local structural statement:

\[
\boxed{
\text{Any regular one-cut/two-interval extremal dual is exactly the corrected
endpoint-atom finite-gap ansatz of §15.}
}
\]

For the boundary family

\[
E_\varepsilon=(x_L+\varepsilon,x_R)\cup(1-\varepsilon,1),
\]

this gives

\[
\ell=x_L+\varepsilon,\qquad r=x_R,\qquad \beta=1-\varepsilon,
\]

which is the branch generated by the current solver.

### 16.4 Remaining hard lemma: interlacing collapse

The proof is not yet complete because a general regular minimizer might have
more than the one active zero interval described above.  The remaining global
gap is now the following finite-gap topology statement.

**Interlacing-collapse lemma.**  Let \(F\) be a positive Stieltjes finite-gap
transform arising from a regular minimising counterexample with
\(|E_\mu|<M_*\).  If \(E_\mu\) has more than the main positive component and
the endpoint split-off component, then either:

1. one of the residues or continuous densities of the associated dual measure
   is negative; or
2. a gap-pinching/Schiffer variation decreases \(|E_\mu|\), contradicting
   minimality; or
3. the configuration degenerates to the two-interval boundary family
   \(E_\varepsilon\).

The reason this is the right remaining lemma is the strict Stieltjes
monotonicity

\[
F'(x)=-\int\frac{d\lambda(t)}{(x-t)^2}<0
\]

on every real component disjoint from \(\operatorname{supp}\lambda\).  Hence
each extra positive component of \(E_\mu\) can contain only one zero of \(F\),
and that zero is forced to interlace with the boundary poles and cut endpoints.
The expected contradiction is that the resulting pole/cut/zero interlacing
cannot remain positive under \(|E_\mu|<M_*\), except in the degenerate
two-interval branch already described in §15.

Thus the current exact-value status is:

\[
\boxed{
L_-\le M_* \text{ is supplied by the one-cut upper construction;}
}
\]

\[
\boxed{
\text{the local dangerous lower-bound branch is the corrected two-interval
finite-gap ansatz;}
}
\]

\[
\boxed{
\text{the missing mathematical step is the interlacing-collapse/global
topology lemma.}
}
\]

Only after this last lemma is proved can the statement

\[
L_-=1.8344304757626617\ldots
\]

be claimed as a complete proof.

### 16.5 Direct normalized lower-bound attack: extra-component stationarity

After accepting the standard reduction as already supplied by the separate
normalization notes, the exact lower-bound target is the normalized theorem

\[
\operatorname{supp}\mu\subset\{-1\}\cup[0,1],\qquad
\mu(\{-1\})\ge\frac12
\quad\Longrightarrow\quad
|E_\mu|\ge M_*.
\]

The first direct attack is to assume a normalized counterexample with
\(|E_\mu|<M_*\), choose a regular length-minimising one, and inspect any extra
positive component

\[
I=(u,v)\subset(0,1)
\]

away from the main component containing \(-1\).  By the collapse lemma the
restriction of \(\mu\) to \(I\) is a single atom,

\[
\mu|_I=q\delta_c,\qquad c\in(u,v),\quad q>0.
\]

Write locally

\[
U_\mu(x)=q\log\frac1{|x-c|}+W(x),
\]

where \(W\) is smooth near \([u,v]\).  Since

\[
U_\mu(u)=U_\mu(v)=0,\qquad
U_\mu'(u)>0,\qquad U_\mu'(v)<0,
\]

moving the atom by \(c\mapsto c+s\) gives the first variation

\[
\dot U(x)=\frac{q}{x-c}.
\]

The endpoint variations are therefore

\[
\dot u=-\frac{q}{(u-c)U_\mu'(u)},\qquad
\dot v=-\frac{q}{(v-c)U_\mu'(v)}.
\]

Thus

\[
\frac{d}{ds}(v-u)
=
-\frac{q}{(v-c)U_\mu'(v)}
+\frac{q}{(u-c)U_\mu'(u)}.
\]

For a length-minimising normalized counterexample, this derivative must vanish.
Hence every extra positive component must satisfy the stationarity condition

\[
\boxed{
(c-u)U_\mu'(u)=(v-c)|U_\mu'(v)|.
}
\]

This calculation is useful because it shows why a purely qualitative
interlacing argument is insufficient: an extra component is not immediately
contradictory; it is allowed only at a rigid balanced position.

On the dual side, first-variation complementarity gives

\[
U_\lambda(c)=0.
\]

For

\[
F(z)=\int\frac{d\lambda(t)}{z-t},
\]

this implies

\[
F(c)=0,\qquad
F'(c)=-\int\frac{d\lambda(t)}{(c-t)^2}<0.
\]

Thus every extra positive component forces one simple real zero of the dual
Cauchy transform inside the component.  If the active zero set has \(g\)
intervals, the finite-gap form is

\[
F(z)=
\frac{P(z)}{Q(z)}
\sqrt{\prod_{k=1}^g(z-\alpha_k)(z-\beta_k)}.
\]

The extra components give real zeros of \(P\), while the boundary atoms give
the poles of \(Q\).  Positivity of residues and cut densities imposes the
pole/cut/zero interlacing.  The normalized lower bound is therefore reduced to
the following quantitative statement.

**Quantitative finite-gap inequality.**  Any positive Stieltjes finite-gap
solution with \(g\ge2\), satisfying the above atom-balance equations,
complementarity zeros, residue positivity, density positivity, and real
interlacing, has

\[
|E|\ge M_*.
\]

Equivalently, the only way for a finite-gap extremal to approach length
\(M_*\) from the normalized lower-bound side is to degenerate to the one-cut
upper construction or to the corrected two-interval boundary branch.

This is now the smallest mathematical hard mouth for the normalized exact
lower bound.  The remaining proof should no longer be phrased as a vague
"global topology" issue; it should be attacked as a quantitative inequality
for positive finite-gap Stieltjes transforms.

### 16.6 First high-genus target: the \(g=2\) inequality

The finite-gap inequality should not be attacked for all \(g\ge2\) at once.
The first closed target is the first possible escape from the two-interval
branch, namely \(g=2\).

Write the active zero set as

\[
Z_0=[\alpha_1,\beta_1]\cup[\alpha_2,\beta_2],
\qquad
\alpha_1<\beta_1<\alpha_2<\beta_2,
\]

and write the associated Stieltjes transform in finite-gap form

\[
F(z)=
\frac{P(z)}{Q(z)}
\sqrt{(z-\alpha_1)(z-\beta_1)(z-\alpha_2)(z-\beta_2)}.
\]

If a normalized counterexample has a first extra positive component

\[
I=(u,v)\subset(0,1),\qquad \mu|_I=q\delta_c,
\quad u<c<v,
\]

then the primal stationarity condition is

\[
(c-u)U_\mu'(u)=(v-c)|U_\mu'(v)|.
\]

The dual complementarity condition at the same atom is

\[
F(c)=0,\qquad F'(c)<0.
\]

Thus \(P\) must have a simple real zero at each extra positive component atom,
with the zero interlacing the poles/cuts in a way compatible with positive
residues and positive density.  The concrete \(g=2\) proof obligation is

\[
\boxed{
|E|=(R_0-L_0)+(v-u)\ge M_*.
}
\]

A sharp failure would have to satisfy all of the following equations at once:
the endpoint zero equations for \(U_\mu\), the atom stationarity equation, the
dual zero \(F(c)=0\), positive residues, positive cut density, and
\(|E|<M_*\).  The next mathematical step is therefore to show that this rigid
system either degenerates to the already-known \(g=1\) two-interval branch or
violates positivity.

### 16.7 Singular-mass cancellation inside an extra component

The useful local simplification is that the singular atom mass cancels out of
the first-variation balance.

On an extra component \(I=(u,v)\) with atom \(q\delta_c\), write

\[
U_\mu(x)=q\log\frac1{|x-c|}+W(x),
\]

where \(W\) is the external field generated by all other mass.  Then

\[
U_\mu'(u)=\frac{q}{c-u}+W'(u),
\qquad
U_\mu'(v)=-\frac{q}{v-c}+W'(v).
\]

Substituting into

\[
(c-u)U_\mu'(u)=-(v-c)U_\mu'(v)
\]

gives the exact cancellation

\[
\boxed{
(c-u)W'(u)+(v-c)W'(v)=0.
}
\]

The endpoint equations \(U_\mu(u)=U_\mu(v)=0\) also give

\[
W(u)=q\log(c-u),\qquad
W(v)=q\log(v-c),
\]

hence

\[
\boxed{
W(v)-W(u)=q\log\frac{v-c}{c-u}.
}
\]

Because \(W\) is a logarithmic potential generated by mass outside \(I\),

\[
W''(x)=\int_{\mathbb R\setminus I}\frac{d\mu(t)}{(x-t)^2}>0
\qquad (x\in I).
\]

Thus \(W'\) is strictly increasing on \(I\), and the balance equation forces

\[
W'(u)<0<W'(v).
\]

This converts the first \(g=2\) obstruction into a convex external-field
problem: an escaping component can exist only if the outside field has a
unique minimum inside \(I\) and the endpoint distances \(c-u\), \(v-c\) satisfy
both the logarithmic endpoint equation and the weighted endpoint-slope
equation.  The next proof move is to combine this convexity with the
finite-gap sign/interlacing constraints on \(F\), eliminating the polynomial
factor \(P\) through \(F(c)=0\).

### 16.8 Rational moment form of the escaping-component balance

The cancellation lemma has an equivalent integral form that is more useful
for the normalized lower bound because it sees the fixed mass at \(-1\).

Let

\[
a=c-u,\qquad b=v-c,\qquad a,b>0.
\]

Since

\[
W'(x)=-\int_{\mathbb R\setminus I}\frac{d\mu(t)}{x-t},
\]

the balanced-slope identity

\[
aW'(u)+bW'(v)=0
\]

becomes

\[
\int_{\mathbb R\setminus I}
\left(\frac{a}{u-t}+\frac{b}{v-t}\right)d\mu(t)=0.
\]

But

\[
\frac{a}{u-t}+\frac{b}{v-t}
=
\frac{a(v-t)+b(u-t)}{(u-t)(v-t)}
=
\frac{(v-u)(c-t)}{(u-t)(v-t)}.
\]

Therefore every escaping component must satisfy

\[
\boxed{
\int_{\mathbb R\setminus I}
\frac{c-t}{(u-t)(v-t)}\,d\mu(t)=0.
}
\]

Since \(t\notin(u,v)\), the denominator is positive.  Hence the identity says
exactly that the left-side mass and the right-side mass balance:

\[
\boxed{
\int_{t<u}
\frac{c-t}{(u-t)(v-t)}\,d\mu(t)
=
\int_{t>v}
\frac{t-c}{(u-t)(v-t)}\,d\mu(t).
}
\]

The endpoint zero equations give the companion logarithmic identity

\[
\boxed{
\int_{\mathbb R\setminus I}
\log\frac{|u-t|}{|v-t|}\,d\mu(t)
=
q\log\frac{v-c}{c-u}.
}
\]

The normalized mass condition contributes the explicit left-side term

\[
\mu(\{-1\})\frac{c+1}{(u+1)(v+1)}
\ge
\frac12\frac{c+1}{(u+1)(v+1)}
\]

to the rational balance.  Thus an extra component can persist only if enough
mass to the right of \(v\) compensates this forced contribution.  This is the
first point where the standard reduction data directly enters the \(g=2\)
finite-gap exclusion.

The next lower-bound lemma should be formulated as follows:

\[
\boxed{
\text{under } |E|<M_*,\text{ the right-side compensation required by the
rational balance contradicts either the logarithmic identity or positivity of
the finite-gap dual density.}
}
\]

### 16.9 Right-collar forcing from the rational balance

The rational balance gives a first quantitative pinching statement.

Let

\[
\ell=v-u,\qquad a=c-u,\qquad b=v-c,\qquad \ell=a+b,
\]

and for \(t>v\) set \(y=t-v\).  The right-side kernel is

\[
K_R(t)=\frac{t-c}{(u-t)(v-t)}
=
\frac{y+b}{y(y+\ell)}.
\]

As a function of \(y>0\),

\[
\frac{d}{dy}\frac{y+b}{y(y+\ell)}
=
-\frac{y^2+2by+b\ell}{y^2(y+\ell)^2}<0.
\]

Hence \(K_R\) is strictly decreasing as one moves to the right of \(v\).
Fix a collar width \(\rho>0\).  If no compensating mass lies in

\[
(v,v+\rho),
\]

then the entire right side of the rational balance is bounded by

\[
\int_{t>v}K_R(t)\,d\mu(t)
\le
\mu((v+\rho,1])\frac{\rho+b}{\rho(\rho+\ell)}
\le
\frac12\frac{\rho+b}{\rho(\rho+\ell)},
\]

because the standard reduction gives \(\mu(\{-1\})\ge1/2\), hence the total
mass to the right is at most \(1/2\).

On the other hand, the atom at \(-1\) alone gives

\[
\int_{t<u}
\frac{c-t}{(u-t)(v-t)}\,d\mu(t)
\ge
\frac12\frac{c+1}{(u+1)(v+1)}.
\]

Therefore an escaping component with no right-collar mass in \((v,v+\rho)\)
must satisfy the necessary inequality

\[
\boxed{
\frac{c+1}{(u+1)(v+1)}
\le
\frac{\rho+b}{\rho(\rho+\ell)}.
}
\]

Equivalently, if

\[
\boxed{
\frac{c+1}{(u+1)(v+1)}
>
\frac{\rho+b}{\rho(\rho+\ell)},
}
\]

then some mass of \(\mu\) must lie inside the collar \((v,v+\rho)\).

This is the first genuine pinching mechanism: every extra component either
has a sufficiently close right neighbour, or the fixed \(-1\) mass cannot be
balanced.  In a finite-gap extremal, a forced right neighbour is not harmless;
it is exactly the configuration that should either merge into the next
positive component or pinch a gap endpoint.  Thus the next mathematical
target is a collar-to-pinch lemma:

\[
\boxed{
\text{right-collar compensation under } |E|<M_* \text{ forces degeneration to
the } g=1 \text{ branch, unless } |E|\ge M_*.
}
\]

The remaining hard part is to prove that the logarithmic endpoint identity
and the finite-gap positivity/interlacing conditions rule out a non-degenerate
collar chain of such escaping components.

### 16.10 Log-rational efficiency reduction

The collar mechanism becomes sharper when the rational balance and the
logarithmic endpoint identity are put over the same kernel.

Keep

\[
\ell=v-u,\qquad
\theta=\frac{c-u}{v-u}\in(0,1),
\qquad
1-\theta=\frac{v-c}{v-u}.
\]

For \(t<u\), put

\[
r=\frac{u-t}{\ell}>0.
\]

Then

\[
K_L(t)=\frac{c-t}{(u-t)(v-t)}
=\frac{r+\theta}{\ell r(r+1)},
\]

and the left logarithmic magnitude is

\[
L_L(t)=\log\frac{v-t}{u-t}=\log\frac{r+1}{r}.
\]

For \(t>v\), put

\[
s=\frac{t-v}{\ell}>0.
\]

Then

\[
K_R(t)=\frac{t-c}{(u-t)(v-t)}
=\frac{s+1-\theta}{\ell s(s+1)},
\]

and the right logarithmic magnitude is

\[
L_R(t)=\log\frac{t-u}{t-v}=\log\frac{s+1}{s}.
\]

Define the two dimensionless efficiencies

\[
A_L(r;\theta)
=
\frac{L_L}{\ell K_L}
=
\frac{r(r+1)}{r+\theta}\log\frac{r+1}{r},
\]

and

\[
A_R(s;\theta)
=
\frac{L_R}{\ell K_R}
=
\frac{s(s+1)}{s+1-\theta}\log\frac{s+1}{s}.
\]

The rational balance says

\[
B:=
\int_{t<u}K_L(t)\,d\mu(t)
=
\int_{t>v}K_R(t)\,d\mu(t).
\]

The logarithmic endpoint identity becomes

\[
\ell B\left(
\mathbb E_R[A_R]-\mathbb E_L[A_L]
\right)
=
q\log\frac{1-\theta}{\theta},
\]

where \(\mathbb E_L,\mathbb E_R\) denote expectation with respect to the
\(K_L\,d\mu/B\) and \(K_R\,d\mu/B\) weighted probability measures.

This is the clean scalar form of the obstruction.  The fixed atom at \(-1\)
contributes to the left weighted average with

\[
r_-=\frac{u+1}{\ell},\qquad
A_-(u,v,\theta)
=
\frac{r_-(r_-+1)}{r_-+\theta}\log\frac{r_-+1}{r_-},
\]

and with \(K_L\)-weight at least

\[
\frac12
\frac{r_-+\theta}{\ell r_-(r_-+1)}.
\]

The same collar mass forced by the rational balance has small
\(A_R(s;\theta)\) when \(s=(t-v)/\ell\) is small, since

\[
A_R(s;\theta)\to0\qquad (s\downarrow0).
\]

Thus close right-collar mass is efficient for rational balance but inefficient
for the logarithmic endpoint identity.  This is the precise mathematical
tension that should close the \(g=2\) escape:

\[
\boxed{
\text{rational balance forces near-right compensation, while the logarithmic
identity penalizes near-right compensation.}
}
\]

The next scalar lemma should compare the possible ranges of
\(A_L(r;\theta)\) and \(A_R(s;\theta)\), with the forced \(-1\) contribution
included.  Proving that no parameter set with \(|E|<M_*\) satisfies this
weighted efficiency identity would remove the first high-genus escape.

### 16.11 Kernel-shape split at \(\theta=1/2\)

Both efficiencies are instances of the same one-parameter function

\[
A_\alpha(x)
=
\frac{x(x+1)}{x+\alpha}\log\frac{x+1}{x},
\qquad 0<\alpha<1,\quad x>0.
\]

Indeed

\[
A_L(r;\theta)=A_\theta(r),\qquad
A_R(s;\theta)=A_{1-\theta}(s).
\]

The endpoint limits are

\[
\lim_{x\downarrow0}A_\alpha(x)=0,\qquad
\lim_{x\to\infty}A_\alpha(x)=1.
\]

Its derivative is

\[
A_\alpha'(x)
=
\frac{
\left(x^2+2\alpha x+\alpha\right)\log\frac{x+1}{x}
-(x+\alpha)}
{(x+\alpha)^2}.
\]

At infinity,

\[
A_\alpha(x)
=
1+\frac{1/2-\alpha}{x}+O(x^{-2}).
\]

Thus the neutral value is \(\alpha=1/2\).  For \(\alpha>1/2\), far-away mass
has efficiency approaching \(1\) from below; for \(\alpha<1/2\), it approaches
\(1\) from above and the function must have an interior overshoot.

Since \(A_R=A_{1-\theta}\), the escaping atom position splits the \(g=2\)
problem into two regimes.

**Regime I: \(\theta\le1/2\).**  The atom is at or to the left of the midpoint
of the escaping component.  Then

\[
q\log\frac{1-\theta}{\theta}\ge0,
\]

so the efficiency identity requires

\[
\mathbb E_R[A_R]\ge \mathbb E_L[A_L].
\]

But the rational balance forces right compensation close to \(v\), where
\(A_R\) is small, while the \(-1\) atom contributes a fixed left efficiency.
This is the easier contradiction regime.

**Regime II: \(\theta>1/2\).**  The atom is closer to the right endpoint.
Then

\[
q\log\frac{1-\theta}{\theta}<0,
\]

so the efficiency identity allows \(\mathbb E_R[A_R]<\mathbb E_L[A_L]\).
This is the genuinely dangerous case.  However it is also exactly the
pinching case \(b=(1-\theta)\ell<a\): the singular atom is already biased
toward the right endpoint, and the rational balance then forces additional
right-collar compensation near that same endpoint.

The next proof target is therefore sharpened:

\[
\boxed{
\theta\le1/2\text{ should be excluded by the efficiency inequality, while }
\theta>1/2\text{ should force right-endpoint pinching and degeneration.}
}
\]

### 16.12 The monotone side of the efficiency kernel

The first kernel fact needed for the split is elementary and does not require
any numeric certification.

For

\[
A_\alpha(x)=
\frac{x(x+1)}{x+\alpha}\log\frac{x+1}{x},
\qquad x>0,
\]

one has

\[
\boxed{
\alpha\ge\frac12
\quad\Longrightarrow\quad
0<A_\alpha(x)<1
\text{ and } A_\alpha \text{ is strictly increasing.}
}
\]

Indeed,

\[
A_\alpha'(x)
=
\frac{N_\alpha(x)}{(x+\alpha)^2},
\]

where

\[
N_\alpha(x)
=
\left(x^2+2\alpha x+\alpha\right)\log\frac{x+1}{x}
-(x+\alpha).
\]

The derivative of \(N_\alpha\) with respect to \(\alpha\) is

\[
\partial_\alpha N_\alpha(x)
=(2x+1)\log\frac{x+1}{x}-1>0.
\]

The last inequality follows from

\[
\log y>\frac{2(y-1)}{y+1}\qquad (y>1)
\]

with \(y=(x+1)/x\).  Hence for \(\alpha\ge1/2\),

\[
N_\alpha(x)\ge N_{1/2}(x).
\]

Again using the same logarithmic inequality,

\[
N_{1/2}(x)
>
\left(x^2+x+\frac12\right)\frac{2}{2x+1}
-\left(x+\frac12\right)
=
\frac{1}{2(2x+1)}
>0.
\]

Therefore \(A_\alpha'(x)>0\) for \(\alpha\ge1/2\).  Since

\[
\lim_{x\downarrow0}A_\alpha(x)=0,
\qquad
\lim_{x\to\infty}A_\alpha(x)=1,
\]

strict monotonicity gives \(0<A_\alpha(x)<1\).

For the \(g=2\) escape this gives an immediate consequence:

\[
\theta\le\frac12
\quad\Longrightarrow\quad
A_R(s;\theta)=A_{1-\theta}(s)<1
\quad\text{for every }s>0.
\]

Moreover \(A_R(s;\theta)\to0\) as \(s\downarrow0\).  Thus a right-collar
compensation packet cannot carry high logarithmic efficiency in the
\(\theta\le1/2\) branch.  Any attempt to satisfy

\[
\mathbb E_R[A_R]\ge\mathbb E_L[A_L]
\]

must either move a definite portion of right \(K_R\)-mass away from the
collar, or make the left weighted efficiency small.  The first option
contradicts the collar forcing unless the component pinches to a neighbour;
the second option requires left-side mass very close to \(u\), which is the
left-endpoint version of the same pinching phenomenon.

Thus the monotone-kernel lemma converts the \(\theta\le1/2\) branch into a
two-sided collar dichotomy:

\[
\boxed{
\theta\le1/2,\ |E|<M_*
\quad\Rightarrow\quad
\text{either right-endpoint pinching or left-endpoint pinching.}
}
\]

The remaining task in this branch is no longer analytic kernel shape; it is
to show that either endpoint pinching reduces the finite-gap solution to the
\(g=1\) branch or increases total positive length to at least \(M_*\).

### 16.13 Blow-up variables for the dangerous branch \(\theta>1/2\)

The branch

\[
\theta>1/2
\]

is dangerous because the endpoint identity no longer asks the right weighted
efficiency to dominate the left one.  It is better viewed as a right-endpoint
blow-up.

Put

\[
a=c-u,\qquad b=v-c,\qquad \kappa=\frac{a}{b}>1,
\qquad \ell=a+b=b(\kappa+1).
\]

For right-side mass near \(v\), write

\[
t=v+b\tau,\qquad \tau>0.
\]

Then the rational kernel and logarithmic magnitude become

\[
K_R(t)
=
\frac{t-c}{(u-t)(v-t)}
=
\frac{\tau+1}{b\,\tau(\tau+\kappa+1)},
\]

and

\[
L_R(t)
=
\log\frac{t-u}{t-v}
=
\log\frac{\tau+\kappa+1}{\tau}.
\]

Thus a right-collar packet at distance \(O(b)\) has rational strength
\(O(m/b)\) if its mass is \(m\), but logarithmic strength only
\(O(m)\).  To compensate the fixed \(-1\) contribution, such a packet needs
only mass \(m=O(b)\).  Consequently, in the dangerous branch the compensating
right mass is naturally a vanishing endpoint cluster.

The singular atom itself is also at distance \(b\) from the endpoint \(v\).
Therefore the local picture is a three-object cluster:

\[
c=v-b,\qquad
t=v+b\tau,\qquad
v.
\]

This is exactly the geometry of a pinching degeneration of the finite-gap
transform.  In Stieltjes terms, a positive finite-gap solution cannot keep
such a cluster as an independent \(g=2\) feature unless the associated zero
of \(P\), the endpoint \(v\), and the nearby compensating pole/cut collapse
in the same local scale.

The dangerous branch should therefore be attacked by the following blow-up
claim.

\[
\boxed{
\theta>1/2,\ |E|<M_*
\quad\Longrightarrow\quad
\text{the right endpoint }v\text{ is a removable pinching limit, not a new
non-degenerate }g=2\text{ extremal.}
}
\]

After pinching, the limiting transform loses one gap and returns to the
already isolated \(g=1\) two-interval branch.  Thus the exact lower bound
reduces to proving that the blow-up limit above preserves positivity of
residues and density only in the pinched \(g=1\) configuration.

### 16.14 The overshoot side is unimodal

The complementary kernel regime is also elementary.  For

\[
0<\alpha<\frac12,
\]

the function

\[
A_\alpha(x)=
\frac{x(x+1)}{x+\alpha}\log\frac{x+1}{x}
\]

has exactly one critical point; it increases from \(0\), reaches one maximum
larger than \(1\), and then decreases to \(1\) from above.

Use the same numerator

\[
N_\alpha(x)
=
\left(x^2+2\alpha x+\alpha\right)\log\frac{x+1}{x}
-(x+\alpha),
\qquad
A_\alpha'(x)=\frac{N_\alpha(x)}{(x+\alpha)^2}.
\]

Its derivative is

\[
N_\alpha'(x)
=
2(x+\alpha)\log\frac{x+1}{x}
-
\frac{2x^2+(2\alpha+1)x+\alpha}{x(x+1)}.
\]

The sharp elementary upper bound

\[
\log\frac{x+1}{x}
<
\frac{2x+1}{2x(x+1)}
\]

is just

\[
\log y<\frac{y^2-1}{2y},\qquad y>1,
\]

with \(y=(x+1)/x\).  Substituting it gives

\[
N_\alpha'(x)<0.
\]

Thus \(N_\alpha\) is strictly decreasing.  Since

\[
\lim_{x\downarrow0}N_\alpha(x)=+\infty,\qquad
\lim_{x\to\infty}N_\alpha(x)=\alpha-\frac12<0,
\]

there is a unique root \(x_\alpha\).  Hence \(A_\alpha\) increases on
\((0,x_\alpha)\) and decreases on \((x_\alpha,\infty)\).  The asymptotic

\[
A_\alpha(x)=1+\frac{1/2-\alpha}{x}+O(x^{-2})
\]

shows that the limiting value \(1\) is approached from above, so the maximum
is strictly larger than \(1\).

For the \(g=2\) escape this means that in the dangerous branch

\[
\theta>1/2,\qquad A_R=A_{1-\theta},
\]

right-side logarithmic efficiency larger than \(1\) can only come from mass
away from the immediate collar.  The collar itself has \(A_R\to0\).  Thus the
right side faces a strict alternative:

\[
\boxed{
\text{near-right mass balances rationally but has poor log efficiency; far
right mass can have high log efficiency but loses rational strength.}
}
\]

This is the scalar form of the blow-up/pinching dichotomy.

### 16.15 Mass-scale consequence of the dangerous blow-up

The blow-up variables also give a quantitative weak-limit statement.

Assume \(\theta>1/2\), so \(a>b\), and write

\[
\kappa=\frac{a}{b}>1.
\]

Suppose first that \(\kappa\) stays bounded away from \(1\).  The rational
balance has a fixed contribution from the atom at \(-1\):

\[
B\ge
\frac12\frac{c+1}{(u+1)(v+1)}.
\]

This is \(O(1)\) and bounded below as long as the extra component remains in
\((0,1)\).  On the right \(b\)-scale, a compensating packet of mass \(m_b\)
near

\[
t=v+b\tau
\]

has rational size

\[
K_R(t)m_b
\asymp
\frac{m_b}{b}
\frac{\tau+1}{\tau(\tau+\kappa+1)}.
\]

Therefore rational balance with an \(O(1)\) left side forces

\[
\boxed{
m_b=O(b)
}
\]

for the entire \(b\)-scale compensating cluster.

The endpoint identity gives

\[
\ell B(\mathbb E_R[A_R]-\mathbb E_L[A_L])
=
q\log\frac{b}{a}
=
-q\log\kappa.
\]

Since \(\ell=b(\kappa+1)\), the left side is \(O(b)\) in every
non-pinching compact \(\tau\)-window.  Hence, if \(\kappa\) is also bounded
above, or more generally if \(\log\kappa\) does not vanish, then

\[
\boxed{
q=O\!\left(\frac{b}{\log\kappa}\right).
}
\]

Thus the singular atom inside the escaping component also loses mass in the
pinching limit.  The only ways out are now explicit:

1. \(\kappa\downarrow1\), which returns to the neutral \(\theta=1/2\) split;
2. \(\kappa\to\infty\), where the atom approaches the right endpoint much
faster than the left endpoint and a second blow-up is needed;
3. an actual endpoint pinching of the finite-gap branch.

In the main dangerous regime, the weak limit therefore deletes the escaping
component: both the interior atom and the nearby compensating right cluster
carry vanishing mass.  The candidate \(g=2\) extremal cannot survive as a
new non-degenerate object; it must converge to the \(g=1\) two-interval
branch unless the length bound has already been met.

### 16.16 Secondary blow-up when \(\kappa\to\infty\)

It remains to understand the second escape in the dangerous branch:

\[
\kappa=\frac{a}{b}\to\infty.
\]

Here \(c\) approaches the right endpoint \(v\) much faster than it approaches
the left endpoint \(u\).  The correct scale is still

\[
t=v+b\tau,
\]

but now

\[
\ell=b(\kappa+1)\sim a.
\]

The right rational kernel is

\[
K_R(t)
=
\frac{\tau+1}{b\,\tau(\tau+\kappa+1)}
\sim
\frac{\tau+1}{a\tau}
\qquad(\tau=O(1)).
\]

Thus the \(b\)-scale right collar no longer has \(1/b\) rational amplification;
it has only \(O(1)\) rational strength.  But its logarithmic contribution is

\[
L_R(t)
=
\log\frac{\tau+\kappa+1}{\tau}
=
\log\kappa+O(1).
\]

So the \(\kappa\to\infty\) branch has a different obstruction:

\[
\boxed{
\text{\(b\)-scale right mass has ordinary rational strength but logarithmic
strength of order }\log\kappa.
}
\]

The endpoint identity

\[
\ell B(\mathbb E_R[A_R]-\mathbb E_L[A_L])
=
-q\log\kappa
\]

therefore gives a clean dichotomy.

**Case 1: a non-vanishing amount of the \(K_R\)-weighted right balance lives
in a fixed \(b\)-scale window \(0<\tau_0\le\tau\le\tau_1<\infty\).**  Then
\(\mathbb E_R[A_R]\) has a positive \(O(\log\kappa)\) contribution.  But in
this branch \(\theta>1/2\), so the monotone-kernel lemma gives

\[
A_L(r;\theta)=A_\theta(r)<1.
\]

Hence \(\mathbb E_L[A_L]\le1\), while the right side of the endpoint identity
is negative:

\[
-q\log\kappa<0.
\]

So Case 1 is impossible.  The only way a \(b\)-scale right packet can avoid
this contradiction is to move to \(\tau\downarrow0\), where \(A_R\) becomes
small.  That is not a non-degenerate \(b\)-scale packet; it is actual
right-endpoint pinching.

**Case 2: the \(b\)-scale right collar carries vanishing \(K_R\)-weighted
balance.**  Then the rational balance is supplied at macroscopic right
distance, where \(A_R=O(1)\).  The left side of the endpoint identity is
therefore \(O(1)\), while the right side is \(-q\log\kappa\).  Hence

\[
\boxed{
q=O\!\left(\frac1{\log\kappa}\right).
}
\]

The escaping atom loses mass.  Since it is also at distance \(b\) from the
right endpoint, it does not survive as a non-degenerate interior atom in the
weak limit.

Thus the secondary blow-up produces no new stable \(g=2\) object.  It gives
only:

1. actual right-endpoint pinching \(\tau\downarrow0\); or
2. disappearance of the escaping atom and return to the lower-genus limit.

This closes the \(\kappa\to\infty\) alternative at the level of mathematical
reduction.  The remaining proof obligation is the finite-gap pinching lemma:
pinching of the branch data must reduce the Cauchy transform to the
\(g=1\) two-interval branch, preserving positivity in the limit.

### 16.17 Finite-gap pinching factor-cancellation lemma

The required pinching lemma is algebraic.  Consider a sequence of positive
finite-gap Stieltjes transforms

\[
F_n(z)=
\frac{P_n(z)}{Q_n(z)}
\sqrt{
(z-\alpha_{1,n})(z-\beta_{1,n})
(z-\alpha_{2,n})(z-\beta_{2,n})
}
\]

with the usual branch at infinity, positive density on cuts, and non-negative
residues at real poles.  Suppose a pair of adjacent branch points pinches:

\[
\beta_{1,n}\to\gamma,\qquad \alpha_{2,n}\to\gamma.
\]

Then locally

\[
\sqrt{(z-\beta_{1,n})(z-\alpha_{2,n})}
\longrightarrow
z-\gamma
\]

on compact subsets away from \(\gamma\), with the sign fixed by the branch.
Hence

\[
F_n(z)
\longrightarrow
\frac{\widetilde P(z)}{\widetilde Q(z)}
(z-\gamma)
\sqrt{(z-\alpha_1)(z-\beta_2)}
\]

before cancelling coalescing pole/zero factors.

There are only three possible local outcomes.

1. **No pole of \(Q_n\) pinches at \(\gamma\).**  Then the factor \(z-\gamma\)
is analytic and can be absorbed into the numerator.  The square-root genus
has dropped by one.

2. **A pole \(p_n\) of \(Q_n\) pinches at \(\gamma\).**  Positivity of residues
and local boundedness of the Stieltjes transforms force the quotient

\[
\frac{z-\gamma}{z-p_n}
\]

to have a finite non-negative limiting residue contribution.  After cancelling
the common removable factor, the remaining transform again has one fewer
square-root cut.  If a positive atom remains at \(\gamma\), it is a pole of
the lower-genus transform, not a new branch.

3. **A zero of \(P_n\) pinches at \(\gamma\).**  Then the zero is absorbed into
the analytic numerator.  It can only reduce mass or create a removable zero;
it cannot create a new positive cut.

Therefore every finite-gap endpoint pinching limit has the form

\[
\boxed{
F_\infty(z)
=
\frac{P_\infty(z)}{Q_\infty(z)}
\sqrt{(z-\alpha_1)(z-\beta_2)}
}
\]

plus possible non-negative endpoint atoms recorded in \(Q_\infty\).  Positivity
of residues and density is closed under weak limits.  Thus a pinched
non-negative \(g=2\) candidate is not a new extremal family; it is a
\(g=1\) candidate with possibly extra endpoint atoms.

This is exactly what is needed for the normalized lower-bound route: all
escape mechanisms found in Sections 16.12--16.16 either force pinching or
delete the escaping component, and pinching returns to the already isolated
\(g=1\) two-interval branch.  The remaining compact case is a genuinely
non-pinched \(g=2\) positive finite-gap solution; it is now the only case
still requiring a direct inequality.

### 16.18 Compact non-pinched \(g=2\) chamber

After the pinching reductions, a hypothetical \(g=2\) counterexample with
\(|E|<M_*\) must lie in a compact non-pinched chamber, unless it has already
degenerated to the \(g=1\) branch.

Concretely, for some \(\delta>0\), all of the following quantities are bounded
below by \(\delta\):

\[
\beta_1-\alpha_1,\quad
\alpha_2-\beta_1,\quad
\beta_2-\alpha_2,\quad
c-u,\quad
v-c,
\]

and all residues and cut-density sign margins are also at least \(\delta\).
The length bound is

\[
|E|=(R_0-L_0)+(v-u)\le M_*-\delta.
\]

Inside this chamber there is no endpoint collision, no disappearing atom, and
no zero-density boundary.  Thus every positivity condition is an open
inequality, and any length-minimising counterexample is an interior point of a
finite-dimensional smooth system.

Let \(\Theta\) denote the finite-gap parameters.  These include the branch
points, the real poles/residues, the zero \(c\) of the numerator \(P\), and
the finite normalization constants.  The active equations are:

1. the Stieltjes normalization at infinity;
2. the flat-zero period equation between the two zero bands;
3. the complementarity zero

\[
F(c)=0;
\]

4. the primal escaping-component stationarity

\[
(c-u)U_\mu'(u)+(v-c)U_\mu'(v)=0;
\]

5. the endpoint zero equations

\[
U_\mu(u)=U_\mu(v)=0.
\]

Write these equations as

\[
\mathcal G(\Theta)=0
\]

and write the length functional as

\[
\mathcal L(\Theta)=(R_0-L_0)+(v-u).
\]

At an interior compact counterexample minimising length, the KKT condition is

\[
\boxed{
d\mathcal L(\Theta)\in \operatorname{span}\{d\mathcal G_j(\Theta)\}.
}
\]

Equivalently, if the Jacobian of \(\mathcal G\) has full rank and
\(d\mathcal L\) is not in its row span, then there is an admissible tangent
direction decreasing \(\mathcal L\), contradicting minimality.

Thus the compact \(g=2\) problem has been reduced to a finite-dimensional
rank obstruction:

\[
\boxed{
\text{show that no positive, non-pinched }g=2\text{ finite-gap point with }
\mathcal L<M_*\text{ satisfies the KKT row-span condition.}
}
\]

This is the right replacement for the earlier vague phrase "global topology".
All boundary exits have already been assigned to pinching or lower-genus
limits; what remains is an interior finite algebraic/transcendental
non-existence statement.

### 16.19 Adjoint form of the compact rank obstruction

The KKT condition can be stated without choosing a particular coordinate
chart.  Suppose an interior compact \(g=2\) minimiser exists.  Then there are
real multipliers, not all zero, such that the first variation

\[
d\mathcal L-\sum_j\lambda_j\,d\mathcal G_j
\]

vanishes on every finite-gap tangent direction.

Finite-gap tangent directions are again Cauchy transforms with the same
hyperelliptic square root, plus rational terms coming from variations of
poles and branch points.  Therefore the adjoint condition is equivalent to
the existence of a non-zero meromorphic differential on the two-cut curve.
The algebraic genus is one; the label \(g=2\) here refers to the two active
finite-gap intervals.

\[
w^2=
(z-\alpha_1)(z-\beta_1)(z-\alpha_2)(z-\beta_2)
\]

with the following forced properties:

1. prescribed principal parts at the active poles;
2. vanishing periods corresponding to the flat-zero constraints;
3. zeros at the escaping atom \(c\) forced by \(F(c)=0\);
4. endpoint sign conditions inherited from \(U_\mu(u)=U_\mu(v)=0\);
5. no allowed sign change on the positive density cuts.

The key point is that these conditions overdetermine a meromorphic
differential of the available degree.  In divisor language, the adjoint would
need too many real zeros while having too few poles once positivity removes
the possible boundary cancellations.

The compact case should therefore be closed by the following divisor-count
lemma.

\[
\boxed{
\text{No non-zero adjoint meromorphic differential satisfying the five
conditions above exists in the positive non-pinched }g=2\text{ chamber.}
}
\]

If this lemma is proved, then the compact \(g=2\) chamber is empty below
\(M_*\).  Together with the pinching reductions, this would finish the
normalised \(g=2\) lower-bound step.

The next concrete mathematical task is to write the divisor of this adjoint
differential explicitly in terms of \(P,Q\) and the four branch points, then
count zeros and poles after imposing the period and endpoint conditions.

### 16.20 Clearing denominators in the adjoint differential

The adjoint obstruction can be made concrete by clearing the same denominators
that occur in the finite-gap Stieltjes transform.

Write

\[
D(z)=
(z-\alpha_1)(z-\beta_1)(z-\alpha_2)(z-\beta_2),
\qquad
w^2=D(z),
\]

and

\[
F(z)=\frac{P(z)}{Q(z)}w.
\]

The poles of \(Q\) encode endpoint atoms or active rational poles.  In the
compact non-pinched chamber, all zeros of \(Q\) stay away from branch points
and away from the escaping atom \(c\).

After fixing the allowed principal parts at the poles of \(Q\), every adjoint
first variation can be represented, modulo the single holomorphic
differential \(dz/w\), in the form

\[
\Omega_H
=
\frac{H(z)}{Q(z)^2\,w}\,dz,
\]

where \(H\) is a real polynomial.  The square \(Q^2\) appears because varying
a pole or residue of \(P/Q\) creates at most double poles in the adjoint
pairing.  The degree of \(H\) is fixed by the condition that \(\Omega_H\) has
no forbidden pole at the two points at infinity on the compactified curve.

Thus the compact adjoint problem is equivalent to a real polynomial problem:
find a non-zero real polynomial \(H\), of the admissible degree, such that
\(\Omega_H\) satisfies:

1. zero \(A\)-periods coming from the flat-zero condition;
2. the endpoint equations \(U_\mu(u)=U_\mu(v)=0\);
3. the escaping atom condition \(F(c)=0\), which imposes

\[
H(c)=0
\]

after clearing \(Q(c)^2w(c)\ne0\);

4. the sign constraint that \(\Omega_H\) has no sign change on the positive
density cuts unless it vanishes there.

The last item is the important one.  On each real cut, \(w_+(x)\) is purely
imaginary and the density sign of \(F\) fixes the sign of

\[
\frac{P(x)}{Q(x)}
\]

relative to the chosen branch.  Hence any admissible adjoint variation that
preserves positivity to first order cannot have an arbitrary sign pattern;
after multiplying by the fixed sign of \(Q^2w_+\), its sign is the sign of
the real polynomial \(H(x)\).  Therefore the compact obstruction reduces to:

\[
\boxed{
\text{no non-zero admissible }H\text{ has the required zeros, periods, and
one-sided signs on the two real cuts.}
}
\]

This is a sharper target than the previous divisor-count statement because it
names the actual object to exclude.

### 16.21 Real-oval sign obstruction

The two-cut curve has two real ovals.  In the compact chamber the cuts and
poles are separated, so after clearing \(Q^2\) the sign of the adjoint on
each oval is governed by \(H\).

Let the two real cuts be

\[
I_1=[\alpha_1,\beta_1],\qquad
I_2=[\alpha_2,\beta_2].
\]

The zero-period condition for \(\Omega_H\) has the form

\[
\int_{I_1}\frac{H(x)}{|Q(x)|^2\sqrt{|D(x)|}}\,dx
=
\int_{I_2}\frac{H(x)}{|Q(x)|^2\sqrt{|D(x)|}}\,dx
\]

up to a fixed positive normalization.  The weights are strictly positive in
the compact chamber.  Therefore, if \(H\) has one sign on both cuts, the
period equation forces the weighted masses to match exactly.  Varying the
relative branch length gives a second independent period/endpoint functional,
so a non-zero \(H\) that keeps a fixed sign on both cuts must satisfy two
independent positive-weight moment equations.

The escaping atom condition gives \(H(c)=0\), with \(c\) lying in the positive
component between endpoint constraints, not on a cut.  The endpoint equations
give two more real linear conditions.  Thus the compact chamber requires a
real polynomial \(H\) satisfying:

\[
H(c)=0,\qquad
\Lambda_1(H)=0,\qquad
\Lambda_2(H)=0,\qquad
\Lambda_3(H)=0,
\]

where each \(\Lambda_j\) is integration against a strictly positive real
kernel or evaluation of the same Cauchy primitive at an endpoint.

The sign obstruction is:

\[
\boxed{
\text{a non-zero admissible }H\text{ satisfying these four constraints must
change sign on a real oval.}
}
\]

But a sign change on a real oval is exactly an infinitesimal loss of positivity
of the dual density or residue sign, contradicting compact interior
positivity.  Therefore the remaining compact \(g=2\) case can be closed by
proving this real-oval sign lemma.

At this point the proof line has been reduced to a precise, local statement:
the compact chamber is excluded if the positive-kernel linear functionals
\(\Lambda_j\) form a Chebyshev system on the real ovals after the zero at
\(c\) is imposed.

### 16.22 Total positivity route for the Chebyshev lemma

There is a standard way to prove the Chebyshev statement: use strict total
positivity of the Cauchy kernel on separated real intervals.

If

\[
x_1<\cdots<x_n,\qquad y_1<\cdots<y_n,
\]

and the \(x_i\)'s lie strictly to one side of the \(y_j\)'s, then

\[
\det\left(\frac{1}{x_i-y_j}\right)_{i,j=1}^n
=
\frac{
\prod_{i<k}(x_k-x_i)\prod_{j<\ell}(y_j-y_\ell)
}{
\prod_{i,j}(x_i-y_j)
}
\]

has a fixed non-zero sign.  Multiplication by a positive weight preserves this
sign-regularity.  Integration against a positive measure in the \(y\)-variable
also preserves total positivity.

The endpoint and period functionals in Section 16.21 are built from exactly
these kernels.  For example, a logarithmic endpoint difference can be written
as

\[
\log\frac{|x-u|}{|x-v|}
=
\int_u^v\frac{ds}{x-s}
\]

with \(x\) on a cut disjoint from \([u,v]\).  Thus the logarithmic functionals
are positive averages of Cauchy kernels.  The period kernels are the same
Cauchy kernels multiplied by the positive elliptic weight

\[
\frac{1}{|Q(x)|^2\sqrt{|D(x)|}}.
\]

Consequently the collection

\[
1,\quad
\int_u^v\frac{ds}{x-s},\quad
\frac{1}{x-c},\quad
\text{period kernel}
\]

is expected to be a sign-regular system on each compact real oval, after the
fixed zero \(H(c)=0\) is factored out.  The remaining compact \(g=2\) chamber
therefore reduces to the following concrete total-positivity lemma.

\[
\boxed{
\text{The weighted Cauchy/logarithmic kernels defining }\Lambda_1,\Lambda_2,
\Lambda_3\text{ are a strict Chebyshev system on the two real ovals.}
}
\]

Once this lemma is proved, every non-zero admissible \(H\) satisfying

\[
H(c)=0,\qquad \Lambda_1(H)=\Lambda_2(H)=\Lambda_3(H)=0
\]

must have enough sign changes to violate compact positivity.  This would close
the compact non-pinched \(g=2\) case without any numerical verification.

This is now the best mathematical next step: prove the strict
total-positivity/Chebyshev lemma directly from the Cauchy determinant formula
and the separation of intervals in the compact chamber.

### 16.23 Variation-diminishing lemma for the compact adjoint

The Chebyshev reduction needs one standard sign-variation theorem.

Let \(J\) be an ordered compact union of real intervals and let

\[
\phi_0,\ldots,\phi_{m-1}
\]

be a strict Chebyshev system on \(J\): for every

\[
x_1<\cdots<x_m
\]

in \(J\), the determinant

\[
\det(\phi_i(x_j))_{i,j=0}^{m-1}
\]

has a fixed non-zero sign.  Let \(\omega(x)>0\) be a positive continuous
weight.  If a non-zero continuous function \(h\) satisfies

\[
\int_J h(x)\phi_i(x)\omega(x)\,dx=0,
\qquad i=0,\ldots,m-1,
\]

then \(h\) has at least \(m\) sign changes on \(J\).

The proof is short.  If \(h\) had at most \(m-1\) sign changes, choose the
change points and use the Chebyshev interpolation property to build a linear
combination

\[
\Phi(x)=\sum_{i=0}^{m-1}a_i\phi_i(x)
\]

whose sign agrees with \(h\) on every sign interval and which is not
identically zero.  Then

\[
\int_J h(x)\Phi(x)\omega(x)\,dx>0,
\]

contradicting the \(m\) moment equations.

Applied to the compact adjoint, the signed function is

\[
h(x)=H(x)
\]

on the real ovals, with the positive weight

\[
\omega(x)=\frac{1}{|Q(x)|^2\sqrt{|D(x)|}}.
\]

The zero \(H(c)=0\) is outside the two density cuts; after factoring the
linear term \(z-c\) in the adjoint polynomial, the remaining period and
endpoint equations are moment equations for Cauchy/logarithmic kernels.
Therefore:

\[
\boxed{
\text{if those kernels form a strict Chebyshev system of dimension }m,
\text{ then every non-zero adjoint }H\text{ has at least }m
\text{ sign changes on the cuts.}
}
\]

Compact positivity permits no such sign change in an admissible first-order
adjoint: changing sign on a density cut would create a tangent direction that
breaks the non-negative density sign on one side of the cut.  Hence the
compact chamber is excluded once the strict Chebyshev property is established
for the concrete kernels \(\Lambda_j\).

### 16.24 Concrete remaining lemma

The proof line has now isolated the last compact \(g=2\) task as the following
pure real-variable statement.

Let

\[
I_1=[\alpha_1,\beta_1],\qquad
I_2=[\alpha_2,\beta_2],
\qquad
\beta_1<\alpha_2,
\]

and let

\[
u<c<v
\]

lie in the escaping positive component disjoint from the cuts.  Let

\[
\omega(x)=\frac{1}{|Q(x)|^2\sqrt{|D(x)|}}>0
\]

on \(I_1\cup I_2\).  Define the ordered real support

\[
J=I_1\cup I_2
\]

with the usual left-to-right order.  The kernels to control are generated by

\[
1,\qquad
\frac{1}{x-c},\qquad
\int_u^v\frac{ds}{x-s},\qquad
\text{the period-normalized constant on each oval}.
\]

The remaining lemma is:

\[
\boxed{
\text{after factoring }H(c)=0,\text{ the three independent endpoint/period
kernels form an extended strict Chebyshev system on }J
\text{ with weight }\omega.
}
\]

The Cauchy determinant identity proves strict sign-regularity for the raw
kernels \(1/(x-y)\).  Positive integration over \(s\in[u,v]\), multiplication
by \(\omega\), and taking non-degenerate linear combinations preserve
sign-regularity in the compact chamber.  Therefore the only missing
mathematical detail is to check that the endpoint/period linear combinations
are non-degenerate and do not collapse to a lower-dimensional system.

This is a finite determinant non-vanishing problem, not a global variational
problem.  In symbolic form, one must show that the \(3\times3\) Wronskian-like
determinants of the three kernels have fixed sign on every ordered triple of
points in \(J\).  Once this determinant sign is established, the compact
non-pinched \(g=2\) chamber is empty below \(M_*\).

### 16.25 Correction: the naive three-kernel determinant is not automatic

The previous paragraph identifies the right local object, but one must not
silently assume that the three kernels

\[
1,\qquad \frac1{x-c},\qquad \int_u^v\frac{ds}{x-s}
\]

are automatically a strict Chebyshev system.  The reason is that the
integration interval \([u,v]\) contains the pole parameter \(c\).  This creates
a signed cancellation that is invisible if one only quotes the Cauchy
determinant formula.

For ordered points

\[
x_1<x_2<x_3
\]

outside \([u,v]\), put

\[
L(x)=\int_u^v\frac{ds}{x-s}.
\]

Then

\[
\Delta(x_1,x_2,x_3)
=
\det
\begin{pmatrix}
1 & (x_1-c)^{-1} & L(x_1)\\
1 & (x_2-c)^{-1} & L(x_2)\\
1 & (x_3-c)^{-1} & L(x_3)
\end{pmatrix}
\]

satisfies the exact identity

\[
\boxed{
\Delta
=
\frac{
(x_2-x_1)(x_3-x_1)(x_3-x_2)
}{
\prod_{i=1}^3(x_i-c)
}
\int_u^v
\frac{c-s}{\prod_{i=1}^3(x_i-s)}\,ds.
}
\]

The factor \(c-s\) changes sign at \(s=c\).  Hence the determinant sign is
not controlled by interval separation alone.  A small numerical stress test
with arbitrary separated \(u<c<v\) and \(x_i\notin[u,v]\) shows both signs
can occur.  This is not a failure of the global route; it says the compact
case needs the stationarity equation, not just raw Cauchy total positivity.

The correct lesson is:

\[
\boxed{
\text{the compact Chebyshev lemma must use the split at }c
\text{ and the escaping-component stationarity.}
}
\]

### 16.26 Split-log repair

Define the two one-sided logarithmic kernels

\[
L_-(x)=\int_u^c\frac{ds}{x-s},\qquad
L_+(x)=\int_c^v\frac{ds}{x-s}.
\]

Each is a positive average of Cauchy kernels over an interval that does not
cross \(c\).  Therefore the Cauchy determinant identity applies separately to
\[
1,\quad \frac1{x-c},\quad L_-(x)
\]

and to

\[
1,\quad \frac1{x-c},\quad L_+(x),
\]

with fixed sign on every compact chamber where the cuts are separated from
\([u,v]\).

The original endpoint logarithmic condition uses

\[
L=L_-+L_+.
\]

The missing information is exactly the stationarity/rational-balance
condition, which distinguishes the two sides of \(c\):

\[
(c-u)W'(u)+(v-c)W'(v)=0.
\]

Equivalently, in the cleared adjoint problem, the \(L_-\) and \(L_+\) moments
are not arbitrary; their coefficients are coupled by the positive lengths

\[
a=c-u,\qquad b=v-c.
\]

Thus the corrected compact lemma is not a naive three-kernel determinant
lemma.  It is a split Chebyshev statement:

\[
\boxed{
\text{the four kernels }1,\ (x-c)^{-1},\ L_-,\ L_+
\text{ form a sign-regular system, and the stationarity relation forbids
the only signed combination that could avoid real-oval sign changes.}
}
\]

This is now the precise next proof target.  It is stronger than the earlier
three-kernel claim and uses the actual variational equation of the escaping
component.  The next calculation should write the stationarity-coupled
determinant as a positive combination of the two one-sided Cauchy determinants
above.

### 16.27 Oriented four-kernel determinant

The split formulation gives an exact determinant identity which was hidden by
the collapsed kernel \(L=L_-+L_+\).  For

\[
s\in(u,c),\qquad t\in(c,v),
\]

and ordered points \(x_1<\cdots<x_4\) outside \([u,v]\), the Cauchy
determinant formula gives

\[
\det
\begin{pmatrix}
1 & (x_1-c)^{-1} & (x_1-s)^{-1} & (x_1-t)^{-1}\\
1 & (x_2-c)^{-1} & (x_2-s)^{-1} & (x_2-t)^{-1}\\
1 & (x_3-c)^{-1} & (x_3-s)^{-1} & (x_3-t)^{-1}\\
1 & (x_4-c)^{-1} & (x_4-s)^{-1} & (x_4-t)^{-1}
\end{pmatrix}
\]

\[
=
-
\frac{
\prod_{i<j}(x_j-x_i)\,(c-s)(c-t)(s-t)
}{
\prod_{i=1}^4 (x_i-c)(x_i-s)(x_i-t)
}.
\]

Since \(s<c<t\), the source factor

\[
(c-s)(c-t)(s-t)=(c-s)(t-c)(t-s)
\]

is positive.  Integrating this identity over \(s\in[u,c]\) and
\(t\in[c,v]\) gives

\[
\Delta_4(x_1,\ldots,x_4)
:=
\det\bigl[1,\ (x-c)^{-1},\ L_-(x),\ L_+(x)\bigr]_{x=x_i}
\]

\[
=
-
\prod_{i<j}(x_j-x_i)
\int_u^c\int_c^v
\frac{(c-s)(t-c)(t-s)}
{\prod_{i=1}^4 (x_i-c)(x_i-s)(x_i-t)}
\,dt\,ds .
\]

The denominator sign is not a defect.  For \(x_i\notin[u,v]\),

\[
\operatorname{sgn}\bigl((x_i-c)(x_i-s)(x_i-t)\bigr)
=
\operatorname{sgn}(x_i-c).
\]

Therefore, with the real-oval orientation factor

\[
\sigma(x):=\operatorname{sgn}(x-c),
\]

one has the fixed sign statement

\[
\boxed{
\left(\prod_{i=1}^4\sigma(x_i)\right)
\Delta_4(x_1,\ldots,x_4)<0
}
\]

for every ordered quadruple in the compact separated chamber.

This is the first genuinely useful replacement for the failed naive
three-kernel determinant.  It says that the split kernels are not an ordinary
Chebyshev system on the un-oriented union of the two cuts.  They are a strict
Chebyshev system on the oriented real ovals, where the two sides of the
escaping component carry opposite signs.

### 16.28 Why the orientation is the right one

The orientation factor is not artificial.  The adjoint already contains the
forced zero

\[
H(c)=0.
\]

Writing

\[
H(x)=(x-c)G(x),
\]

the physical condition "no sign change of \(H\) on the positive density cuts"
does **not** mean that \(G\) has one ordinary sign on
\(I_1\cup I_2\).  Because \(x-c\) changes sign across the escaping component,
it means that

\[
\sigma(x)G(x)
\]

has one ordinary sign on the oriented union.

Thus the corrected compact obstruction has the following shape:

1. factor \(H=(x-c)G\);
2. rewrite the period and endpoint first variations as moments of \(G\)
against the four split kernels

\[
1,\quad (x-c)^{-1},\quad L_-,\quad L_+;
\]

3. insert the natural orientation \(\sigma(x)=\operatorname{sgn}(x-c)\);
4. use the determinant inequality in 16.27 to force sign variation of
\(\sigma G\);
5. translate back to a sign change of \(H\) on a real oval, contradicting
compact interior positivity.

The remaining mathematical hard point is now smaller and sharper than before:

\[
\boxed{
\text{derive the exact first-variation identities showing that the compact
adjoint moments are precisely the oriented split-kernel moments above.}
}
\]

Once those identities are written down, the determinant sign is already fixed
by 16.27; the proof no longer needs a numerical search at this compact
obstruction.

### 16.29 Local field-increment identities

The adjoint-to-split-kernel identification can be separated from the global
finite-gap parametrisation.  Let \(\eta\) be any signed first-order variation
of the exterior dual density/residue data supported on the real cuts

\[
J=I_1\cup I_2,\qquad J\cap[u,v]=\varnothing.
\]

Define its logarithmic field on the escaping component by

\[
\Phi_\eta(y)
:=
\int_J \log\frac1{|y-x|}\,d\eta(x).
\]

Then

\[
\Phi_\eta'(y)
=
\int_J\frac{d\eta(x)}{x-y}.
\]

Hence the four local probes of the field at \(u<c<v\) are exactly

\[
\eta(J)=\int_J 1\,d\eta,
\]

\[
\Phi_\eta'(c)
=
\int_J\frac{d\eta(x)}{x-c},
\]

\[
\Phi_\eta(c)-\Phi_\eta(u)
=
\int_J
\left(\int_u^c\frac{ds}{x-s}\right)d\eta(x)
=
\int_J L_-(x)\,d\eta(x),
\]

and

\[
\Phi_\eta(v)-\Phi_\eta(c)
=
\int_J
\left(\int_c^v\frac{ds}{x-s}\right)d\eta(x)
=
\int_J L_+(x)\,d\eta(x).
\]

Thus the split kernels have a direct intrinsic meaning:

\[
\boxed{
1,\ (x-c)^{-1},\ L_-,\ L_+
\text{ are the total mass, the }c\text{-jet, and the two one-sided
field increments across the escaping component.}
}
\]

This is the missing bridge between the variational equations and the
determinant calculation in 16.27.  Endpoint equations are equations for the
field values at \(u\) and \(v\); the dual zero \(F(c)=0\) is the vanishing of
the \(c\)-jet; and the stationarity equation couples the two one-sided
increments through the positive lengths

\[
a=c-u,\qquad b=v-c.
\]

### 16.30 Density row-space reduction

The compact adjoint does not need arbitrary values of
\(\Phi_\eta(u),\Phi_\eta(c),\Phi_\eta(v)\).  The atom variables

\[
q,\qquad a=c-u,\qquad b=v-c,\qquad c
\]

absorb the common additive field level and the singular logarithmic terms.
After this local elimination, the exterior density part of the linearised
endpoint/atom block depends only on the four quantities in 16.29:

\[
\eta(J),\qquad
\Phi_\eta'(c),\qquad
\Phi_\eta(c)-\Phi_\eta(u),\qquad
\Phi_\eta(v)-\Phi_\eta(c).
\]

Equivalently, if the adjoint polynomial is factored as

\[
H(x)=(x-c)G(x),
\]

then the density row-space of the compact KKT obstruction is spanned by the
moments

\[
\int_J G(x)\omega(x)\,dx,\qquad
\int_J \frac{G(x)\omega(x)}{x-c}\,dx,
\]

\[
\int_J L_-(x)G(x)\omega(x)\,dx,\qquad
\int_J L_+(x)G(x)\omega(x)\,dx,
\]

where

\[
\omega(x)=\frac1{|Q(x)|^2\sqrt{|D(x)|}}>0.
\]

The local non-degeneracy needed for this row-space reduction is precisely the
compact chamber condition

\[
q>0,\qquad a>0,\qquad b>0,\qquad W'(u)<0<W'(v),\qquad W''>0
\text{ on }[u,v].
\]

Under these assumptions the variables \((q,a,b,c)\) give full rank in the
singular local block: changing \(q\) changes the logarithmic scale, changing
\((a,b)\) changes the two one-sided endpoint gaps, and changing \(c\) changes
the \(c\)-jet.  No additional exterior density functional is created by the
endpoint zero equations or the stationarity equation.

The compact proof target is therefore sharpened to:

\[
\boxed{
\text{prove the above local elimination rigorously, then apply the oriented
Chebyshev determinant of 16.27 to the four displayed moments.}
}
\]

At this point the determinant side is closed at the mathematical-identity
level.  The remaining proof work is not numerical; it is the finite-dimensional
implicit-function elimination of the local variables \((q,a,b,c)\) from the
endpoint/atom block.

### 16.31 Endpoint pivots and the remaining Schur scalar

The local elimination can be made more explicit.  Put

\[
a=c-u,\qquad b=v-c,\qquad u=c-a,\qquad v=c+b,
\]

and write

\[
A=W'(u),\qquad B=W'(v),\qquad A_2=W''(u),\qquad B_2=W''(v).
\]

The two endpoint equations are

\[
E_-:=q\log\frac1a+W(u)=0,\qquad
E_+:=q\log\frac1b+W(v)=0.
\]

In the variables \((q,a,b,c)\),

\[
dE_-
=
\log\frac1a\,dq
+(-q/a-A)\,da
+A\,dc
+d\Phi(u),
\]

and

\[
dE_+
=
\log\frac1b\,dq
+(-q/b+B)\,db
+B\,dc
+d\Phi(v).
\]

But

\[
U'(u)=q/a+A>0,\qquad
U'(v)=-q/b+B<0.
\]

Therefore the endpoint block has the two non-zero pivots

\[
\frac{\partial E_-}{\partial a}=-U'(u)<0,\qquad
\frac{\partial E_+}{\partial b}=U'(v)<0.
\]

So \(a\) and \(b\) can always be solved locally from the two endpoint
equations in the compact chamber.

The dual zero equation

\[
F(c)=0
\]

has the non-zero \(c\)-pivot

\[
F'(c)=-\int\frac{d\lambda(t)}{(c-t)^2}<0.
\]

Thus \(c\) is also locally eliminable.  After eliminating \(a,b,c\), only the
stationarity equation

\[
S:=aW'(u)+bW'(v)=0
\]

can create a residual local rank failure.

For the pure \(q\)-direction, with the exterior field and \(c\) fixed, the
endpoint equations give

\[
da=\frac{\log(1/a)}{U'(u)}\,dq,\qquad
db=-\frac{\log(1/b)}{U'(v)}\,dq.
\]

Therefore the Schur derivative of stationarity in that direction is

\[
\boxed{
\mathfrak S_q
=
(A-aA_2)\frac{\log(1/a)}{U'(u)}
-
(B+bB_2)\frac{\log(1/b)}{U'(v)}.
}
\]

Since \(U'(v)<0\), the second displayed term is positive in the usual
\((0,1)\)-component regime, while the first is negative.  A cancellation is
not ruled out by convexity alone.  Thus the precise remaining local
non-degeneracy problem is:

\[
\boxed{
\mathfrak S_q\ne0
\text{, or else identify the cancelling case and show it is exactly a
pinching/lower-genus degeneration.}
}
\]

This is a substantial narrowing.  The compact proof no longer asks for an
abstract rank statement.  It asks for a one-scalar Schur complement exclusion,
after three explicit non-zero pivots have already removed the endpoint lengths
and the zero \(c\).

### 16.32 Correction: \(\mathfrak S_q\) is only a sufficient pivot

The scalar \(\mathfrak S_q\) above is the Schur derivative in the pure
\(q\)-direction with the exterior field and \(c\) frozen.  Thus

\[
\mathfrak S_q\ne0
\]

is a convenient sufficient condition for local rank, but it is not necessary.
If \(\mathfrak S_q=0\), the full local block may still have rank because
exterior field variations enter the stationarity equation through
\(\Phi(u),\Phi(v),\Phi'(u),\Phi'(v)\) and through the \(c\)-zero equation.
So the exact target should be the full Schur functional, not only the pure
mass derivative.

Let

\[
\phi_u=d\Phi(u),\qquad \phi_v=d\Phi(v),
\qquad \psi_u=d\Phi'(u),\qquad \psi_v=d\Phi'(v).
\]

The endpoint equations give, after \(dE_-=dE_+=0\),

\[
da
=
\frac{\log(1/a)\,dq+A\,dc+\phi_u}{U'(u)},
\]

and

\[
db
=
-
\frac{\log(1/b)\,dq+B\,dc+\phi_v}{U'(v)}.
\]

The linearised stationarity equation

\[
S=aW'(u)+bW'(v)=0
\]

then has differential

\[
dS
=
(A-aA_2)\,da
+(B+bB_2)\,db
+(aA_2+bB_2)\,dc
+a\psi_u+b\psi_v.
\]

Substituting \(da,db\) gives the full Schur expression

\[
\boxed{
\begin{aligned}
\mathcal S
=&
(A-aA_2)
\frac{\log(1/a)\,dq+A\,dc+\phi_u}{U'(u)}
\\
&-
(B+bB_2)
\frac{\log(1/b)\,dq+B\,dc+\phi_v}{U'(v)}
\\
&+(aA_2+bB_2)\,dc+a\psi_u+b\psi_v .
\end{aligned}
}
\]

Finally, the dual zero equation eliminates \(dc\):

\[
dF(c)+F'(c)\,dc=0,\qquad F'(c)<0,
\]

so

\[
dc=-\frac{dF(c)}{F'(c)}.
\]

Therefore the true remaining local-rank statement is:

\[
\boxed{
\mathcal S
\text{ is not identically zero as a functional of the exterior variation.}
}
\]

The pure scalar \(\mathfrak S_q\) is just the coefficient of \(dq\) in
\(\mathcal S\) before the \(c\)-zero elimination.  If this coefficient does
not vanish, the local block is already full rank.  If it does vanish, the next
available coefficients are those of

\[
\phi_u,\quad \phi_v,\quad \psi_u,\quad \psi_v,\quad dF(c).
\]

Hence cancellation of \(\mathfrak S_q\) is no longer a fatal obstruction.  It
only moves the proof to the remaining field-jet coefficients of the same
Schur functional.

### 16.33 Field-jet kernel form of the full Schur functional

For an exterior signed variation \(\eta\) on \(J\),

\[
\phi_u=\int_J\log\frac1{|u-x|}\,d\eta(x),\qquad
\phi_v=\int_J\log\frac1{|v-x|}\,d\eta(x),
\]

and

\[
\psi_u=\int_J\frac{d\eta(x)}{x-u},\qquad
\psi_v=\int_J\frac{d\eta(x)}{x-v}.
\]

The value \(dF(c)\) is also a Cauchy-type jet at \(c\).  Up to the fixed
positive finite-gap weight \(\omega\), the full Schur functional is therefore
an exterior moment against the kernel

\[
\boxed{
K_{\rm Schur}(x)
=
\alpha_u\log\frac1{|u-x|}
+\alpha_v\log\frac1{|v-x|}
+\beta_u\frac1{x-u}
+\beta_v\frac1{x-v}
+\beta_c\frac1{x-c}
+\alpha_0,
}
\]

with coefficients determined explicitly by
\(a,b,q,A,B,A_2,B_2,U'(u),U'(v),F'(c)\).

This changes the final compact task in an important way.  The four split
kernels \(1,(x-c)^{-1},L_-,L_+\) are the right basis for endpoint increments,
but the full stationarity Schur complement also sees endpoint derivative
kernels \((x-u)^{-1}\) and \((x-v)^{-1}\).  These kernels are still Cauchy
kernels with poles in the same escaping gap, so the oriented total positivity
route remains available.  The correct final Chebyshev family is therefore the
enlarged local jet family

\[
\boxed{
1,\quad (x-u)^{-1},\quad (x-c)^{-1},\quad (x-v)^{-1},
\quad L_-,\quad L_+.
}
\]

This is a better statement than the previous scalar target.  It avoids
pretending that one coefficient must be non-zero, and instead asks for a
strict total-positivity/variation-diminishing lemma for all local field jets
generated by the escaping component.

### 16.34 Why the enlarged family is still a Cauchy-total-positivity problem

The enlarged family does not introduce a new analytic mechanism.  Each member
is generated by the same Cauchy kernel with source parameter in the escaping
gap:

\[
\frac1{x-u},\qquad \frac1{x-c},\qquad \frac1{x-v},
\]

and

\[
L_-(x)=\int_u^c\frac{ds}{x-s},\qquad
L_+(x)=\int_c^v\frac{ds}{x-s}.
\]

Thus \(L_-\) and \(L_+\) are positive averages of the same Cauchy kernel over
the two ordered source intervals \([u,c]\) and \([c,v]\).  The constant
function \(1\) is the Cauchy kernel source at infinity, since

\[
\lim_{y\to\infty} y\frac1{y-x}=1.
\]

Consequently the determinant signs needed for

\[
1,\ (x-u)^{-1},\ (x-c)^{-1},\ (x-v)^{-1},\ L_-,\ L_+
\]

are confluent/averaged Cauchy determinants.  They are obtained from the basic
Cauchy determinant by:

1. letting one source go to infinity to produce the constant column;
2. placing three source atoms at \(u,c,v\);
3. replacing two source atoms by positive averages over the ordered intervals
   \([u,c]\) and \([c,v]\);
4. using Andreief/variation-diminishing multilinearity to integrate the
   determinant over those ordered source variables.

The only subtlety is the same orientation already found in 16.27: because
the source interval straddles \(c\), the ordinary left-to-right order on
\(J=I_1\cup I_2\) must be replaced by the real-oval orientation

\[
\sigma(x)=\operatorname{sgn}(x-c).
\]

So the final compact lemma should be stated as:

\[
\boxed{
\text{The six local jet kernels form an extended strict Chebyshev system on
the oriented real ovals.}
}
\]

This lemma is now the clean mathematical hard mouth.  It is independent of
the finite-gap coefficients \(P,Q\), except for the positive weight
\[
\omega(x)=\frac1{|Q(x)|^2\sqrt{|D(x)|}},
\]

which does not change sign variation.

Once this six-kernel oriented Chebyshev lemma is proved, the full Schur
functional \(\mathcal S\) cannot vanish identically on every exterior
variation without forcing the adjoint \(H=(x-c)G\) to change sign on a real
oval.  That contradicts compact interior positivity and closes the compact
non-pinched branch.

### 16.35 Determinant proof skeleton for the six-kernel lemma

The six-kernel lemma can be reduced to one explicit determinant integral.
For ordered points

\[
x_1<\cdots<x_6,\qquad x_i\notin [u,v],
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

Expanding the two averaged columns gives

\[
\Delta_6
=
\int_u^c\int_c^v
\det
\begin{bmatrix}
1 &(x-u)^{-1}&(x-c)^{-1}&(x-v)^{-1}&(x-s)^{-1}&(x-t)^{-1}
\end{bmatrix}_{x=x_i}
\,dt\,ds .
\]

For every interior pair

\[
u<s<c<t<v,
\]

the five finite source points are strictly ordered.  After a fixed column
permutation, the determinant is a standard Cauchy determinant with one source
at infinity:

\[
\det
\begin{bmatrix}
1 &(x-y_1)^{-1}&\cdots&(x-y_5)^{-1}
\end{bmatrix}_{x=x_i},
\qquad
y_1<\cdots<y_5.
\]

The Cauchy formula gives a fixed non-zero sign:

\[
\det
\begin{bmatrix}
1 &(x-y_1)^{-1}&\cdots&(x-y_5)^{-1}
\end{bmatrix}
=
C
\frac{
\prod_{i<j}(x_j-x_i)\prod_{p<q}(y_q-y_p)
}{
\prod_{i,p}(x_i-y_p)
},
\]

where \(C=\pm1\) is determined only by the chosen column order.  The source
Vandermonde is strictly positive for \(u<s<c<t<v\).  Since each \(x_i\) lies
outside \([u,v]\), the sign of the denominator row factor is

\[
\operatorname{sgn}\prod_{p=1}^5(x_i-y_p)
=
\operatorname{sgn}(x_i-c),
\]

because there are five finite source points in the escaping gap.  Therefore

\[
\boxed{
\left(\prod_{i=1}^6\sigma(x_i)\right)\Delta_6(x_1,\ldots,x_6)
\text{ has one fixed non-zero sign,}
\qquad
\sigma(x)=\operatorname{sgn}(x-c).
}
\]

The integral over \(s,t\) cannot cancel because the integrand has the same
sign for every \(u<s<c<t<v\).  Endpoint coincidences do not matter: the
averaged columns integrate over the open rectangle up to a measure-zero
boundary, and the strict sign survives by positivity of the interior
integration region.

Thus the six local jet kernels are an oriented strict Chebyshev system in the
determinantal sense.  This closes the determinant part of the compact
obstruction at the level of a real-variable lemma.

### 16.36 What still remains after the six-kernel determinant

The determinant lemma does **not** by itself prove the exact lower bound.  It
closes only one local piece:

\[
\text{field-jet moments on a fixed compact non-pinched }g=2\text{ chamber.}
\]

The proof still needs the following two mathematical identifications.

First, the KKT adjoint must be shown to use no density functionals beyond the
six local jet moments.  Sections 16.29--16.33 derive the local formulas, but a
clean written proof still has to state the finite-dimensional variables and
perform the Schur elimination without hiding the period-normalisation row.

Second, the sign-variation contradiction must be stated with the correct
dimension count.  The six-kernel Chebyshev lemma says that a non-zero
function orthogonal to all six moments has at least six oriented sign changes.
To use it, the admissible adjoint polynomial \(H=(x-c)G\) must indeed be
orthogonal to these six moments after all local variables are eliminated.
Then oriented sign changes of \(G\) translate back into forbidden sign changes
of \(H\) on the real density ovals.

So the next exact proof target is:

\[
\boxed{
\text{write the compact KKT adjoint as six moment equations against }
1,(x-u)^{-1},(x-c)^{-1},(x-v)^{-1},L_-,L_+.
}
\]

Once that identity is completed, the determinant proof in 16.35 supplies the
variation-diminishing contradiction.

### 16.37 Review of what has actually been proved in this branch

At this point it is important not to overstate the result.  The work above has
not proved \(L_-=M_*\).  It has proved or reduced the compact part of the
route to much sharper mathematical statements.

What is now closed at the level of ordinary mathematics:

1. The naive three-kernel determinant

\[
1,\quad (x-c)^{-1},\quad \int_u^v\frac{ds}{x-s}
\]

is not reliable, because the factor \(c-s\) changes sign.

2. Splitting at \(c\) gives the correct one-sided kernels

\[
L_-=\int_u^c\frac{ds}{x-s},\qquad
L_+=\int_c^v\frac{ds}{x-s}.
\]

3. The local Schur complement must use the full field-jet family, not only the
single pure-\(q\) scalar \(\mathfrak S_q\).

4. The determinant for the six local jet kernels

\[
1,\quad (x-u)^{-1},\quad (x-c)^{-1},\quad (x-v)^{-1},\quad L_-,\quad L_+
\]

has fixed sign on the oriented real ovals.  This follows from the 6-by-6
Cauchy determinant integral in 16.35.

What is not yet closed:

1. The compact KKT adjoint still has to be written exactly as six orthogonality
conditions against those kernels.

2. The period-normalisation row has to be accounted for inside that six-row
ledger; it cannot be left as a vague "period condition".

3. After the compact \(g=2\) chamber is closed, the proof still needs the
higher-gap induction or degeneration argument showing that no \(g\ge3\)
configuration escapes the \(g=2\) obstruction.

4. The exact value also requires the matching upper construction at \(M_*\).
That construction is already conceptually the one-cut boundary candidate, but
it must be written in the same normalisation as the lower-bound theorem.

Thus the immediate next task is not computation.  It is the six-row KKT
ledger.

### 16.38 Six-row KKT ledger to be proved

Let the exterior first variation of the compact dual density/residue data be
\(\eta\), and write

\[
d\eta(x)=G(x)\omega(x)\,dx
\]

on the two real ovals after clearing the fixed positive weight

\[
\omega(x)=\frac1{|Q(x)|^2\sqrt{|D(x)|}}.
\]

The local variables are

\[
q,\qquad a=c-u,\qquad b=v-c,\qquad c,
\]

and the active local equations are:

\[
E_-=0,\qquad E_+=0,\qquad F(c)=0,\qquad S=0.
\]

Together with total mass and period normalisation, the density part of the
adjoint should yield the following six moment rows:

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

The intended source of each row is:

1. \(R_0\): total mass / residue normalisation at infinity.
2. \(R_c\): the dual zero equation \(F(c)=0\).
3. \(R_-\) and \(R_+\): the two endpoint field increments
   \(\Phi(c)-\Phi(u)\) and \(\Phi(v)-\Phi(c)\).
4. \(R_u\) and \(R_v\): the derivative jets \(\Phi'(u)\) and \(\Phi'(v)\)
   entering the stationarity Schur complement.

The period-normalisation row must be tested after the local variables
\((q,a,b,c)\) are eliminated.  The correct requirement is not literally that
the period equation itself is redundant; it is that its **density part** is
represented by a kernel in the Chebyshev span generated by the six local jet
rows.  This is the only place where a hidden extra kernel could still appear.
Therefore the precise proof obligation is:

\[
\boxed{
\text{show that the density part of the eliminated period row lies in the
kernel span of }1,(x-u)^{-1},(x-c)^{-1},(x-v)^{-1},L_-,L_+.
}
\]

If this kernel-span statement fails, then the six-kernel determinant is not
enough and the correct Chebyshev family must be enlarged by exactly that
missing period kernel.  If it holds, the compact \(g=2\) chamber reduces to
the oriented Chebyshev contradiction already isolated in 16.35.

### 16.39 Next most needed mathematical step

The next step should be the period-row calculation.  In concrete terms, write
the period condition as

\[
\int_{I_1} dU_\eta-\int_{I_2} dU_\eta=0
\]

with the appropriate finite-gap normalization, then express
\(dU_\eta(y)\) on the escaping component using the basis

\[
1,\quad (x-u)^{-1},\quad (x-c)^{-1},\quad (x-v)^{-1},\quad L_-,\quad L_+.
\]

The desired output is an identity of the form

\[
K_{\rm period}(x)
=
\alpha_0+\frac{\alpha_u}{x-u}+\frac{\alpha_c}{x-c}
+\frac{\alpha_v}{x-v}+\alpha_-L_-(x)+\alpha_+L_+(x),
\]

for the density kernel \(K_{\rm period}\) that remains after local
elimination.  The coefficients depend only on the compact finite-gap
parameters.  This is now the highest-value calculation for completing the
exact lower-bound route.  It is the point where the proof either closes the
compact \(g=2\) branch or exposes a specific seventh kernel that must be
added.

### 16.40 Period row: the seventh kernel is real

The period row should not be forced into the six local jet kernels without
checking its geometry.  On a genus-one two-cut curve, the period constraint is
the coefficient of the holomorphic differential

\[
\frac{dz}{w}.
\]

After clearing the common positive density weight

\[
\omega(x)=\frac1{|Q(x)|^2\sqrt{|D(x)|}},
\]

this row is not generated by the local field jets at \(u,c,v\).  It is the
relative oval-normalisation row.  In the real-oval notation it has the form

\[
R_{\rm per}(G)
=
\rho_1\int_{I_1}G(x)\omega(x)\,dx
+\rho_2\int_{I_2}G(x)\omega(x)\,dx,
\]

with non-zero real constants \(\rho_1,\rho_2\) determined by the chosen
period normalisation.  Equivalently, its kernel is the piecewise constant
function

\[
\pi(x)=
\begin{cases}
\rho_1,&x\in I_1,\\
\rho_2,&x\in I_2.
\end{cases}
\]

Modulo the total mass row \(R_0\), this is the oval-balance kernel

\[
\pi_0(x)=
\begin{cases}
1,&x\in I_1,\\
-\theta_{\rm per},&x\in I_2,
\end{cases}
\]

for a non-zero normalising constant \(\theta_{\rm per}\) fixed by the period
normalisation.  The sign convention can be chosen so that
\(\theta_{\rm per}>0\) when the two ovals are given opposite period
orientation.

This explains why the previous six-kernel target was too optimistic.  The
six local jet kernels are analytic functions of \(x\) on each component of
\(\mathbb R\setminus[u,v]\).  If a linear combination of them were piecewise
constant on open subintervals of both ovals, then differentiating would give a
rational function that vanishes on intervals, hence vanishes identically.
Thus the combination would be a single global constant, not an independent
relative oval constant.  Therefore the period row is not generically in the
six-kernel span.

The correct compact row family is:

\[
\boxed{
\pi_0,\quad
1,\quad (x-u)^{-1},\quad (x-c)^{-1},\quad (x-v)^{-1},\quad L_-,\quad L_+.
}
\]

The new kernel \(\pi_0\) is not another Cauchy source.  It is the genus-one
period/oval-balance source.

### 16.41 Correct use of the period row

The seventh row \(\pi_0\) must be recorded in the KKT ledger, but it is not
needed for the Chebyshev contradiction once the six local jet rows are present.
Indeed, the determinant lemma in 16.35 says that

\[
1,\quad (x-u)^{-1},\quad (x-c)^{-1},\quad (x-v)^{-1},\quad L_-,\quad L_+
\]

already form an oriented strict Chebyshev system on the two real ovals.
Therefore, by the standard sign-variation theorem, any non-zero \(G\)
orthogonal to these six rows must have oriented sign variation.

The period row is still important for the correctness of the KKT system: the
compact adjoint must satisfy it because the two-cut curve has one holomorphic
period.  But adding an extra orthogonality condition cannot weaken the
six-row sign-variation conclusion.  Thus the compact contradiction should be
organised as follows:

1. prove the KKT ledger contains the six local jet moment rows and the period
   row \(\pi_0\);
2. apply the six-kernel oriented Chebyshev lemma only to the six local rows;
3. obtain oriented sign variation of \(G\);
4. translate it back to forbidden sign variation of \(H=(x-c)G\) on a real
   density oval.

This correction matters.  We do **not** need to prove that the seven functions
including \(\pi_0\) are an ordinary Chebyshev system.  They are not: \(\pi_0\)
is piecewise constant and locally duplicates the constant row on each oval.
The correct role of \(\pi_0\) is bookkeeping for the period equation, not
determinantal sign control.

### 16.42 Review after the period-row correction

What improved in this step:

1. The period row has been identified as a genuine seventh kernel, the
   oval-balance function \(\pi_0\).
2. The earlier target
   \(K_{\rm period}\in\operatorname{span}\{1,(x-u)^{-1},(x-c)^{-1},
   (x-v)^{-1},L_-,L_+\}\) is no longer the preferred route; it is generically
   false because the period row is a holomorphic/oval mode.
3. The determinant proof in 16.35 remains useful, but only for the six local
   jet rows.
4. The compact \(g=2\) branch now needs a clean KKT row-ledger proof showing
   that the six local jet rows really appear; \(\pi_0\) is an additional
   period row but is not needed in the determinant argument.

The next most needed task is therefore:

\[
\boxed{
\text{prove the compact KKT row ledger: six local jet rows plus the period row }
\pi_0.
}
\]

After that, the six-kernel determinant from 16.35 gives the sign-variation
contradiction, and the compact \(g=2\) branch can be connected back to the
global lower-bound proof.  The later tasks remain: higher-gap
degeneration/induction and the matching upper construction at \(M_*\).

### 16.43 Corrected KKT ledger criterion

There is one more linear-algebra correction.  KKT does not automatically say
that the adjoint density \(G\) is separately orthogonal to six named rows.
What it gives is an annihilator relation after the local variables
\((q,a,b,c)\) are eliminated.  Therefore the correct ledger target is a
rank/equivalence statement about the eliminated density constraint map.

Let

\[
\mathcal R(G)
=
\left(
R_0(G),R_u(G),R_c(G),R_v(G),R_-(G),R_+(G)
\right),
\]

where

\[
\begin{aligned}
R_0(G)&=\int_J G\omega,\qquad
R_u(G)=\int_J\frac{G\omega}{x-u},\\
R_c(G)&=\int_J\frac{G\omega}{x-c},\qquad
R_v(G)=\int_J\frac{G\omega}{x-v},\\
R_-(G)&=\int_JL_-G\omega,\qquad
R_+(G)=\int_JL_+G\omega.
\end{aligned}
\]

The compact KKT elimination must show that the density part of every
admissible tangent variation is constrained exactly by \(\mathcal R\), up to
invertible changes of row coordinates and the extra period row.  Equivalently,
after removing \(q,a,b,c\), the density annihilator contains the annihilator of
\(\mathcal R\):

\[
\boxed{
\mathcal R(G)=0
\quad\Longrightarrow\quad
G\text{ is an admissible density tangent for the local block,}
}
\]

or dually, every compact adjoint \(G\) satisfies

\[
\boxed{
R_0(G)=R_u(G)=R_c(G)=R_v(G)=R_-(G)=R_+(G)=0
}
\]

after an invertible row change.  This is the precise point that must be
proved; it cannot be assumed from KKT notation alone.

The period equation may add the separate row

\[
\int_J\pi_0G\omega.
\]

That row is not used in the six-kernel determinant, but it must be present in
the complete KKT ledger.

The hard part is now sharply stated: prove that the augmented KKT block,
including the objective row \(d\mathcal L=d(v-u)\), has Schur complement row
rank six on the density kernels
\[
1,(x-u)^{-1},(x-c)^{-1},(x-v)^{-1},L_-,L_+.
\]
The objective row is essential: the five constraint rows
\((M,F_c,E_-,E_+,S)\) alone cannot have rank six.  If the augmented rank is
only five, the six-kernel Chebyshev argument does not yet apply; one must
either find the missing independent row or weaken the variation-diminishing
step.

Thus the next proof step is a row-by-row derivation of these six equations
from the KKT first variation.

### 16.44 Row-by-row derivation skeleton

Here is the derivation skeleton that must be filled in cleanly.

Let \(\eta\) be an arbitrary exterior density variation and write its local
field on the escaping component as

\[
\Phi_\eta(y)=\int_J\log\frac1{|y-x|}\,d\eta(x).
\]

Then the six rows arise as follows.

**Mass row.**  The Stieltjes normalisation at infinity fixes total mass:

\[
dM(\eta)=\int_J d\eta(x)=\int_JG(x)\omega(x)\,dx.
\]

This is the row \(1\).

**Zero-at-\(c\) row.**  The dual complementarity equation is \(F(c)=0\).  Its
density part is

\[
dF(c)[\eta]=\int_J\frac{d\eta(x)}{c-x}
=-\int_J\frac{G(x)\omega(x)}{x-c}\,dx.
\]

This supplies the row \((x-c)^{-1}\).

**Endpoint value rows.**  The endpoint equations \(E_-=E_+=0\), after taking
differences through the atom point \(c\), use

\[
\Phi_\eta(c)-\Phi_\eta(u)
=\int_JL_-(x)G(x)\omega(x)\,dx,
\]

and

\[
\Phi_\eta(v)-\Phi_\eta(c)
=\int_JL_+(x)G(x)\omega(x)\,dx.
\]

These supply \(L_-\) and \(L_+\).  The common additive field level is absorbed
by the local atom mass \(q\) and by the endpoint zero equations; it does not
create a new density kernel.

**Endpoint derivative rows.**  The stationarity equation

\[
S=aW'(u)+bW'(v)=0
\]

has density derivative

\[
dS[\eta]\supset
a\Phi_\eta'(u)+b\Phi_\eta'(v)
=
a\int_J\frac{G(x)\omega(x)}{x-u}\,dx
+b\int_J\frac{G(x)\omega(x)}{x-v}\,dx,
\]

after the endpoint lengths \(a,b\) have been eliminated using the non-zero
endpoint pivots.  Since \(a,b>0\), the two endpoint jets appear with
non-degenerate coefficients.  Together with independent variations of
\((a,b)\), they supply the rows \((x-u)^{-1}\) and \((x-v)^{-1}\).

**Period row.**  The genus-one period contributes the separate row \(\pi_0\).
It is recorded in the ledger but is not needed for the six-kernel determinant.

The remaining technical point is to make the phrase "supply the rows"
precise.  A single stationarity equation gives one Schur row, not two
independent endpoint derivative rows by itself.  The claim that both
\((x-u)^{-1}\) and \((x-v)^{-1}\) occur independently must come from the full
Jacobian block involving \(E_-,E_+,S\) and the eliminated variables \(a,b\).
This is exactly the finite-dimensional Schur-complement rank calculation that
still has to be proved.

### 16.45 Review after this step

This step corrects the previous overcomplication.  We do not need a new
seven-function Chebyshev determinant.  The proof should be organised as:

1. derive the KKT density row ledger and prove it contains the six local rows;
2. ignore the extra period row for the sign-variation step, because additional
   orthogonality only strengthens the hypothesis;
3. apply the six-kernel oriented Chebyshev determinant from 16.35;
4. translate sign variation of \(G\) into forbidden sign variation of
   \(H=(x-c)G\).

The next most needed mathematical task is therefore the finite-dimensional
augmented Schur-complement rank lemma, stated without hiding this issue:

\[
\boxed{
\text{the eliminated augmented KKT block }(d\mathcal L,dM,dF_c,dE_-,dE_+,dS)
\text{ has rank six on }
1,(x-u)^{-1},(x-c)^{-1},(x-v)^{-1},L_-,L_+.
}
\]

This is now the smallest remaining compact \(g=2\) mouth.

### 16.46 Obsolete Schur rank-six attempt

The following was the first attempted matrix formulation.  It is useful for
setting notation, but the rank-six conclusion is corrected in 16.47.

The augmented KKT rows should be ordered as

\[
(\mathcal L,M,F_c,E_-,E_+,S)
\]

together with the local variables

\[
(q,a,b,c).
\]

For a density perturbation, record the six local jets

\[
\xi_0,\xi_u,\xi_c,\xi_v,\xi_-,\xi_+
\]

corresponding to

\[
1,\ (x-u)^{-1},\ (x-c)^{-1},\ (x-v)^{-1},\ L_-,\ L_+.
\]

The linearisation has block form

\[
d\mathcal K
=
A\,d(q,a,b,c)+B\,\xi,
\]

where \(d\mathcal K\) denotes the six augmented rows, \(A\) is the
local-variable Jacobian, and \(B\) is the density-jet matrix.  Endpoint pivots
and \(F'(c)<0\) show that a large part of \(A\) has full rank.  The exact
Schur complement is

\[
B_{\rm Schur}
=
B_{\rm free}-A_{\rm free}A_{\rm piv}^{-1}B_{\rm piv}.
\]

The tempting but incorrect target was:

\[
\boxed{
\operatorname{rank}B_{\rm Schur}=6.
}
\]

This cannot be the right statement after eliminating four local variables.
The corrected cokernel formulation is given next.

### 16.47 Correction: Schur rank six is still the wrong linear algebra

The previous subsection still overstates what elimination can do.  There are
six augmented rows but four local variables:

\[
(\mathcal L,M,F_c,E_-,E_+,S)
\quad\text{versus}\quad
(q,a,b,c).
\]

If the local-variable Jacobian \(A\) has rank \(4\), eliminating
\((q,a,b,c)\) leaves a cokernel of dimension

\[
6-4=2.
\]

Therefore the Schur complement cannot produce six independent density moment
constraints.  The correct object is not a \(6\)-row annihilator.  It is a
two-dimensional cokernel of the local block.

Concretely, write

\[
d\mathcal K=A\,d(q,a,b,c)+B\,\xi.
\]

The admissible density constraints after eliminating local variables are
obtained by left-null vectors

\[
\lambda\in\ker A^T.
\]

For each such \(\lambda\), the remaining density row is

\[
\lambda^TB\,\xi.
\]

Thus the actual Schur object is

\[
\boxed{
B_{\rm cok}:=\ker(A^T)\,B,
\qquad
\operatorname{rank}B_{\rm cok}=2
\text{ generically.}
}
\]

This changes the compact proof target.  The six local jet kernels form a
Chebyshev system, but the KKT elimination selects only a two-dimensional
subspace of their span.  One should not claim that \(G\) is orthogonal to all
six kernels.  Instead, the compact adjoint density kernel has the form

\[
K_\lambda(x)
=
\lambda_0
+\frac{\lambda_u}{x-u}
+\frac{\lambda_c}{x-c}
+\frac{\lambda_v}{x-v}
+\lambda_-L_-(x)
+\lambda_+L_+(x),
\]

where the coefficient vector \(\lambda\) lies in the two-dimensional cokernel
selected by the local KKT equations.

The sign-variation tool must therefore be used in the dual Chebyshev way:
non-zero elements of a Chebyshev span have **few zeros**, while the compact
positivity/period conditions force **too many zeros or sign alternations** for
the particular \(K_\lambda\).  This is different from the earlier moment
orthogonality argument.

### 16.48 Correct compact \(g=2\) mouth after the rank correction

The compact proof should now be reorganised as follows.

1. Compute the \(6\times4\) local-variable Jacobian \(A\) for
\[
(\mathcal L,M,F_c,E_-,E_+,S)
\]
against
\[
(q,a,b,c).
\]

2. Compute a basis of the two-dimensional cokernel
\[
\ker A^T.
\]

3. Push this cokernel through the six density jets to obtain a two-dimensional
space
\[
\mathcal K_{\rm adj}
\subset
\operatorname{span}\{1,(x-u)^{-1},(x-c)^{-1},(x-v)^{-1},L_-,L_+\}.
\]

4. Prove that every non-zero
\[
K\in\mathcal K_{\rm adj}
\]
violates the compact positivity/period requirements.  The six-kernel
Chebyshev determinant is still useful here because it controls zeros of
non-zero linear combinations in the ambient six-dimensional span.

The new precise target is:

\[
\boxed{
\text{show that the two-dimensional KKT cokernel subspace }
\mathcal K_{\rm adj}
\text{ contains no admissible sign pattern on the two real ovals.}
}
\]

This is a real correction, not just a rephrasing.  The previous "six moment
orthogonality" target was too strong and not supported by the dimensions of
the local elimination.

### 16.49 Review after the augmented-row correction

This correction is important.  The previous "rank six" statement for five
constraint rows was impossible on linear-algebra grounds, and the follow-up
"rank six after adding \(d\mathcal L\)" was still dimensionally wrong after
eliminating four local variables.  The correct KKT object is now:

\[
\ker A^T B.
\]

The next most needed calculation is therefore explicit:

\[
\boxed{
\text{write }A,\text{ compute }\ker A^T,\text{ and derive the two-dimensional}
\text{ adjoint kernel subspace }\mathcal K_{\rm adj}.
}
\]

After that, the problem becomes a two-dimensional sign-pattern exclusion
inside a six-dimensional Chebyshev span.  This is the current smallest
mathematical hard mouth for closing compact \(g=2\).

### 16.50 Candidate augmented local matrix

The next calculation can be made concrete by choosing a local gauge.  Use
relative endpoint rows, subtracting the common exterior field level at \(c\),
so that the density increments are

\[
\xi_-=\Phi(c)-\Phi(u),\qquad
\xi_+=\Phi(v)-\Phi(c),
\]

rather than the three absolute values \(\Phi(u),\Phi(c),\Phi(v)\).  This is
legitimate because the common additive level is absorbed by the endpoint zero
normalisation and the atom mass \(q\).

With rows ordered as

\[
(\mathcal L,M,F_c,\widetilde E_-,\widetilde E_+,S)
\]

and variables ordered as

\[
(q,a,b,c),
\]

the local-variable block has the expected schematic form

\[
A=
\begin{pmatrix}
0&1&1&0\\
1&0&0&0\\
0&0&0&F'(c)\\
\log(1/a)&-U'(u)&0&A_u\\
\log(1/b)&0&U'(v)&B_v\\
0&A_u-aA_{2,u}&B_v+bB_{2,v}&aA_{2,u}+bB_{2,v}
\end{pmatrix},
\]

where

\[
A_u=W'(u),\qquad B_v=W'(v),\qquad
A_{2,u}=W''(u),\qquad B_{2,v}=W''(v).
\]

The corresponding density-jet columns are ordered as

\[
(\xi_0,\xi_u,\xi_c,\xi_v,\xi_-,\xi_+)
\]

for

\[
1,\ (x-u)^{-1},\ (x-c)^{-1},\ (x-v)^{-1},\ L_-,\ L_+.
\]

In the same gauge, the density block should have schematic form

\[
B=
\begin{pmatrix}
0&0&0&0&0&0\\
1&0&0&0&0&0\\
0&0&-1&0&0&0\\
0&0&0&0&-1&0\\
0&0&0&0&0&1\\
0&a&0&b&0&0
\end{pmatrix}.
\]

Signs in the \(\widetilde E_\pm\) rows depend on whether the row is written as
\(\Phi(c)-\Phi(u)\) or \(\Phi(u)-\Phi(c)\), but this does not affect rank.
The important structural point is that the six density jets enter in six
different rows before local elimination:

1. \(\xi_0\) in mass;
2. \(\xi_c\) in the dual zero;
3. \(\xi_-,\xi_+\) in the two relative endpoint rows;
4. \(\xi_u,\xi_v\) in stationarity;
5. \(\mathcal L\) supplies the extra augmented row needed for a non-trivial
   cokernel.

The next exact algebraic task is now:

\[
\boxed{
\text{compute }\ker A^T\text{ for this }A,\text{ then multiply by }B.
}
\]

This will produce the two-dimensional coefficient subspace
\(\mathcal K_{\rm adj}\).  The signs \(U'(u)>0\), \(U'(v)<0\), \(F'(c)<0\),
and \(a,b>0\) should be used to show that this subspace cannot contain an
admissible compact sign pattern.

### 16.51 Explicit cokernel basis

The symbolic cokernel calculation is now small enough to write down.  Put

\[
p=\log(1/a),\qquad r=\log(1/b),
\]

\[
U_u=U'(u)>0,\qquad U_v=U'(v)<0,\qquad F_c=F'(c)<0,
\]

and keep

\[
A_u=W'(u),\quad B_v=W'(v),\quad A_{2,u}=W''(u),\quad B_{2,v}=W''(v).
\]

For the matrix \(A\) in 16.50, a basis of \(\ker A^T\) pushes through \(B\)
to the following two density-kernel coefficient vectors in the ordered basis

\[
(1,\ (x-u)^{-1},\ (x-c)^{-1},\ (x-v)^{-1},\ L_-,\ L_+).
\]

The first vector is

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

The second vector is

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

Thus

\[
\mathcal K_{\rm adj}
=
\operatorname{span}\{K_1,K_2\},
\]

where \(K_j\) is the corresponding linear combination of the six local jet
kernels.  This replaces the previous vague "rank" target by an explicit
two-dimensional space.

The compact \(g=2\) problem is now:

\[
\boxed{
\text{show no non-zero }sK_1+tK_2
\text{ has the admissible compact sign pattern on }I_1\cup I_2.
}
\]

The six-kernel Chebyshev determinant says every non-zero \(sK_1+tK_2\) has
controlled zero count in the ambient Chebyshev span.  What remains is to
translate the compact positivity/period conditions into a lower bound on the
number of zeros or sign alternations required of \(sK_1+tK_2\).

### 16.52 The next sign-pattern reduction

The adjoint-kernel calculation changes the shape of the compact proof.  We no
longer need to prove six independent moment equations.  We need to prove that
the two-dimensional family

\[
K_{s,t}=sK_1+tK_2
\]

cannot be the first variation of an admissible compact \(g=2\) dual measure.
The useful way to phrase this is as a sign-pattern exclusion.

Let the two compact intervals be

\[
I_1=[u,c],\qquad I_2=[c,v],
\]

with \(u<c<v\).  In the compact branch the exterior potential is flat on the
active intervals and non-negative on the forbidden set.  A one-sided endpoint
motion therefore has a fixed sign: moving an endpoint outward cannot lower the
Lagrangian at first order, while moving it inward cannot improve the active
flatness without violating positivity.  In adjoint language this means that an
admissible \(K_{s,t}\) must have alternating one-sided signs at

\[
u,\ c^-,\ c^+,\ v
\]

after multiplying by the orientation of the corresponding endpoint motion.
The period row gives one more sign reversal: the variation that transfers
density from \(I_1\) to \(I_2\) has zero total period, so \(K_{s,t}\) cannot
keep a single sign on both ovals unless it is orthogonal to a positive measure
on each oval.  Since the period weights are positive, that forces at least one
interior zero on each oval.

Thus the compact branch would imply the following lower bound:

\[
\boxed{
K_{s,t}\not\equiv0
\quad\Longrightarrow\quad
K_{s,t}\text{ has at least six alternating real zeros counted with the oval
orientations.}
}
\]

The six zeros are:

1. one sign change forced by the left endpoint \(u\);
2. one zero inside \(I_1\) from the period balance;
3. one sign change at \(c^-\);
4. one sign change at \(c^+\);
5. one zero inside \(I_2\) from the period balance;
6. one sign change forced by the right endpoint \(v\).

This is the exact mathematical mouth that remains.  To close it one needs the
following Chebyshev lemma in the local six-kernel span:

\[
\boxed{
\text{No non-zero element of }
\operatorname{span}\{K_1,K_2\}
\text{ can have the above six alternating oval zeros.}
}
\]

The ambient six-kernel Chebyshev determinant is not by itself enough, because
six zeros are possible for a general six-dimensional span.  The extra saving
must come from the special two-dimensional coefficient surface
\(\operatorname{span}\{\kappa_1,\kappa_2\}\).  Concretely, the next proof must
show that the ratio

\[
R(x)=\frac{K_1(x)}{K_2(x)}
\]

is strictly monotone on each oval after the correct orientation, and that the
two oriented ranges overlap in the wrong order.  If this is proved, then a
single value \(-t/s\) cannot be assumed once on each of the six required
alternation slots, so no admissible compact \(g=2\) branch exists.

The remaining compact proof is therefore reduced to three purely mathematical
lemmas:

\[
\begin{aligned}
\text{(A) endpoint sign lemma: }&
\text{ admissibility fixes the four oriented endpoint signs;}\\
\text{(B) period-zero lemma: }&
\text{ positivity of the period weights forces one interior zero on each oval;}\\
\text{(C) adjoint ratio lemma: }&
R=K_1/K_2\text{ is oriented-monotone with incompatible oval ranges.}
\end{aligned}
\]

This is progress because it removes the earlier vague "rank" target.  The
hardest remaining item is now exactly lemma (C).  It should be attacked by
writing the Wronskian

\[
K_1K_2'-K_1'K_2
\]

over the common denominator

\[
(x-u)^2(x-c)^2(x-v)^2
\]

plus the two logarithmic primitives \(L_\pm\), then using the stationarity
relations to cancel the removable endpoint factors.  After cancellation, the
desired sign should be a low-degree rational inequality with coefficients
controlled by

\[
U_u>0,\quad U_v<0,\quad F_c<0,\quad a,b>0,\quad W''>0.
\]

If the Wronskian sign cannot be forced under these hypotheses, then this
compact \(g=2\) line is not yet a complete exact-value proof; it will need an
additional extremality relation, most likely the second-variation positivity
of the two-interval Cauchy-transform ansatz.

### 16.53 Wronskian normal form

The Wronskian calculation has a useful general normal form.  Write

\[
K_1=R_1+\alpha L_-+\beta L_+,\qquad
K_2=R_2+\gamma L_-+\delta L_+,
\]

where \(R_1,R_2\) are rational combinations of

\[
1,\ (x-u)^{-1},\ (x-c)^{-1},\ (x-v)^{-1}.
\]

In the present cokernel basis,

\[
\alpha=\frac{U_v}{U_u},\qquad \beta=1,\qquad
\gamma=\frac{-A_u+aA_{2,u}+B_v+bB_{2,v}}{U_u},\qquad \delta=0.
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

has no \(L_-L_+\), \(L_-^2\), or \(L_+^2\) terms.  It is exactly

\[
\boxed{
W_{12}=C_0(x)+C_-(x)L_-(x)+C_+(x)L_+(x),
}
\]

with

\[
\begin{aligned}
C_-(x)
&=\alpha R_2'(x)-\gamma R_1'(x)
  +(\alpha\delta-\beta\gamma)L_+'(x),\\
C_+(x)
&=\beta R_2'(x)-\delta R_1'(x)
  +(\beta\gamma-\delta\alpha)L_-'(x),\\
C_0(x)
&=R_1R_2'-R_1'R_2
  +R_1(\gamma L_-'+\delta L_+')
  -R_2(\alpha L_-'+\beta L_+').
\end{aligned}
\]

For this basis \(\delta=0\), hence the two logarithmic coefficients simplify to

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

This is a stronger reduction than the previous informal Wronskian target:
only two rational coefficient functions control the logarithmic obstruction.
Therefore the next hand proof should first try to show that, after substituting
the explicit \(R_1,R_2,\alpha,\beta,\gamma\), both \(C_-\) and \(C_+\) have the
same oriented sign on the two ovals.  If that succeeds, the remaining
non-logarithmic term \(C_0\) can be bounded by the endpoint values of
\(L_\pm\) and the removable endpoint cancellations.

The key unresolved mathematical question is now precise:

\[
\boxed{
\text{Do stationarity and }W''>0\text{ force the signs of }
C_-,C_+,C_0\text{ needed for }W_{12}\text{ to have one sign?}
}
\]

If yes, the compact \(g=2\) branch closes by the ratio-monotonicity lemma.  If
not, the current two-dimensional adjoint kernel is missing one more algebraic
relation, probably the second-variation inequality.

### 16.54 Explicit logarithmic coefficients and the new obstruction

The two logarithmic Wronskian coefficients can now be written without any
large determinant expansion.  Put

\[
\Gamma=\frac{-A_u+aA_{2,u}+B_v+bB_{2,v}}{U_u},
\]

and

\[
Q_c=
\frac{
A_u^2-A_uaA_{2,u}-A_uB_v-A_ubB_{2,v}
+aA_{2,u}U_u+bB_{2,v}U_u
}{F_cU_u}.
\]

Then

\[
R_2(x)=
\frac{p(-A_u+aA_{2,u}+B_v+bB_{2,v})}{U_u}
+\frac{a}{x-u}+\frac{Q_c}{x-c}+\frac{b}{x-v},
\]

so

\[
\boxed{
C_+(x)=
-\frac{a}{(x-u)^2}
-\frac{Q_c}{(x-c)^2}
-\frac{b}{(x-v)^2}
+\Gamma\left(\frac1{x-u}-\frac1{x-c}\right).
}
\]

Similarly, write

\[
P_c=-\frac{A_uU_v-B_vU_u}{F_cU_u},\qquad
\Alpha=\frac{U_v}{U_u}<0.
\]

Since

\[
R_1(x)=\frac{-U_ur+U_vp}{U_u}+\frac{P_c}{x-c},
\]

we get

\[
\boxed{
C_-(x)=
\Alpha\left(
-\frac{a}{(x-u)^2}
-\frac{Q_c}{(x-c)^2}
-\frac{b}{(x-v)^2}
\right)
+\Gamma\frac{P_c}{(x-c)^2}
-\Gamma\left(\frac1{x-c}-\frac1{x-v}\right).
}
\]

This is the first point where the compact route becomes visibly non-trivial.
The signs of \(a,b,U_u,U_v,F_c\) alone do not determine the signs of
\(\Gamma,Q_c,P_c\).  Therefore a proof of Wronskian monotonicity cannot come
from the basic orientation inequalities only.  It must use at least one of the
stationarity equations in a sharper form.

The required stationarity strengthening should be:

\[
\boxed{
Q_c\ge0,\qquad
\Gamma\left(\frac1{x-u}-\frac1{x-c}\right)
\le
\frac{a}{(x-u)^2}+\frac{Q_c}{(x-c)^2}
\quad (x\in I_1),
}
\]

and the analogous right-oval inequality

\[
\boxed{
Q_c\ge0,\qquad
-\Gamma\left(\frac1{x-c}-\frac1{x-v}\right)
\le
\frac{Q_c}{(x-c)^2}+\frac{b}{(x-v)^2}
\quad (x\in I_2).
}
\]

If these two inequalities hold, then \(C_+\le0\) on the left oval and the
corresponding oriented \(C_-\) inequality holds on the right oval, giving the
first half of the ratio-monotonicity proof.

This reveals the next exact hard lemma:

\[
\boxed{
\text{derive the two displayed one-oval inequalities from endpoint
stationarity and }W''>0.
}
\]

Equivalently, the compact ansatz must imply that \(\Gamma\) is not an
independent parameter; it is bounded by the convex endpoint curvatures
\(aA_{2,u}\) and \(bB_{2,v}\).  Without that curvature control, \(C_\pm\) can
change sign and the ratio-monotonicity route does not close.

### 16.55 Curvature clamp for the one-oval inequalities

The one-oval inequalities in 16.54 have an exact elementary reduction.  On
\(I_1=(u,c)\), put

\[
A=x-u>0,\qquad B=c-x>0,\qquad d_-=c-u.
\]

Then \(A+B=d_-\) and

\[
\frac1{x-u}-\frac1{x-c}=\frac1A+\frac1B=\frac{d_-}{AB}.
\]

Thus

\[
\Gamma\left(\frac1{x-u}-\frac1{x-c}\right)
\le
\frac{a}{(x-u)^2}+\frac{Q_c}{(x-c)^2}
\]

for every \(x\in I_1\) is equivalent, when \(Q_c\ge0\), to

\[
\Gamma d_-AB\le aB^2+Q_cA^2
\qquad(A,B>0,\ A+B=d_-).
\]

The sharp lower bound

\[
\inf_{A,B>0}
\frac{aB^2+Q_cA^2}{d_-AB}
=\frac{2\sqrt{aQ_c}}{d_-}
\]

gives the exact condition

\[
\boxed{
\Gamma\le \frac{2\sqrt{aQ_c}}{c-u}.
}
\]

If \(\Gamma\le0\), the left-oval inequality is automatic; the displayed bound
is the sharp positive-\(\Gamma\) condition.

Similarly, on \(I_2=(c,v)\), with

\[
A=x-c>0,\qquad B=v-x>0,\qquad d_+=v-c,
\]

the right-oval inequality is equivalent to

\[
-\Gamma\le \frac{2\sqrt{bQ_c}}{v-c}.
\]

Therefore the two one-oval logarithmic coefficient bounds collapse to the
single curvature clamp

\[
\boxed{
Q_c\ge0,\qquad
-\frac{2\sqrt{bQ_c}}{v-c}
\le \Gamma \le
\frac{2\sqrt{aQ_c}}{c-u}.
}
\]

This is the cleanest mathematical formulation reached so far.  It says that
the compact \(g=2\) branch will close by the Wronskian-ratio route if endpoint
stationarity and second variation imply the curvature clamp above, together
with the remaining rational term \(C_0\) endpoint cancellation.

This also gives a precise failure test.  If the actual finite-gap
stationarity equations allow \(\Gamma\) outside this interval, then the current
two-dimensional adjoint-ratio argument cannot prove monotonicity; one must add
the second-variation inequality as an independent condition rather than hoping
it is hidden inside first-order stationarity.

### 16.56 Curvature clamp as a second-variation discriminant

The clamp in 16.55 is exactly the form of a \(2\times2\) second-variation
condition.  This is the right mathematical interpretation.

For the left oval, the inequality

\[
\Gamma d_-AB\le aB^2+Q_cA^2,\qquad A+B=d_-=c-u,
\]

is the positivity of the quadratic form

\[
\boxed{
\mathcal Q_-(A,B)=aB^2-\Gamma d_-AB+Q_cA^2.
}
\]

Since \(A,B\) are arbitrary positive endpoint barycentric coordinates on
\((u,c)\), positivity for every interior point is equivalent to

\[
\boxed{
Q_c\ge0,\qquad \Gamma^2d_-^2\le4aQ_c
\quad\text{when }\Gamma>0.
}
\]

This is just the non-positive discriminant condition for \(\mathcal Q_-\).
Thus the left half of the curvature clamp is not an independent analytic
estimate; it is the statement that the second variation is non-negative on the
two-dimensional perturbation spanned by:

1. moving the left endpoint mass/edge coordinate with weight \(B\);
2. moving the central neck coordinate with weight \(A\).

The right oval gives the analogous quadratic form

\[
\boxed{
\mathcal Q_+(A,B)=bB^2+\Gamma d_+AB+Q_cA^2,
\qquad d_+=v-c,
}
\]

and positivity is equivalent to

\[
\boxed{
Q_c\ge0,\qquad \Gamma^2d_+^2\le4bQ_c
\quad\text{when }\Gamma<0.
}
\]

Therefore the complete curvature clamp is precisely:

\[
\boxed{
\mathcal Q_-\ge0\text{ on the left barycentric cone and }
\mathcal Q_+\ge0\text{ on the right barycentric cone.}
}
\]

This identifies the missing proof ingredient.  The compact branch must supply
not merely first-order KKT stationarity, but the two scalar second-variation
inequalities

\[
\Delta_-:=4aQ_c-\Gamma^2(c-u)^2\ge0
\quad(\Gamma>0),
\]

and

\[
\Delta_+:=4bQ_c-\Gamma^2(v-c)^2\ge0
\quad(\Gamma<0).
\]

If \(\Gamma\) has the opposite sign, the corresponding one-oval inequality is
automatic and no discriminant condition is needed on that side.

This is a useful correction to the previous plan.  The Wronskian route cannot
be closed from first-order stationarity alone.  It should be closed by the
standard extremal principle:

\[
\boxed{
\text{compact finite-gap extremizers have non-negative second variation under
endpoint/neck perturbations.}
}
\]

The next exact task is to write those endpoint/neck perturbations in the
Cauchy-transform variables and show that their Hessian entries are exactly
\((a,Q_c,\Gamma d_-)\) and \((b,Q_c,-\Gamma d_+)\) up to a positive common
normalisation.  Once that identification is made, the curvature clamp follows
from positive semidefiniteness.

### 16.57 Endpoint/neck Hessian block to prove

The Hessian identification can be stated without choosing a numerical
certificate.  Let \(\theta_-\) be the left endpoint-transfer coordinate and
\(\zeta\) the neck coordinate at \(c\).  The correct local second-variation
statement is:

\[
\boxed{
\delta^2\mathcal L(\theta_-,\zeta)
=
\lambda_-
\left(a\theta_-^2-\Gamma(c-u)\theta_-\zeta+Q_c\zeta^2\right),
\qquad \lambda_->0.
}
\]

Similarly, for the right endpoint-transfer coordinate \(\theta_+\),

\[
\boxed{
\delta^2\mathcal L(\theta_+,\zeta)
=
\lambda_+
\left(b\theta_+^2+\Gamma(v-c)\theta_+\zeta+Q_c\zeta^2\right),
\qquad \lambda_+>0.
}
\]

This is now the concrete theorem that should replace the vague phrase
"second variation positivity."  The entries have a clear origin:

1. \(a\) and \(b\) are the endpoint mass/edge coefficients.  They are positive
   because the compact density has positive edge weight at the two moving
   endpoint modes.
2. \(Q_c\) is the Schur-complement curvature in the neck coordinate after
   eliminating the local variables \((q,a,b,c)\).
3. \(\Gamma(c-u)\) and \(-\Gamma(v-c)\) are the mixed endpoint-neck terms.  The
   factors \(c-u\) and \(v-c\) come from converting the pointwise Cauchy kernel
   difference
   \[
   \frac1{x-u}-\frac1{x-c}
   \quad\text{or}\quad
   \frac1{x-c}-\frac1{x-v}
   \]
   into barycentric endpoint coordinates.

Once these two Hessian identities are proved, the proof of the logarithmic
Wronskian sign is short:

\[
\delta^2\mathcal L\ge0
\quad\Rightarrow\quad
\mathcal Q_\pm\ge0
\quad\Rightarrow\quad
\text{curvature clamp}
\quad\Rightarrow\quad
C_\pm\text{ have the required oriented signs.}
\]

The remaining algebraic check is whether the Schur-complement coefficient
called \(Q_c\) in the cokernel basis is exactly the neck Hessian coefficient,
or differs by a positive normalising factor.  If it differs by a positive
factor, all inequalities survive after rescaling.  If the factor changes sign,
then the current gauge for \(F_c\) is oriented incorrectly and must be flipped.

Thus the next hand calculation is:

\[
\boxed{
\text{compute the Schur complement of the local KKT block in the neck
coordinate and compare it with }Q_c.
}
\]

The \(A\)-matrix from 16.50 is still needed, but it cannot by itself be the
Hessian.  It is the first-variation constraint Jacobian.  The second-variation
calculation needs the bordered Hessian obtained by adjoining the second
derivatives of the finite-gap Lagrangian in the endpoint/neck variables.

### 16.58 Correction: the first-order block is not the Hessian

This is an important correction.  The local matrix \(A\) in 16.50 records the
linearised constraints:

\[
d\mathcal K=A\,dy+B\,d\xi .
\]

It determines the cokernel

\[
\ker(A^T)B
\]

and hence the adjoint two-dimensional space
\(\mathcal K_{\rm adj}\).  It does not determine the second variation.  The
curvature clamp requires the second derivative of the reduced Lagrangian, so
the correct object is a bordered Hessian:

\[
\boxed{
\mathsf H_{\rm bord}
=
\begin{pmatrix}
\mathsf H_{yy}&A^T\\
A&0
\end{pmatrix},
}
\]

where \(y=(q,a,b,c)\), and \(\mathsf H_{yy}\) is the genuine second derivative
matrix of the finite-gap Lagrangian in the local variables.  After eliminating
the constrained local variables, the effective second variation in the
endpoint/neck directions is a Schur complement:

\[
\boxed{
\mathsf H_{\rm eff}
=
\mathsf H_{\xi\xi}
-\mathsf H_{\xi y}\mathsf H_{yy}^{-1}\mathsf H_{y\xi}
\quad\text{inside the tangent space }d\mathcal K=0.
}
\]

Equivalently, one may compute it through the bordered inverse of
\(\mathsf H_{\rm bord}\).  The previous phrase "view the same \(A\)-matrix as a
Hessian block" was too strong; the correct statement is:

\[
\boxed{
A\text{ supplies the constraints for the Schur complement; }
\mathsf H_{yy},\mathsf H_{\xi y},\mathsf H_{\xi\xi}
\text{ supply the curvature.}
}
\]

This correction matters because \(Q_c\) and \(\Gamma\) have only been obtained
from the first-order cokernel calculation so far.  To prove the curvature
clamp mathematically, one must show that the same combinations occur in the
reduced bordered Hessian.  That is a nontrivial second-order identity, not a
consequence of \(A\) alone.

### 16.59 Minimal second-order data needed

The proof now needs exactly three reduced Hessian entries.  Let
\(\theta_-\), \(\theta_+\), and \(\zeta\) denote respectively the left
endpoint-transfer, right endpoint-transfer, and neck coordinates.  The
required reduced Hessian entries are:

\[
\boxed{
\mathsf H_{\theta_-\theta_-}=\lambda_-a,\qquad
\mathsf H_{\zeta\zeta}=\lambda_-Q_c,\qquad
2\mathsf H_{\theta_-\zeta}=-\lambda_-\Gamma(c-u)
}
\]

for the left block, and

\[
\boxed{
\mathsf H_{\theta_+\theta_+}=\lambda_+b,\qquad
\mathsf H_{\zeta\zeta}=\lambda_+Q_c,\qquad
2\mathsf H_{\theta_+\zeta}=\lambda_+\Gamma(v-c)
}
\]

for the right block, with \(\lambda_\pm>0\).  These six scalar identities are
the whole missing Hessian identification.

The diagonal endpoint entries are the easiest: in the Cauchy-transform
normalisation, moving an endpoint edge mode differentiates the simple pole
coefficient at that endpoint, so positivity of the compact density gives the
positive weights \(a\) and \(b\).

The neck diagonal entry is the real issue.  It must be shown that after
eliminating \(q,a,b,c\), the second derivative in the neck coordinate equals
the same Schur coefficient \(Q_c\) that appears in the cokernel vector
\(\kappa_2\), up to positive orientation.

The mixed entries are the second issue.  The endpoint/neck cross derivative
should be the first-order change of the neck equation under endpoint transfer;
after barycentric rescaling this is exactly the coefficient \(\Gamma(c-u)\) on
the left and \(-\Gamma(v-c)\) on the right.

Thus the next mathematical proof has three subclaims:

\[
\begin{aligned}
\text{(H1)}\quad&\text{endpoint diagonal }=a,b;\\
\text{(H2)}\quad&\text{neck diagonal }=Q_c;\\
\text{(H3)}\quad&\text{endpoint-neck mixed terms }=\mp\Gamma d_\pm.
\end{aligned}
\]

If H1-H3 are proved, positive semidefiniteness of the reduced Hessian gives
the curvature clamp from 16.55, and the logarithmic Wronskian obstruction is
closed.

This is now the current smallest honest hard mouth.  It is also the right
place to stop using first-order rank language: the remaining gap is a
second-order Schur-complement identity.

### 16.60 What part of H1-H3 is already mathematical

Among H1-H3, H1 is not a serious obstruction.  The endpoint-transfer
coordinate is a square-root edge displacement.  In the Cauchy-transform
normalisation, the compact density near a regular endpoint has the local form

\[
\rho(x)\,dx
=
\sigma_u\sqrt{x-u}\,dx
\quad\text{near }u,
\qquad
\rho(x)\,dx
=
\sigma_v\sqrt{v-x}\,dx
\quad\text{near }v,
\]

with \(\sigma_u,\sigma_v>0\).  Moving the endpoint by a square-root coordinate
\(\theta\) changes the active interval only to second order, and the second
variation is the positive edge coefficient times \(\theta^2\).  After matching
the local Cauchy normalisation used in 16.50, these edge coefficients are
precisely the positive endpoint weights called \(a\) and \(b\).  Thus H1 is
the standard endpoint-edge positivity:

\[
\boxed{
\mathsf H_{\theta_-\theta_-}>0,\qquad
\mathsf H_{\theta_+\theta_+}>0,
}
\]

and, after normalisation,

\[
\mathsf H_{\theta_-\theta_-}=\lambda_-a,\qquad
\mathsf H_{\theta_+\theta_+}=\lambda_+b.
\]

The real remaining proof is therefore H2-H3:

\[
\boxed{
\text{identify the neck diagonal as }Q_c
\text{ and the endpoint-neck mixed terms as }\mp\Gamma d_\pm.
}
\]

This is important because it prevents a false closure.  Endpoint positivity
alone only gives the diagonal \(a,b>0\).  It does not control \(\Gamma\).
Control of \(\Gamma\) requires the mixed endpoint-neck Hessian entries, and
control of \(Q_c\) requires the neck diagonal Schur complement.

The next best calculation is consequently:

1. write the neck perturbation as the local variation that changes the common
   level at \(c\) while preserving mass and the endpoint flatness equations;
2. solve the first-order constraints using the same \(A\)-block;
3. evaluate the second derivative of the Lagrangian along this solved tangent
   vector;
4. compare the resulting coefficient with \(Q_c\);
5. repeat with one endpoint-transfer coordinate added to get the mixed
   coefficient \(\Gamma d_\pm\).

This is exactly where the full exact-value proof still needs work.  Once H2
and H3 are proved, the compact \(g=2\) obstruction is no longer a numerical
or heuristic statement; it becomes a standard Hessian positive-semidefinite
argument.

### 16.61 Tangent-space correction for the neck coordinate

There is another important correction before computing H2-H3.  A "pure neck
jet" is not automatically a valid first-order perturbation.  The linearised
constraints are

\[
A\,dy+B\,d\xi=0.
\]

Thus a density-side perturbation \(d\xi\) is tangent only if it is annihilated
by the adjoint cokernel:

\[
\boxed{
\langle \kappa_1,d\xi\rangle=0,\qquad
\langle \kappa_2,d\xi\rangle=0.
}
\]

Equivalently,

\[
d\xi\in\ker((\ker A^T)B).
\]

This means that none of the six elementary density jets

\[
\xi_0,\xi_u,\xi_c,\xi_v,\xi_-,\xi_+
\]

should be used alone as a solved tangent coordinate.  In particular, the neck
coordinate is not simply "turn on \(\xi_c\)."  It must be the projection of the
neck direction to the four-dimensional first-order tangent space.

The correct procedure is:

1. choose four free density-side coordinates;
2. solve the two compatibility equations
   \[
   \langle \kappa_1,d\xi\rangle=0,\qquad
   \langle \kappa_2,d\xi\rangle=0
   \]
   for the two dependent density jets;
3. solve \(A\,dy=-B\,d\xi\) for the local variables \(dy\);
4. compute the second variation on this solved tangent vector.

A convenient gauge is to take

\[
(\xi_u,\xi_v,\xi_-,\xi_+)
\]

as free and solve for

\[
(\xi_0,\xi_c).
\]

This gauge keeps the two endpoint-transfer directions visible while allowing
the neck coordinate to be represented by a constrained combination of
\(\xi_-\) and \(\xi_+\).  In this gauge, the neck direction should be the
anti-symmetric transfer between the two relative endpoint rows:

\[
\zeta:\qquad \xi_-=-1,\qquad \xi_+=1,
\]

with \(\xi_0,\xi_c\) then determined by the two compatibility equations.  The
endpoint-transfer directions are represented by the \(\xi_u\) and \(\xi_v\)
coordinates, again with \(\xi_0,\xi_c\) solved.

This correction is essential.  The Hessian entries H2-H3 must be computed
after this tangent projection.  Otherwise \(Q_c\) and \(\Gamma\) can be
misidentified by adding forbidden normal components.

The next exact calculation is therefore not "differentiate in \(\xi_c\)."  It
is:

\[
\boxed{
\text{write the projected tangent basis }
T_u,T_v,T_\zeta
\text{ in the }(\xi_0,\xi_u,\xi_c,\xi_v,\xi_-,\xi_+)\text{ coordinates.}
}
\]

Only after this projection should one compare the reduced Hessian entries with
\(Q_c\) and \(\Gamma\).

### 16.62 Projected tangent basis in determinant form

The tangent projection can be written cleanly without expanding all
coefficients.  Write

\[
\kappa_j=(\kappa_{j0},\kappa_{ju},\kappa_{jc},
\kappa_{jv},\kappa_{j-},\kappa_{j+})
\qquad(j=1,2),
\]

and set

\[
D=\kappa_{10}\kappa_{2c}-\kappa_{1c}\kappa_{20}.
\]

Assume \(D\ne0\).  This is the non-degenerate compact chart in which
\((\xi_0,\xi_c)\) can be solved from the two compatibility equations.

For a free vector

\[
h=(h_u,h_v,h_-,h_+)
\]

meaning

\[
\xi_u=h_u,\qquad \xi_v=h_v,\qquad \xi_-=h_-,\qquad \xi_+=h_+,
\]

define

\[
R_j(h)=\kappa_{ju}h_u+\kappa_{jv}h_v+\kappa_{j-}h_-+\kappa_{j+}h_+.
\]

Then the unique tangent lift is

\[
\boxed{
\xi_0(h)=\frac{-R_1(h)\kappa_{2c}+\kappa_{1c}R_2(h)}{D},
}
\]

and

\[
\boxed{
\xi_c(h)=\frac{-\kappa_{10}R_2(h)+\kappa_{20}R_1(h)}{D}.
}
\]

Thus the projected tangent vector is

\[
T(h)=
(\xi_0(h),h_u,\xi_c(h),h_v,h_-,h_+).
\]

The three directions needed for H2-H3 are now concrete:

\[
T_u=T(1,0,0,0),\qquad
T_v=T(0,1,0,0),
\]

and

\[
\boxed{
T_\zeta=T(0,0,-1,1).
}
\]

The projected neck direction \(T_\zeta\) is the correct object for computing
the neck diagonal Hessian.  It is not the elementary vector \(e_c\).

This determinant form also explains why the previous first-order cokernel
calculation is still useful.  The same coefficients \(\kappa_1,\kappa_2\)
define the tangent chart.  What remains genuinely second-order is the pullback
of the bordered Hessian to the three tangent vectors:

\[
\boxed{
H_{ij}^{\rm red}=
T_i^T\,\mathsf H_{\rm eff}\,T_j,
\qquad
i,j\in\{u,v,\zeta\}.
}
\]

The target identities H2-H3 now become:

\[
H_{\zeta\zeta}^{\rm red}=\lambda Q_c,\qquad
H_{u\zeta}^{\rm red}=-\frac{\lambda}{2}\Gamma(c-u),\qquad
H_{v\zeta}^{\rm red}=\frac{\lambda}{2}\Gamma(v-c),
\]

with positive normalisation \(\lambda\) after matching the left/right endpoint
charts.  This is the exact algebraic form of the remaining proof.

### 16.63 Pullback criterion for the missing Hessian calculation

The remaining second-order calculation can be isolated in one matrix identity.
Let \(G\) denote the reduced second-variation form on the six density jets
after the local variables \(y=(q,a,b,c)\) have been eliminated by the bordered
Hessian.  Thus \(G\) is the symmetric form satisfying

\[
\delta^2\mathcal L(d\xi)=d\xi^T G\,d\xi
\]

for tangent density perturbations.

Let \(P\) be the \(6\times4\) tangent-lift matrix defined by 16.62:

\[
T(h)=P h,\qquad h=(h_u,h_v,h_-,h_+).
\]

Then the true four-dimensional tangent Hessian is

\[
\boxed{
M=P^TGP.
}
\]

The three vectors used above are the columns/combinations

\[
e_u=(1,0,0,0),\qquad e_v=(0,1,0,0),\qquad
e_\zeta=(0,0,-1,1).
\]

Therefore H2-H3 are equivalent to the following three scalar identities:

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

This is a useful stopping point because it separates the first-order and
second-order parts cleanly:

1. \(P\) is already determined by the cokernel calculation.
2. \(G\) is the only missing object.
3. Once \(G\) is known, the curvature clamp is a finite algebraic consequence
   of \(M=P^TGP\).

The next proof step must therefore produce \(G\) from the logarithmic
potential Lagrangian.  In potential-theoretic terms, \(G\) should be the
second derivative of the finite-gap dual energy under changes of the local
Cauchy data:

\[
\delta^2\mathcal L
=
\iint -\log|x-y|\,d(\delta\nu)(x)d(\delta\nu)(y)
+\text{endpoint and constraint curvature terms}.
\]

After the KKT constraints are imposed, all normal components are removed by
the bordered Schur complement; the remaining tangent form is \(G\).

Thus the proof has been reduced to the following exact theorem:

\[
\boxed{
\textbf{Reduced Hessian theorem.}\quad
\text{For the compact two-interval extremal ansatz, the reduced jet Hessian }
G\text{ satisfies the three pullback identities above.}
}
\]

If this theorem is proved, then:

\[
G\succeq0
\Rightarrow
M\succeq0
\Rightarrow
\text{curvature clamp}
\Rightarrow
\text{Wronskian log-part sign}
\Rightarrow
\text{compact }g=2\text{ branch excluded.}
\]

This also makes clear what has not yet been proved.  The current notes have
not derived \(G\) from the finite-gap Lagrangian.  They have reduced the
remaining mathematical problem to that derivation.  The next calculation should
therefore start from the Cauchy-transform energy formula and compute the
second derivative with respect to the six jet coordinates, before applying the
projection \(P\).

### 16.64 Decomposition of the reduced Hessian \(G\)

The reduced Hessian \(G\) should be decomposed before attempting any long
formula.  For a tangent variation \(\delta\nu\) of the compact dual measure,
the second variation has three contributions:

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

is the direct logarithmic energy term.  In the compact finite-gap regime this
term is the source of the Hessian positive-semidefinite structure after the
usual dual sign convention.

The edge term \(\mathcal E_{\rm edge}\) contains the square-root endpoint
curvatures.  It is responsible for the diagonal endpoint entries \(a\) and
\(b\).  This is the H1 part already isolated in 16.60.

The Schur term \(\mathcal E_{\rm Schur}\) is the correction obtained by solving
the first-order constraints for the local variables \(y=(q,a,b,c)\).  In block
form, if the raw second variation in \((y,\xi)\) variables is

\[
\begin{pmatrix}
H_{yy}&H_{y\xi}\\
H_{\xi y}&H_{\xi\xi}
\end{pmatrix},
\]

then the eliminated density-side Hessian has the form

\[
\boxed{
G=H_{\xi\xi}-H_{\xi y}H_{yy}^{-1}H_{y\xi}
}
\]

when \(H_{yy}\) is invertible in the chosen chart, and otherwise the same
expression is interpreted as the bordered Schur complement.

This decomposition gives the right proof strategy:

1. prove that \(\mathcal E_{\log}+\mathcal E_{\rm edge}\) supplies the
   positive-semidefinite form on tangent variations;
2. compute \(\mathcal E_{\rm Schur}\) in the local variables;
3. show that after projection by \(P\), the entries involving \(T_\zeta\) are
   precisely \(Q_c\) and \(\Gamma d_\pm\).

The important mathematical point is that \(Q_c\) is expected to be a
Schur-complement coefficient, not a raw logarithmic-energy coefficient.  This
explains why it appeared in \(\kappa_2\): \(\kappa_2\) is already an eliminated
first-order object.  The same elimination must appear again in the second
variation.

The next explicit calculation should therefore focus on the local Schur
piece:

\[
\boxed{
\text{compute }H_{\xi y}H_{yy}^{-1}H_{y\xi}
\text{ for the neck and endpoint-transfer jets.}
}
\]

If this produces exactly the combinations \(Q_c\) and \(\Gamma\), then the
remaining bulk log-energy part only has to be checked for positive
semidefiniteness on the projected tangent cone.  That is a standard finite-gap
convexity statement and is likely easier than the current Schur identity.

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
