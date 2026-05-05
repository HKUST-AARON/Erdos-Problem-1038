# Erdős Problem 1038 - 已可交付进展（Tao 关注版）

## 1. 题目重写（统一形式）

对非平凡首一实根在 \([-1,1]\) 的多项式 \(f\in \mathbb R[x]\)，设
\[
\mu_f:=\frac1n\sum_{j=1}^n \delta_{r_j},\qquad
f(x)=\prod_{j=1}^n (x-r_j),\ r_j\in[-1,1].
\]
定义
\[
U_\mu(x):=\int_{-1}^1 \log\frac1{|x-t|}\,d\mu(t),
\qquad
E_\mu:=\{x:U_\mu(x)>0\}.
\]
则
\[
\{x:|f(x)|<1\}=E_{\mu_f}.
\]
所以问题等价于
\[
L_+:=\sup_{\mu\in\mathcal P([-1,1])}|E_\mu|,
\quad
L_-:=\inf_{\mu\in\mathcal P([-1,1])}|E_\mu|.
\]

---

## 2. 上确界 \(L_+\) 已闭合（可交付）

### 2.1 结果
\[
\boxed{L_+=2\sqrt2.}
\]

### 2.2 下界
\[
f(x)=x^2-1
\quad\Longrightarrow\quad
|f(x)|<1 \iff -\sqrt2<x<\sqrt2,
\]
故 \(|E_{\mu_f}|=2\sqrt2\)，所以 \(L_+\ge 2\sqrt2\)。

### 2.3 上界（Tao notes 风格）：\(L_+\le2\sqrt2\)

有标准对偶/重排框架（见 Tao notes 中对长度2 区间上端点配置的结论）：
- 若 \(\mu\) 支持在长度为 2 的区间上，则 \(|E_\mu|\le2\sqrt2\)；
- 且等号仅在两点测度（每点质量 \(1/2\)）的极端构型中达到：
\[
\mu=\frac12\delta_{-1}+\frac12\delta_{1}
\]
（平移版本对应平移区间）。

因为我们题设根固定在 \([-1,1]\)，可得上界直接成立：
\[
L_+\le2\sqrt2.
\]

于是
\[
L_+=2\sqrt2.
\]

---

## 3. 这个阶段可立即提交给 Tao 的正文版本结构（Sup 的 proof block）

可直接放进文稿的最小段落：

1. 先写 monic 多项式与对数势能的等价转换（本文件 1 节）。
2. 写 \(f(x)=x^2-1\) 给出下界。
3. 引用/复述“长度为 2 的支撑区间上势能正位集长度上界”结论（上界）及等号形态。
4. 结论 \(L_+=2\sqrt2\)。

这样你这条工作线即为“可闭合结论”。

---

## 3.1 可复用局部对偶块：\(\nu_0=\frac12(\delta_{-\varphi}+\delta_{\varphi-1})\)

令 \(\varphi=\frac{1+\sqrt5}{2}\)，\(\varphi-1=\frac1\varphi\)。取
\[
\nu_0:=\frac12\delta_{-\varphi}+\frac12\delta_{\varphi-1}.
\]
则
\[
U_{\nu_0}(x)=\frac12\log\frac1{|x+\varphi|}+\frac12\log\frac1{|x-(\varphi-1)|}.
\]
在区间 \(x\in[0,\varphi-1]\) 上有
\[
U_{\nu_0}(x)
=-\frac12\log\!\big((x+\varphi)(\varphi-1-x)\big)
=-\frac12\log(1-x-x^2)\ge0,
\]
因为 \((x+\varphi)(\varphi-1-x)=1-x-x^2\le1\)，且在 \((0,\varphi-1)\) 严格小于 1。

在 \(x\in[\varphi-1,1]\) 上
\[
U_{\nu_0}(x)
=-\frac12\log\!\big((x+\varphi)(x-\varphi+1)\big)
=-\frac12\log(x^2+x-1)\ge0,
\]
因为 \(x^2+x-1\in[0,1]\)。并且
\[
U_{\nu_0}(-1)=0,\qquad U_{\nu_0}(0)=0,\qquad U_{\nu_0}(1)=0.
\]
所以
\[
U_{\nu_0}(x)\ge0\quad\text{在 } \{-1\}\cup[0,1]\text{ 上成立}.
\]

这个单元在讨论两点对偶族时可直接复用：它给出一类显式、可检查的 dual witness（只做解析计算，无需取样）。其用途主要是与“一点变分 + 区间推进”框架拼装下界，但仍不足以闭合整体 \(L_-\)。

---

## 4. 下确界当前状态：已有可交付 lower bound，exact inf 未闭合

在 Tao/natso reduction（归一化 minimizer 满足
\(\mu(\{-1\})\ge1/2\), \(\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1]\)）之后，三原子 covering certificate 给出
\[
\boxed{L_-\ge1.7875.}
\]

具体常数为
\[
M=1.7875,\quad A=1.27535,\quad B=0.34971,\quad D=2.73422.
\]
对每个 \(a\in[-M,-\sqrt2]\)，取
\[
\nu_a=\delta_a+A\delta_{a+M}+B\delta_{a+D}.
\]
令
\[
V(y)=\log\frac1{|y|}
+A\log\frac1{|y-M|}
+B\log\frac1{|y-D|}.
\]
在 \(y\in[\sqrt2-1,1+M]\) 上，唯一需检查的有限点为端点和二次方程
\[
1312530000y^2-4316957051y+2443709125=0
\]
的两个根。区间检查给出
\[
V(\sqrt2-1)>0.1825,\quad
V(r_1)>2.5\cdot10^{-4},\quad
V(r_2)>2.4\cdot10^{-4},\quad
V(1+M)>2.7\cdot10^{-4}.
\]
因此 \(U_{\nu_a}>0\) on \([-1,1]\)。由对偶恒等式，三点
\[
a,\quad a+M,\quad a+D
\]
至少一个落入 \(E_\mu\)。再结合
\[
(-\sqrt2,0)\subset E_\mu
\]
和三个平移区间的两两不交性，得到 \(|E_\mu|\ge M=1.7875\)。

因此当前可写为
\[
1.7875\le L_-\le 1.83443047576266\ldots
\]

论坛 stronger numerical status:
- 固定三原子参数
\[
M=1.7877,\quad A=1.27383,\quad B=0.34979,\quad D=2.73436
\]
通过同一有限点检查的数值验证，最小裕度约 \(2.24\cdot10^{-5}\)，但尚未写成 directed interval arithmetic 证书。
- 四原子 \(1.8\) 路线已经拆开：固定四原子 positivity block 数值通过，但最小裕度很薄（约 \(3.5\cdot10^{-7}\)）；核心缺口是证明 \([-1.708,0]\subset E_\mu\) 的二维 family certificate。当前密集网格未发现反例，\([0,1]\) 上观测最小值约 \(1.26\cdot10^{-3}\)，但仍不是严格证明。
- 新的保守 \(1.8\) 路线更值得推进：先用二维 family 证明 \((-1.7,0)\subset E_\mu\)（数值上 \([0,1]\) 最小裕度约 \(2.86\cdot10^{-2}\)，\(-1\) 处强制为 \(10^{-4}\)），再用高裕度四原子块补出额外 \(0.1\) 长度（数值最小裕度约 \(3.51\cdot10^{-3}\)）。这仍需 interval arithmetic，但比旧四原子块安全得多。
- two-interval ansatz 方面，外部反馈指出必须加入 endpoint atom \(m_1\delta_1\)。该点是正确的：若
\[
F(z)=\frac{z+A}{(z-\ell)(z-r)(z-1)}\sqrt{(z-\alpha)(z-\beta)},\quad \beta=1-\varepsilon,
\]
则 \(z=1\) 的 residue 为
\[
m_1=\frac{(1+A)\sqrt{(1-\alpha)\varepsilon}}{(1-\ell)(1-r)}>0
\]
在目标参数区间内成立。

所以对外口径应是：
\[
\text{rigorous written progress: }L_-\ge1.7875,\qquad
\text{forum-strength numerical targets: }1.7877,\ 1.8.
\]

完整 exact infimum 仍未闭合：
\[
L_-\stackrel{?}{=}1.83443047576266\ldots
\]
关键缺口是:

- 对**任意候选正集** \(E\subset\mathbb R\)，尤其非单区间形态，
  仍缺一个全局对偶证书：存在 \(\nu\ge0\)、\(\operatorname{supp}\nu\subset\mathbb R\setminus E\) 且
  \[
  U_\nu\ge0\text{ on }[-1,1].
  \]
- 只要这一步对 \(|E|<M_*\) 可行，便可得到 \(L_-\ge M_*\)。

这里 \(M_*\approx1.83443047576266\) 来自 one-cut 构造的上界候选（见你前述候选公式）。

---

## 5. 下一步一句话

下一步优先级：
1. 先 intervalize 新的保守 \(1.8\) 路线：\((-1.7,0)\) forcing family + 高裕度四原子块。
2. 若 1 的二维 family 出现技术阻力，再退回固定三原子 \(1.7877\) 的 directed interval arithmetic 证书。
3. 同步修正 exact inf 的 two-interval ansatz：加入 \(m_1\delta_1\)，再做 sign-chart reduction。
4. 最后推进 exact inf 的 general \(E\) dual certificate。
## 2026-05-02 update: 1.8063 lower-bound package

The lower-bound route has advanced from a grid check to a certificate-backed
conditional theorem, and then from \(1.8\) to \(1.8063\).

Current status:

- The fixed-shift three-atom certificate improves the earlier safe \(1.7875\)
  bound to a reproducible \(1.7877\) one-variable certificate.  The comments
  also contain a stronger variable-weight three-atom numerical route near
  \(1.7902\), so \(1.7877\) is not the three-atom frontier.
- The high-margin four-atom block needed for the \(1.8\) route is verified.
- A stronger four-atom block on \([-1.8036,-1.7]\) is now verified by both the
  Decimal certificate and the Lean numeric checker.  In this four-atom line,
  \(1.8038\) is already negative in the current search.
- A still stronger five-atom block on \([-1.804,-1.7]\) is now verified by both
  the Decimal certificate and the Lean numeric checker.
- A five-atom block on \([-1.805,-1.7]\) is now verified by both the Decimal
  certificate and the Lean numeric checker.
- A five-atom block on \([-1.806,-1.7]\) is now verified by both the Decimal
  certificate and the Lean numeric checker, though with smaller margin.
- A five-atom block on \([-1.8063,-1.7]\) is now verified by the Decimal
  certificate and mirrored in the Lean numeric checker.  This is the current
  strongest local certificate-backed lower-bound block.
- The missing two-parameter forcing family
  \[
  a\in[-1.7,-\sqrt2],\quad b\in[0,1.82+a],
  \quad
  \nu_{a,b}=\delta_a+(1.395-b)\delta_b+C(a,b)\delta_{1.071-b}
  \]
  is now covered by a finite interval-box verifier.
- The duality step has been rewritten using a shifted truncated-kernel lemma,
  so the \(\mu(\{-1\})\ge1/2\) atom is no longer hidden under a finite-energy
  assumption.
- Lean now runs the three-atom, four-atom through \(1.8036\), five-atom through
  \(1.8063\), and conservative forcing interval numeric checks in
  `1038/LeanCertificates.lean`; all pass.
- The exact-infimum route has been restarted in
  `1038/solve_two_interval_finite_gap.py` and §15 of
  `1038_dual_two_interval_progress.md`: the corrected two-interval
  finite-gap ansatz includes the endpoint atom at \(1\), solves
  \(U(\alpha)=U(-1)=0\) for the small-\(\varepsilon\) branch, identifies the
  \(\varepsilon=0\) limiting system
  \((A_0,\alpha_0)\approx(1.183353601765,0.804461769731)\), and reduces the
  next proof bottleneck to a singular/interval parameter-branch theorem in
  \(\eta=\sqrt{\varepsilon}\).
- The two-interval branch skeleton now has a separate verifier,
  `1038/verify_two_interval_branch_skeleton.py`, and passes on
  \(\varepsilon=0.002,0.001,0.0005,0.0002,0.0001,0.00005\).  This is still a
  sampled Krawczyk skeleton, not an outward-rounded interval proof.  The
  verifier now also rechecks stored contact residuals and can run an Arb/Acb
  center-residual diagnostic: it computes \(U(-1)\) as an Arb ball and derives
  \(U(\alpha)\) from the residue-log Arb ball for \(U(-1)-U(\alpha)\), avoiding
  a direct Arb integration of the contact log singularity.  It also has an
  Arb/Acb full-box \(U(-1)\) check in the boundary-layer variable
  \(u=\sin(\theta/2)\), which keeps the small-\(\varepsilon\) endpoint pole at
  \(1\) separated as \(t-1=-\varepsilon-2h u^2\).  The same primitive now
  encloses the \(U(-1)\) directional derivatives in the local \(B,\tau\)
  coordinates over each Krawczyk box.  A separate diagnostic primitive now
  encloses the contact \(U(\alpha)\) derivatives in the local \(B,\tau\)
  directions over each Krawczyk box, using split \(u=\sin(\theta/2)\) and
  \(v=\cos(\theta/2)\) charts plus a conservative Arb tail ball at the contact
  endpoint.  These primitives are now assembled into a diagnostic Arb interval
  \(D_{(B,\tau)}K\) matrix with entrywise center containment.  The direct
  \(1\times1\) full-box Krawczyk defect action remains too wide in the
  \(\tau\) component, but the new `--arb-interval-krawczyk-check` computes the
  center correction as an Arb upper bound for \(|C K_{\mathrm{center}}|\) and a
  \(7\times7\) subbox diagnostic passes
  \(\operatorname{correction}_{\mathrm{Arb}}+\max\operatorname{defect}<\operatorname{radii}\)
  on all six rows; the worst remaining margin is \(4.163420\cdot10^{-3}\) at
  \(\varepsilon=0.001\), \(\tau\), with the defect term dominating.  This is a
  local interval Krawczyk inclusion diagnostic, not a full \(L_-\ge1.83\)
  proof.
- The corrected two-interval route now also has two split checkers:
  `1038/verify_two_interval_sign_box.py` verifies the sign chart, positivity
  boxes, stored-center containment, and stored sign-margin consistency, while
  `1038/verify_two_interval_krawczyk_grid.py` stress-tests the full
  \((B,\tau)\)-Krawczyk boxes.  Both pass on all six rows.  The sign-box checker
  has a tamper self-test; the Krawczyk checker also has a refinement mode, and
  grids \(11,21,41\) give zero reported drift at the printed precision.  The
  current worst sampled Krawczyk margin is \(9.876968\cdot10^{-3}\), with worst
  contraction
  \(1.230325\cdot10^{-2}\).  It now also reports the intervalization budget
  implied by the unused Krawczyk margin: with a half-margin split, the tightest
  uniform center-\(K\) radius budget is \(2.110507\cdot10^{-3}\), and the
  tightest uniform \(DK\)-entry budget is \(1.055254\cdot10^{-1}\) in rescaled
  coordinates.  This supports the finite-gap branch toward the
  \(1.8344304757\ldots\) exact route; it is not a proof of the global
  \(L_-\ge1.83\) statement until the interval Krawczyk and general
  \(E\)-reduction are closed.
- `1038/FormalSkeleton.lean` now formalizes the conditional proof pipeline as
  a Lean theorem from explicit certificate assumptions:
  short counterexample \(\Rightarrow\) normalized baseline
  \(\Rightarrow\) two-dimensional or four-atom case
  \(\Rightarrow\) contradiction.
- The two-dimensional interval certificate is now exported as fixed leaf boxes
  in `1038/conservative_forcing_interval_certificate.json`, and the verifier
  can re-check that JSON certificate without re-searching.

Thus, accepting the standard Tao/natso reduction

\[
\mu(\{-1\})\ge\frac12,\qquad
\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1],
\]

the current package proves the conditional theorem

\[
\boxed{|E_\mu|\ge1.8063.}
\]

Forum-safe wording:

> Conditional on the standard minimizer reduction, I can prove a \(1.8063\) lower
> bound using a finite interval-box certificate for the two-parameter forcing
> family.  The checker is reproducible in Python and mirrored by a Lean-executed
> numeric certificate; it is not yet a full Mathlib formalization of the
> logarithm inequalities.

## 2026-05-02 proof rebuild: two-interval finite-gap route

This is the current clean theorem chain after re-proving the two-interval line
from the implemented ansatz.  It deliberately separates what is proved, what is
diagnostic, and what is still missing before any \(L_-\ge1.83\) claim.

### A. Corrected ansatz and endpoint atom

Fix
\[
\ell=x_L+\varepsilon,\qquad r=x_R,\qquad \beta=1-\varepsilon,
\]
and consider
\[
F(z)=\frac{z+A}{(z-\ell)(z-r)(z-1)}
\sqrt{(z-\alpha)(z-\beta)},\qquad F(z)\sim 1\quad(z\to\infty)
\]
with
\[
\ell<-1<r<\alpha<\beta<1,\qquad A>1.
\]
The branch is chosen so that the extracted density on \((\alpha,\beta)\) is
nonnegative in the checked sign chart.  At \(z=1\), the square root is analytic
and
\[
\sqrt{(1-\alpha)(1-\beta)}=\sqrt{(1-\alpha)\varepsilon}.
\]
Therefore \(F\) has residue
\[
m_1=
\operatorname{Res}_{z=1}F(z)
=
\frac{(1+A)\sqrt{(1-\alpha)\varepsilon}}{(1-\ell)(1-r)}>0.
\]
Thus any positive-measure Cauchy-transform interpretation of this ansatz must
include the endpoint atom \(m_1\delta_1\).  This part is a direct residue
calculation and is mathematically closed.

### B. Fixed-\(\varepsilon\) local branch certificate

Let
\[
\eta=\sqrt{\varepsilon},\qquad
\alpha=\alpha_0+\eta\tau,\qquad
A=A_0+\eta(\sigma\tau+B),
\]
where \((A_0,\alpha_0)\) is the limiting solution and \(\sigma\) is the limiting
null-slope recorded in the JSON skeleton.  Define
\[
K(B,\tau;\eta)
=
\left(
\frac{U(\alpha)}{\eta},
\frac{w\,U(\alpha)+U(-1)}{\eta^2}
\right).
\]
For each stored row
\[
\varepsilon\in\{0.002,0.001,0.0005,0.0002,0.0001,0.00005\},
\]
the verifier checks:

1. the sign chart \(1<A<-\ell\), \(\ell<-1<r<\alpha<\beta<1\);
2. atom and density positivity at the stored center;
3. Arb center residuals for \(K(B_0,\tau_0;\eta)\);
4. Arb/Acb enclosures for the two columns of \(D_{B,\tau}K\) over the local
   \(B,\tau\) box;
5. the componentwise Krawczyk inequality
\[
|C K(B_0,\tau_0;\eta)|
\;+\;
\sup_X |I-C\,D_{B,\tau}K(X)|\,r
<r,
\]
with a \(7\times7\) subdivision of the local \(B,\tau\) box.

Validated command:

```bash
.venv/bin/python 1038/verify_two_interval_branch_skeleton.py --quiet \
  --arb-primitive-check --arb-center-residual-check --arb-box-uminus-check \
  --arb-box-uminus-derivative-check --arb-box-contact-derivative-check \
  --arb-box-dk-check --arb-interval-krawczyk-check \
  --arb-box-dk-subdivisions 7,7 --self-test-tamper
```

Result:

```text
OVERALL TWO-INTERVAL SKELETON CHECK: PASS
(6 rows; tamper self-test PASS 6 cases; verifier integrity only, not a math proof)
```

Interpretation: conditional on the correctness of the Arb primitives, this is a
fixed-\(\varepsilon\) local branch certificate for the implemented equations.
It is not yet a continuum theorem in \(\varepsilon\).

### C. Adjacent epsilon-slab diagnostic

The new slab checker works on adjacent stored rows.  On a slab
\([\varepsilon_1,\varepsilon_2]\), it interpolates \(B_c(\eta)\) and
\(\tau_c(\eta)\) affinely in \(\eta\), then checks boxes
\[
B=B_c(\eta)+u,\qquad \tau=\tau_c(\eta)+v,
\qquad |u|,|v|\le 10^{-2}.
\]
It now verifies the sign chart over the full \(\eta\)-slab and all \(u,v\)
subboxes, rejects non-adjacent slab endpoints, and reports the worst defect
source.  In the default diagnostic mode, the center correction and \(DK\)
dependence on \(\eta\) are still sampled, not interval-enclosed.

Validated single-slab command:

```bash
.venv/bin/python 1038/verify_two_interval_epsilon_slabs.py \
  1038/two_interval_branch_certificate_skeleton.json \
  --slab 0.00005:0.0001 \
  --center affine-endpoints \
  --uv-radii 0.01,0.01 \
  --arb-box-dk-subdivisions 7,7 \
  --quiet
```

Result:

```text
PASS, worst_margin=1.489253e-03,
component=v, dominant=defect,
status=diagnostic-not-continuum-proof
```

The five adjacent slabs also pass when run one at a time with these diagnostic
settings:

```text
[0.00005,0.0001]  7,7   PASS, margin 1.489253e-03
[0.0001, 0.0002]  7,14  PASS, margin 4.798109e-03
[0.0002, 0.0005]  7,14  PASS, margin 5.666347e-03
[0.0005, 0.001]   7,14  PASS, margin 4.632834e-03
[0.001,  0.002]   7,14  PASS, margin 4.417884e-03
```

This is meaningful evidence for the small-\(\varepsilon\) branch, but it is
still not a proof of a continuum branch because \(\eta\)-dependence is sampled.

### D. Attempted eta-interval DK closure and current obstruction

The checker now also has an experimental mode
`--eta-interval-dk-check`, which encloses \(DK\) over eta subintervals instead
of sampling eta.  This attacks the main missing step directly.  The naive
interval lift currently fails because the Arb derivative boxes become much too
wide in the \(v=\tau\) direction.

Commands tried:

```bash
.venv/bin/python 1038/verify_two_interval_epsilon_slabs.py \
  1038/two_interval_branch_certificate_skeleton.json \
  --slab 0.00005:0.0001 \
  --center affine-endpoints \
  --uv-radii 0.01,0.01 \
  --arb-box-dk-subdivisions 7,7 \
  --eta-interval-dk-check --quiet
```

Failure:

```text
margin=-3.950630e-01,
correction=2.635876e-05,
defect=4.050367e-01,
component=v, dominant=defect
```

With finer eta subdivision:

```bash
--arb-box-dk-subdivisions 14,7 --eta-interval-dk-check
```

Failure:

```text
margin=-2.549520e-01,
defect=2.649256e-01,
component=v, dominant=defect
```

The adjacent slab \([0.0001,0.0002]\) also fails in the same way:

```text
margin=-2.566466e-01,
defect=2.665948e-01,
component=v, dominant=defect
```

The next repair was to add a combined derivative primitive for the rescaled
second equation.  Instead of enclosing
\[
dU(\alpha),\qquad dU(-1)
\]
separately and then forming
\[
\frac{w\,dU(\alpha)+dU(-1)}{\eta^2},
\]
the solver now has
`_combined_contact_minus_one_directional_derivative_acb_from_arb`, which
integrates the derivative of \(wU(\alpha)+U(-1)\) directly.  This preserves part
of the Lyapunov-Schmidt cancellation that was lost by separate interval
evaluation.

The improvement is real but not yet enough.  On the first slab
\([0.00005,0.0001]\), component \(v\):

```text
direct separate derivative, 7,7:
  defect=4.050367e-01

combined derivative with corrected contact-tail bound, 7,7:
  defect=3.039123e-01

combined derivative, 14,7:
  defect=1.626021e-01

combined derivative, 28,7:
  defect=9.184954e-02

combined derivative, 56,7:
  defect=5.670137e-02
```

With smaller \(u,v\) radius \(0.005\) and \(28,7\), the same obstruction gives

```text
radius=5.000000e-03,
defect=4.564576e-02,
component=v.
```

So the failure is no longer an unexplained numerical issue.  It is a quantified
dependency problem in the eta-dependent \(v\)-column of \(D K\).  Direct
subdivision appears to converge, but far too slowly for a proof-grade
certificate.  The next proof step cannot be "turn epsilon into an Arb interval"
naively, and it also cannot be solved efficiently by brute-force subdivision.
It must use a renormalized eta expansion or a sharper analytic formula for the
eta-dependent \(v\)-derivative box.

### E. Exact remaining theorem before any \(1.83\) claim

The missing theorem is:

> There is an \(\varepsilon_0>0\) such that for every
> \(0<\varepsilon\le\varepsilon_0\), the corrected endpoint-atom
> two-interval ansatz has a solution of
> \(U(\alpha)=U(-1)=0\) satisfying the sign chart, positivity of all extracted
> masses/density, and the global dual potential sign conditions.

Current status of its proof:

1. fixed-\(\varepsilon\) local branch: diagnostic certificate closed on six rows;
2. adjacent finite slab chain: sampled diagnostic closed on
   \([0.00005,0.002]\);
3. eta-interval \(DK\): attempted, but current direct Arb intervalization fails
   from dependency blow-up in the \(\tau\) derivative component;
4. eta-interval center \(K\): still missing, especially an interval version of
   the contact value \(U(\alpha)\) or an equivalent residue-log primitive over
   parameter boxes;
5. global positivity/general \(E\) reduction: not yet proved.

Therefore the honest conclusion is:

\[
\boxed{
\text{The two-interval route is alive and numerically coherent, but the full }
L_-\ge1.83\text{ proof is not yet closed.}
}
\]

The next proof action is not to add more sampled epsilon rows.  It is to replace
the eta-dependent derivative and center-residual checks by a renormalized,
outward-rounded eta-slab certificate.

### E2. 2026-05-06 mathematical proof ledger

The exact-value target is now fixed as

\[
M_* = x_R-x_L
=1.8344304757626617\ldots,
\]

with

\[
x_L=-1.8081073680988165,\qquad
x_R=0.02632310766384517.
\]

The current paper-level proof chain is:

1. **Upper bound.**  The one-cut primal measure

   \[
   \mu_a=A(a)\delta_{-1}+f_a(x)\mathbf1_{[a,1]}(x)\,dx
   \]

   with

   \[
   f_a(x)=
   \frac{x+1-A(a)\sqrt{2(1+a)}}
   {\pi(x+1)\sqrt{(1-x)(x-a)}}
   \]

   has \(U_{\mu_a}=0\) on \([a,1]\).  At
   \(a_*=0.804461769730796\ldots\), its two exterior zeros are
   \(x_L,x_R\), so \(E_{\mu_{a_*}}=(x_L,x_R)\) and

   \[
   L_-\le M_*.
   \]

2. **Local lower-bound branch.**  For a regular extremal whose dual active
   zero set is one interval \([\alpha,\beta]\), the condition
   \(U_\lambda=0\) on \([\alpha,\beta]\) forces the Cauchy transform to be

   \[
   F(z)=
   \frac{z+A}{(z-\ell)(z-r)(z-1)}
   \sqrt{(z-\alpha)(z-\beta)}.
   \]

   With

   \[
   \ell<-1<r<\alpha<\beta<1,\qquad 1<A<-\ell,
   \]

   the residues at \(\ell,r,1\) and the density on \([\alpha,\beta]\) are
   positive.  The sign chart reduces \(U_\lambda\ge0\) on \([-1,1]\) to the
   two contact equations

   \[
   U_\lambda(\alpha)=0,\qquad U_\lambda(-1)=0.
   \]

   This is the corrected endpoint-atom two-interval finite-gap ansatz.

3. **Remaining global gap.**  The missing step is not another numeric row.  It
   is the global topology lemma: every regular \(|E_\mu|<M_*\) counterexample
   must either fall into the one-cut/two-interval finite-gap branch above, or
   admit a gap-pinching/Schiffer variation that decreases \(|E_\mu|\).

Equivalently, the next purely mathematical target is the interlacing-collapse
lemma for positive Stieltjes finite-gap transforms.  On every real component
away from the dual support,

\[
F'(x)=-\int\frac{d\lambda(t)}{(x-t)^2}<0,
\]

so every extra positive component forces a unique zero of \(F\) interlacing
with boundary poles and cut endpoints.  The expected closure is that such a
higher-genus interlacing pattern cannot stay positive under
\(|E_\mu|<M_*\), except by degeneration to the two-interval branch.

Until this interlacing-collapse/global topology lemma is proved, the correct
status is:

\[
\boxed{
L_-\le M_* \text{ is explained by the one-cut construction, while }
L_-\ge M_* \text{ remains open at the global topology step.}
}
\]

### E3. Direct normalized lower-bound attack

After treating the standard reduction as supplied by the separate
normalization notes, the exact lower-bound target is the normalized statement

\[
\operatorname{supp}\mu\subset\{-1\}\cup[0,1],\qquad
\mu(\{-1\})\ge\frac12
\quad\Rightarrow\quad
|E_\mu|\ge M_*.
\]

The current direct attack on this normalized theorem starts from a regular
counterexample with \(|E_\mu|<M_*\).  If there is an extra positive component

\[
I=(u,v)\subset(0,1)
\]

containing the unique atom \(q\delta_c\), then locally

\[
U_\mu(x)=q\log\frac1{|x-c|}+W(x).
\]

Moving \(c\mapsto c+s\) gives

\[
\dot U(x)=\frac{q}{x-c}.
\]

Since \(U_\mu(u)=U_\mu(v)=0\), with

\[
U_\mu'(u)>0,\qquad U_\mu'(v)<0,
\]

the endpoint variations are

\[
\dot u=-\frac{q}{(u-c)U_\mu'(u)},\qquad
\dot v=-\frac{q}{(v-c)U_\mu'(v)}.
\]

Length minimality of the counterexample forces

\[
\boxed{
(c-u)U_\mu'(u)=(v-c)|U_\mu'(v)|.
}
\]

Thus an extra component is not ruled out by topology alone; it must satisfy a
rigid balance equation.

On the dual side, complementarity gives \(U_\lambda(c)=0\).  For

\[
F(z)=\int\frac{d\lambda(t)}{z-t},
\]

one obtains

\[
F(c)=0,\qquad
F'(c)=-\int\frac{d\lambda(t)}{(c-t)^2}<0.
\]

So every extra positive component contributes a unique simple real zero of the
dual Cauchy transform.  If the active zero set has \(g\) intervals, this
places the problem in a positive finite-gap class

\[
F(z)=
\frac{P(z)}{Q(z)}
\sqrt{\prod_{k=1}^g(z-\alpha_k)(z-\beta_k)}.
\]

The remaining normalized lower-bound theorem is now the quantitative
finite-gap inequality:

\[
\boxed{
g\ge2\text{ positive finite-gap solutions satisfying the balance,
complementarity, residue positivity and density positivity conditions have }
|E|\ge M_*.
}
\]

This is sharper than the earlier "global topology" phrasing.  The exact
remaining mathematical work is to prove this quantitative inequality, or to
show that every equality/near-equality case degenerates to the one-cut
construction or the corrected two-interval branch.

### F. 2026-05-02 hard-mouth rebuild: what actually breaks in \(K_{2,\tau}\)

The first useful repair is an algebraic rescaling in the eta-interval DK
checker.  For eta intervals the verifier now keeps the Lyapunov-Schmidt
directions unscaled:

\[
\partial_B=(1,0),\qquad \partial_\tau=(\nu,1),
\]

and assembles

\[
K_{1,s}=dG_0[s],\qquad
K_{2,s}=\frac{w\,dG_0[s]+dG_1[s]}{\eta}.
\]

This is algebraically the same as the previous
\[
\frac{dG_0[\eta s]}{\eta},\qquad
\frac{w\,dG_0[\eta s]+dG_1[\eta s]}{\eta^2},
\]
but avoids putting an interval eta factor into the direction before the final
division.  On the first slab \([0.00005,0.0001]\), with \(7,7\) subdivisions,
this improves the eta-interval failure from

```text
previous combined derivative:
  defect=3.039123e-01

unscaled LS direction:
  defect=5.341965e-02
  margin=-4.344601e-02
```

The sampled MVP is unchanged and still passes:

```text
eta_DK_mode=sampled,
worst_margin=1.489253e-03,
defect=(3.866094e-04, 8.484388e-03).
```

The new failure instrumentation shows the exact remaining obstruction.  The
worst first-slab eta-interval check is:

```text
eta=[0.0070710678118654753,0.0074894866958846928],
u_subbox=6,
v_subbox=6,
component=v,
entry[1,1] action=5.042265e-02,
DK[1,1]=[-1.739483e+00,1.739483e+00].
```

Thus the bad term is not a general two-dimensional Krawczyk problem.  It is the
\((K_2,\tau)\) entry, i.e.

\[
\frac{w\,dU(\alpha)[\nu,1]+dU(-1)[\nu,1]}{\eta}.
\]

For a representative worst subbox after eta subdivision \(28,7\), the raw
split is:

```text
atom contribution to H_s:
  [-1.588679507e-01, -1.580724000e-01]

full H_s:
  [-5.720000009e-03, 5.720000009e-03]

full H_s / eta:
  radius about 8.089301605e-01.
```

So the present Arb primitive has already fixed the contact/minus-one
combination, but it still evaluates the atom and continuous parts separately.
The decisive cancellation is now between the endpoint atom contribution and
the continuous density contribution.  Merely refining the quadrature
breakpoints did not shrink this ball, and increasing \(u,v\) subdivisions did
not help either.

The hard next lemma is therefore sharper:

> Build a divided residue-log primitive for
> \[
> \frac{H_s(A,\alpha,\eta)-H_s(A_0,\alpha_0,0)}{\eta},
> \qquad
> H_s=w\,dU(\alpha)[\nu,1]+dU(-1)[\nu,1],
> \]
> or an equivalent formula in which the endpoint atom and continuous
> contribution are combined before interval enclosure.

This is the current hard mouth of the two-interval route.  Brute-force eta or
\(u,v\) subdivision is not an efficient path to closure.

### G. Residue-log divided primitive experiment

A natural next attempt was to write the differentiated full Cauchy transform
directly in the Joukowski coordinate:

\[
F_s(z)
=
\frac{R(z)}{(z-\ell)(z-r)(z-1)}
\left(
\nu-\frac{z+A}{2(z-\alpha)}
\right),
\qquad
s=\nu\partial_A+\partial_\alpha.
\]

With
\[
z=c+\kappa(w+w^{-1}),\qquad
R=\kappa(w-w^{-1}),
\]
the differential \(F_s(z(w))z'(w)\,dw\) is rational in \(w\).  At fixed
parameters this gives

\[
d_sU(\alpha)=-P(-1),\qquad
d_sU(-1)=-P(w_{-1}),
\]
where \(P\) is a finite residue-log primitive over the six preimages of
\(\ell,r,1\).  A new experimental solver routine,
`_combined_directional_derivative_residue_log_from_arb`, implements this
fixed-parameter formula.  Numeric checks against `analytic_G_derivative` agree
to floating integration error.

The endpoint \(1\) pair has to be written in the stable form

\[
\rho_1^-=\frac{\sqrt{1-\alpha}-\eta}{\sqrt{1-\alpha}+\eta},
\qquad
\rho_1^+=\frac{\sqrt{1-\alpha}+\eta}{\sqrt{1-\alpha}-\eta},
\]

instead of using \(\sqrt{y^2-4}\), because \(y\to2\) at the endpoint layer.
The left-side inner preimages also have to be written as reciprocals of the
outer preimages to avoid enclosing zero.

I then added an experimental eta-divided version,
`_combined_directional_derivative_residue_log_divided_from_arb`, which subtracts
the \(\eta=0\) residue-log terms for the \(\ell,r\) poles and treats the
endpoint \(1\) pair after division by eta.  At fixed floating parameters this
matches the current \(H_s/\eta\) value.  However, when inserted into the first
eta slab as an interval box, it fails worse than the old combined quadrature:

```text
residue-log divided, first slab, 7,7:
  defect=3.423855e-01,
  DK[1,1]=[-1.010000e+01, 1.010000e+01]

old combined contact/minus-one primitive, first slab, 7,7:
  defect=5.341965e-02,
  DK[1,1]=[-1.739483e+00, 1.739483e+00]
```

So the residue-log direction is mathematically right but the current
implementation still splits too many residue-log terms before enclosing the
box.  The remaining cancellation is not just endpoint atom versus continuous
density; it also sits across the \(\ell,r,1\) residue-log terms after the
\(\eta=0\) subtraction.  The active verifier is therefore kept on the stronger
combined contact/minus-one primitive, with the residue-log divided routine left
as an experimental prototype.

The next proof-level implementation should not sum six separately boxed
residue-log terms.  It should form the single rational primitive numerator over
a common denominator, cancel removable factors, and only then take the eta
divided difference.

### H. Paired smooth-pole experiment

The next attempted reduction paired the two large smooth-pole terms on each
Joukowski sheet before taking the eta divided difference:

\[
a_\ell\log|x-\rho_\ell|+a_r\log|x-\rho_r|
=
a_\ell\log\left|\frac{x-\rho_\ell}{x-\rho_r}\right|
+(a_\ell+a_r)\log|x-\rho_r|.
\]

This is implemented as the experimental routine
`_combined_directional_derivative_residue_log_pair_divided_from_arb`.
At fixed floating parameters it agrees with the analytic Jacobian values:

```text
epsilon=0.001:
  target=-4.5549324580472417e-01,
  pair-divided ball contains the target

epsilon=0.0001:
  target=-4.332281104077063e-01,
  midpoint error about 6.5e-14

epsilon=0.00005:
  target=-4.29937165414466e-01,
  midpoint error about 4.0e-13
```

However, on the first eta interval of the first slab, it still fails badly.  In
the eta-only version of the worst subbox, with \(u,v\) fixed at the subbox
center and only eta interval-enclosed, the old combined quadrature gives

```text
old combined primitive:
  DK[1,1] radius about 1.7536248
```

whereas the paired residue-log divided prototype gives

```text
paired residue-log divided:
  DK[1,1] radius about 9.0700000
```

The component diagnosis shows the remaining wide term is not the raw
\(\ell/r\) cancellation itself.  It is the eta divided variation of the paired
residue sum on the outer sheet:

```text
((a_ell+a_r)-(a_ell0+a_r0))/eta:
  radius about 0.8395

multiplied by log|x-rho_r0|:
  contributes radius about 2.37
```

Putting \(a_\ell+a_r\) over a common denominator improves almost nothing:

```text
naive pair-sum divided radius:   0.839499
common-denominator divided radius: 0.839051
```

So the next obstruction is sharper than pairing residues.  The interval engine
must not form

\[
\frac{f(\eta)-f(0)}{\eta}
\]
by evaluating \(f(\eta)\) and \(f(0)\) as two unrelated balls.  It needs a
first-order eta Taylor model, affine arithmetic, or an explicitly derived
divided formula for the paired residue sums themselves.

Current best active checker therefore remains the combined contact/minus-one
primitive with the unscaled LS direction:

```text
first slab eta-interval, 7,7:
  DK[1,1]=[-1.739483, 1.739483],
  defect=5.341965e-02.
```

The paired residue-log prototype is useful as a localization tool, but it is
not yet a better verifier.

### I. Tao note calibration and the first hard number after reading it

The uploaded Tao note `erdos-1038-2 terry tao.pdf` is directly aligned with
this exact-infimum line.  Its Section 4 writes the Hilbert-transform/Cauchy
transform ansatz for the one-cut candidate, identifies the numerical endpoint
data

```text
x_L = -1.8081073680988165
x_R =  0.02632310766384517
M_* = x_R - x_L = 1.8344304757626617
```

and ends with Problem 4.1: for small \(\varepsilon>0\), construct a positive
dual measure supported on

\[
[-1.808+\varepsilon,0.026]\cup[a,1-\varepsilon]
\]

with nonnegative potential on \([-1,1]\).  This is exactly the corrected
two-interval branch implemented here, with the endpoint atom at \(1\) included.

The existing solver is therefore not a side route to \(1.8\); it is the local
model for the conjectural exact value \(M_*=1.8344304757626617\ldots\).  The
finite-atom \(1.8063\) certificate remains a lower-bound route, while this
two-interval route is the candidate exact-value route if the global dual
reduction can be closed.

After adding the DK-focused diagnostic mode

```bash
.venv/bin/python 1038/verify_two_interval_epsilon_slabs.py \
  1038/two_interval_branch_certificate_skeleton.json \
  --slab 0.00005:0.0001 \
  --center affine-endpoints \
  --uv-radii 0.01,0.01 \
  --arb-box-dk-subdivisions 1,2 \
  --dk11-eta-radius-report 8,16,32,64 \
  --dk11-sample-grid 2
```

the first small-\(\varepsilon\) slab reports:

```text
eta_subdivisions=8
  max_interval_radius=1.711198e+00
  max_sample_radius=2.384146e-03
  max_radius_inflation=7.295353e+02

eta_subdivisions=64
  max_interval_radius=7.396337e-01
  max_sample_radius=2.207919e-03
  max_radius_inflation=3.429966e+02
  worst_interval=[-7.396337e-01,7.396337e-01]
  worst_sample=[-4.342351e-01,-4.299223e-01]
```

With a coarser \(u,v\) split, even \(\eta\)-subdivision 256 still shows the
same dependency loss:

```text
eta_subdivisions=256
  max_interval_radius=6.367800e-01
  max_sample_radius=2.189095e-03
  max_radius_inflation=2.980689e+02
```

But on the actual worst \(7\times7\) subbox, direct targeted checks show the
old combined primitive does converge toward the true value when \(\eta\) is
cut finely:

```text
N=7:   DK[1,1]=[-1.739483,  1.739483], true≈-0.433834
N=112: DK[1,1]=[-0.560453, -0.287014], true≈-0.433603
N=224: DK[1,1]=[-0.521138, -0.326786], true≈-0.433595
N=448: DK[1,1]=[-0.501622, -0.346586], true≈-0.433583
```

This gives the first hard post-Tao diagnostic number: the analytic branch is
stable near \(-0.43\), while the current interval evaluator can inflate the
same entry by \(300\)-\(700\times\) depending on the box.  Thus the failure is
not absence of a numerical branch; it is the eta-divided interval enclosure.

The next code-level cut is now precise.  In
`solve_two_interval_finite_gap.py`,
`_combined_directional_derivative_residue_log_pair_divided_from_arb` still
forms terms of the shape

```python
((sum_residue - sum_residue0) / eta) * log_abs(base0)
```

with `sum_residue = a_ell + a_r`.  This evaluates the two residues at
\(\eta>0\) and \(\eta=0\) as unrelated Arb balls.  The next implementation
should parameterize \(B,\tau,A,\alpha,\ell,\beta,c,\kappa\) as functions of
\(\eta\) on each slab and compute divided quantities directly:

\[
\delta q=\frac{q-q_0}{\eta},\quad
\delta c=\frac{c-c_0}{\eta},\quad
\delta\kappa=\frac{\kappa-\kappa_0}{\eta},
\]

\[
\delta\rho=
\frac{\delta q-\delta c-\delta\kappa(\rho_0+\rho_0^{-1})}
{\kappa(1-1/(\rho\rho_0))},
\]

then apply the quotient rule to the residue

\[
a_q=
\frac{\kappa(\rho-\rho^{-1})}{D_q}
\left(d_A-\frac{q+A}{2(q-\alpha)}d_\alpha\right)
\]

so that \(\delta a_q\) is formed directly, rather than as
\((a_q-a_{q,0})/\eta\).  This is the most likely next implementation to move
the eta-interval enclosure from the current diagnostic stage toward a real
continuum Krawczyk certificate.

## J. Eta-Divided Residue Kernel Attempt

The first eta-divided residue-log implementation is now in code behind an
explicit diagnostic switch:

```bash
.venv/bin/python 1038/verify_two_interval_epsilon_slabs.py \
  1038/two_interval_branch_certificate_skeleton.json \
  --slab 0.00005:0.0001 \
  --center affine-endpoints \
  --uv-radii 0.01,0.01 \
  --arb-box-dk-subdivisions 1,2 \
  --dk11-eta-radius-report 16 \
  --dk11-sample-grid 2 \
  --eta-interval-dk-kernel residue-log
```

It does two things that the previous prototype did not do:

1. constructs \(A,\alpha\) from the same Arb \(\eta\)-box via
   \(A=A_0+\eta(\nu\tau+B)\), \(\alpha=\alpha_0+\eta\tau\);
2. replaces the explicit subtraction quotients in the paired residue-log
   primitive by eta-divided preimage, branch-value, residue, and log-ratio
   quotients.

At point values, this kernel matches the analytic Jacobian.  For example, at
\(\varepsilon=10^{-4}\) it gives

```text
residue-log DK[1,1] = -0.4332281104105087...
analytic DK[1,1]    = -0.4332281104058441...
```

But as an interval kernel it is not yet the right closure.  On the first
small-\(\varepsilon\) slab, with the same \(u,v\) radii, it reports:

```text
kernel=acb, eta_subdivisions=16
  max_interval_radius=1.173797e+00
  worst_sample=[-4.343975e-01,-4.299223e-01]

kernel=residue-log, eta_subdivisions=16
  max_interval_radius=2.180000e+00
  worst_sample=[-4.373654e-01,-4.328054e-01]
```

So the new formula is algebraically consistent but still too wide.  The
remaining obstruction is exactly the phrase "common rational expression": the
implementation divides each preimage/residue/log factor, then adds them.  It
has not yet combined the full paired smooth contribution into one rational-log
expression before Arb evaluation.  That next step must cancel the removable
\(\eta\)-factors across the whole \(\ell/r\) pair first, and only then enclose
the resulting expression.

For this reason the production default remains the older `acb` kernel; the
`residue-log` kernel is kept as a checked diagnostic path, not as a claimed
tightening.

## K. Remote Slab Matrix After Eta Refinement

The remote 24-core machine was used as a parallel diagnostic runner for the
current adjacent epsilon slabs.  A small driver,
`parallel_slab_diagnostics.py`, now fans out radius-report jobs; it does not
change the verifier or the certificate logic.

The key continuum check is the actual interval Krawczyk pass/fail matrix, not
the radius report.  With the production `acb` kernel, affine endpoint centers,
and `--eta-interval-dk-check`, the first two small epsilon slabs now close if
the eta subdivision is increased to 224 and the \(u,v\) radius is reduced to
`0.0003,0.0003`:

```text
slab=0.00005:0.0001, radius=0.0003, eta=224
  PASS, worst_margin=1.476235e-04

slab=0.0001:0.0002, radius=0.0003, eta=224
  PASS, worst_margin=1.354100e-04
```

The next three adjacent slabs did not close under the same certification
setup.  At eta 224 the failures were:

```text
slab=0.0002:0.0005, radius=0.0003
  FAIL, margin=-5.605783e-04, dominant=defect

slab=0.0005:0.001, radius=0.0003
  FAIL, margin=-5.999470e-04, dominant=defect

slab=0.001:0.002, radius=0.0003
  FAIL, margin=-4.228079e-04, dominant=correction
```

Increasing eta further does help, but it does not by itself close the
remaining slabs.  The high-eta remote run gave:

```text
slab=0.0002:0.0005, radius=0.0003, eta=448
  FAIL, margin=-5.174021e-04, dominant=defect

slab=0.0005:0.001, radius=0.0003, eta=448
  FAIL, margin=-1.375342e-04, dominant=correction

slab=0.0005:0.001, radius=0.0003, eta=896
  FAIL, margin=-2.202244e-05, dominant=correction

slab=0.001:0.002, radius=0.0003, eta=448
  FAIL, margin=-4.060184e-04, dominant=correction

slab=0.001:0.002, radius=0.0003, eta=896
  FAIL, margin=-3.434002e-04, dominant=correction

slab=0.001:0.002, radius=0.0006, eta=896
  FAIL, margin=-2.656767e-04, dominant=correction
```

The single `slab=0.0002:0.0005, eta=896` job was terminated after the other
high-eta jobs completed because it was the only remaining long-running
process and the eta 448 result was still clearly defect-dominated.  This is
enough to identify the next obstruction: the route is no longer blocked
uniformly by the first eta singularity.  Two slabs close.  The third still
needs a tighter DK/defect enclosure, while the top two slabs need a better
center/radius strategy or a refined continuation step because the Krawczyk
correction is comparable with, or larger than, the allowed box radius.

## L. Four Of Five Adjacent Slabs Closed By Tuning

The next remote-only tuning pass was run after the section K matrix.  It did
not change the center model; it only tuned the Krawczyk box radius and eta
subdivision count in the existing `affine-endpoints` verifier.

The third slab, which previously failed by about \(5\times 10^{-4}\), closes
in a narrow radius window:

```text
slab=0.0002:0.0005, radius=0.00028, eta=1344
  PASS, worst_margin=6.622592e-06

slab=0.0002:0.0005, radius=0.00029, eta=1344
  PASS, worst_margin=1.640791e-05
```

The fourth slab also closes once the radius is increased enough to absorb the
sampled center correction but not so much that the DK defect dominates:

```text
slab=0.0005:0.001, radius=0.0004, eta=896
  PASS, worst_margin=7.475216e-05

slab=0.0005:0.001, radius=0.0004, eta=1344
  PASS, worst_margin=7.527316e-05

slab=0.0005:0.001, radius=0.0006, eta=1344
  PASS, worst_margin=2.686209e-04

slab=0.0005:0.001, radius=0.0008, eta=1344
  PASS, worst_margin=3.580990e-05
```

Together with section K, this gives a four-slab diagnostic closure:

```text
0.00005:0.0001   PASS, radius=0.0003,  eta=224
0.0001:0.0002    PASS, radius=0.0003,  eta=224
0.0002:0.0005    PASS, radius=0.00029, eta=1344
0.0005:0.001     PASS, radius=0.0006,  eta=1344
0.001:0.002      open in this verifier
```

The remaining top slab was improved but not closed:

```text
slab=0.001:0.002, radius=0.0008,  eta=1344
  FAIL, margin=-2.030082e-04, dominant=defect

slab=0.001:0.002, radius=0.00065, eta=2688
  FAIL, margin=-1.115617e-04, dominant=correction

slab=0.001:0.002, radius=0.0009,  eta=2688
  FAIL, margin=-1.682608e-04, dominant=defect
```

Seven `eta=4096` top-slab jobs in the radius window
`0.00060..0.00070` were terminated after more than fifteen minutes without
producing a result.  That is a useful negative signal: the last slab should
not be attacked by simply increasing eta subdivisions.  The next mathematical
cut is to add a better continuation/center model for the top slab, or split
the row-to-row continuation before applying the same Krawczyk box.
