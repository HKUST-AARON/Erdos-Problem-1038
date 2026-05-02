# 1038 - 实根单调多项式上小值区间测度的上下确界

## 题号
1038

## 精确题目
Determine the infimum and supremum of
\[
\left| \{ x\in \mathbb{R} : |f(x)| < 1\}\right|
\]
as $f\in \mathbb{R}[x]$ ranges over all non-constant monic polynomials, all of whose roots are real and in the interval $[-1,1]$.

## 来源/语境
https://www.erdosproblems.com/1038  
https://www.erdosproblems.com/latex/1038

状态：open（网站标注为当前未有已知完整结论）。

当前进展摘要：
- 问题仍未闭合。
- 在 Tao/natso 标准 reduction 下，当前本地 certificate-backed lower-bound package 为 \(\,L_-\ge1.8063\,\)。
- 三原子部分：固定平移三原子已严谨化到 \(1.7877\)，但 comments 中变量权重三原子数值路线约到 \(1.7902\)，所以固定三原子不是前沿。
- 四/五原子部分：二维 conservative forcing family 已有 interval-box certificate；四原子 final block 到 \(1.8036\)，五原子 final block 到 \(1.8063\)。

备注：Terence Tao（TerenceTao）也在该题评论/讨论中出现，值得先检索其相关讨论或公开思路。

本地早期进展记录：已在 Tao/natso reduction 框架下写入一个三原子 finite certificate，得到
\[
L_-\ge1.7875.
\]
该结果不闭合 exact infimum，但可作为 forum-ready lower-bound progress；详见 `1038_dual_two_interval_progress.md` 第 8 节与 `1038_tao_ready_next_step_sup_closed.md` 第 4 节。

后续增强状态：固定三原子 \(1.7877\) 已通过可复现的高精度 one-variable verifier PASS；保守 \(1.8\) 路线的二维 forcing family 已通过 finite interval-box certificate；最终 finite-atom block 现在由五原子 \(1.8063\) 版本给出。这里仍不是 proof assistant 级别的完整 Mathlib 证明。

## 统一提问提示词（可直接粘贴）

请直接贴给模型的提示词（用于 GPT-5.5 Pro 和 Gemini 同时）：

你是数学证明代理，任务是把上面的题目一步一步完整解出来，不要写“这题很困难”或停留在难度评价。  
按这个流程输出：  

1. 先给“命题状态与目标”：明确是要证明存在/不存在，或给等价命题。  
2. 先检索并提取该题在官方网站/评论区/相关网页中的公开证明、反例、讨论；若存在别人的证明或关键思路，要逐条对齐后再决策是否采用。  
3. 若页面显示有 Terence Tao 等人的讨论，先提取其关键思路并与自己的框架对齐。  
4. 列出全部输入与边界：变量范围、定义、已知条件、退化情形。  
5. 给出整体策略，并拆成子目标 $S_1,S_2,\dots,S_m$。  
6. 对每个 $S_i$ 按“前提 → 推导 → 结论”完整写出，不得跳步。  
7. 每完成一个 $S_i$，立刻做局部复核：  
   7.1 是否用了未声明假设；  
   7.2 是否漏掉小参数边界；  
   7.3 是否可直接推到下一步。  
8. 若发现漏洞，返回该步重写后再继续；不要跳过。  
9. 在整题末尾做一次“反向复核”：从结论反推关键引理，确认与题面一致。  
10. 最后给“当前闭环状态”。闭环即输出完整证明；未闭环则给下一步修复动作并继续。
## 2026-05-02 proof-package update

The finite-atom lower-bound work now has the following status.

\[
\boxed{1.8063\le L_-}
\]

is proven conditionally on the standard Tao/natso reduction to normalized
minimizers satisfying

\[
\mu(\{-1\})\ge\frac12,\qquad
\operatorname{supp}\mu\subseteq\{-1\}\cup[0,1].
\]

What changed:

- The earlier three-atom safe bound \(1.7875\) has been strengthened to a
  reproducible fixed-shift \(1.7877\) one-variable certificate.  This is not
  the comments frontier for all three-atom variants: the variable-weight
  three-atom numerical route in the discussion reaches about \(1.7902\).
- The high-margin four-atom block that adds the final \(0.1\) length after
  \((-1.7,0)\subset E_\mu\) is verified.
- A stronger four-atom block now reaches \([-1.8036,-1.7]\), adding \(0.1036\)
  length after \((-1.7,0)\subset E_\mu\), and upgrading the four-atom
  conditional lower bound to \(1.8036\).
- A stronger five-atom block on \([-1.804,-1.7]\) now adds \(0.104\) length,
  upgrading the conditional lower bound from \(1.803\) to \(1.804\).
- A five-atom block on \([-1.805,-1.7]\) now adds \(0.105\) length, upgrading
  the conditional lower bound from \(1.804\) to \(1.805\).
- A five-atom block on \([-1.806,-1.7]\) now adds \(0.106\) length, upgrading
  the conditional lower bound from \(1.805\) to \(1.806\).
- A five-atom block on \([-1.8063,-1.7]\) now adds \(0.1063\) length, upgrading
  the conditional lower bound from \(1.806\) to \(1.8063\).  This is currently
  the strongest certificate-backed finite-atom lower-bound package here.
- The two-parameter forcing family used to prove
  \[
  |E_\mu|<1.8\Rightarrow (-1.7,0)\subset E_\mu
  \]
  is no longer only a grid check.  It is covered by a finite interval-box
  verifier in `1038/verify_conservative_forcing_interval.py`.
- The Lean executable certificate in `1038/LeanCertificates.lean` now runs:
  three-atom \(1.7877\), four-atom blocks through \(1.8036\), five-atom blocks
  through \(1.8063\), and the conservative forcing interval-box check.  All
  pass.
- The exact-infimum route is now the corrected two-interval finite-gap ansatz
  with endpoint atom at \(1\).  The diagnostic solver
  `1038/solve_two_interval_finite_gap.py` finds a valid small-\(\varepsilon\)
  branch for \(\varepsilon=0.02\) down to \(0.0005\), plus the limiting system
  at \(\varepsilon=0\).  The next hard proof task is the
  singular/interval parameter-branch theorem in \(\eta=\sqrt{\varepsilon}\).
- `1038/FormalSkeleton.lean` now formalizes the proof pipeline as a conditional
  theorem from explicit assumptions/certificates, without pretending to
  formalize real measure or logarithmic potential theory.
- The two-dimensional interval-box certificate has been fixed into
  `1038/conservative_forcing_interval_certificate.json`; the checker can now
  re-check this JSON certificate independently of the recursive search.
- The duality step has been patched to use shifted truncated kernels, avoiding
  the invalid shortcut of applying a finite-energy identity to a measure with
  a possible atom at \(-1\).

Remaining caveat: this is still not a full proof of the conjectural exact
infimum \(1.8344304757\ldots\).  The exact route still needs a global dual
certificate for general candidate sets, likely via the corrected two-interval
Cauchy-transform ansatz with endpoint atoms and continuous density.
