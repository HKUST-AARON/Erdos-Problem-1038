# 547 - 树的 Ramsey 数上界：严格复核版

## 题号
547

## 精确题目（官网字面）

> If $T$ is a tree on $n$ vertices then
> \[
> R(T) \leq 2n-2.
> \]

来源/语境：

- Erdős Problems #547: https://www.erdosproblems.com/547
- LaTeX: https://www.erdosproblems.com/latex/547
- Definitions: https://www.erdosproblems.com/definitions

官网状态：`DECIDABLE`，即 *Resolved up to a finite check*。

最后复核日期：2026-05-01。

---

## 0. 结论先行

### 0.1 字面形式化命题

若严格按“有限图”定义允许单点树 $K_1$，并按通常 Ramsey 数定义取最小正整数 $N$，则官网字面命题是 **false**。

反例：

\[
T=K_1,\qquad n=1.
\]

此时

\[
R(K_1)=1,
\]

但

\[
2n-2=0.
\]

于是题面断言变成

\[
1\le 0,
\]

矛盾。

所以：

\[
\boxed{\text{字面全称命题若包括 } n=1 \text{，则被 } K_1 \text{ 严格证伪。}}
\]

### 0.2 数学本意 / 非平凡树版本

若修正为

\[
n\ge 2,
\]

或写成“非平凡树”，则这不是一个已被 $n=1$ 反例推翻的数学猜想，而是 Burr--Erdős 树 Ramsey 数上界问题的本体。

当前可严谨说法是：

\[
\boxed{\text{对充分大的 } n \text{ 已知成立；全体小 } n \text{ 仍需有限检查或额外证明。}}
\]

因此，不应提交为“推翻 Burr--Erdős 猜想”。可以提交为：

> 当前字面表述缺少边界条件；若允许 $K_1$，则应补充 $n\ge2$ 或“nontrivial tree”。

---

## 1. 官方资料复核

### 1.1 官网 #547

官网 #547 写明：

\[
R(T)\le 2n-2
\]

并标为 `DECIDABLE / Resolved up to a finite check`。

官网还说明：

- 该命题可由 Erdős--Sós 猜想推出；
- Ajtai--Komlós--Simonovits--Szemerédi 曾宣布相关大 $n$ 证明，但未发表；
- Zhao 已通过另一方法证明 $R(T)\le 2n-2$ 对所有充分大的 $n$ 成立。

参考：

- https://www.erdosproblems.com/547

### 1.2 官网 Definitions

官网定义中写：对任意有限图 $G,H$，$R(G,H)$ 是使任意 $K_N$ 的红蓝二染色含红 $G$ 或蓝 $H$ 的最小 $N$；若 $G=H$，记作 $R(G)$。

参考：

- https://www.erdosproblems.com/definitions

这里没有显式排除 $K_1$。因此，作为形式化命题，$K_1$ 边界必须被处理。

### 1.3 相关 Erdős--Sós 问题 #548

官网 #548 当前标为 `FALSIFIABLE / Open, but could be disproved with a finite counterexample`，且注明该问题 implies #547。

参考：

- https://www.erdosproblems.com/548

这说明不能把 “#547 可由 #548 推出” 写成 “#547 已由 #548 完全证明”。

---

## 2. 对外部代理稿的严格审查

外部代理稿的核心说法分成两部分：

1. 用 $n=1$ 证伪字面命题；
2. 用 Loebl--Komlós--Sós / Zhao 机制解释 $n\ge2$ 的实质命题。

逐条审查如下。

### 2.1 关于 $S_1$：$n=1$ 反例

结论：**正确，但只击中字面边界。**

取

\[
T=K_1,
\qquad n=1.
\]

$K_1$ 是一棵树。任意 $K_N$ 在 $N\ge1$ 时都包含一个 $K_1$。因此

\[
R(K_1)=1.
\]

题面右端为

\[
2n-2=0.
\]

所以字面不等式失败。

局部复核：

- 未使用额外假设；
- 反例依赖“允许单点树”这一正常图论约定；
- 该反例不涉及任何深层 Ramsey 理论；
- 它只能证明题面需加 $n\ge2$，不能证明非平凡树版本错误。

### 2.2 关于 $S_2,S_3$：度数鸽巢

结论：**正确。**

设 $n\ge2$，令

\[
N=2n-2.
\]

对 $K_N$ 任意红蓝染色，记红图和蓝图为 $G_R,G_B$。对任意顶点 $v$，有

\[
d_R(v)+d_B(v)=N-1=2n-3.
\]

因此

\[
\max\{d_R(v),d_B(v)\}\ge n-1.
\]

令

\[
V_R=\{v:d_R(v)\ge n-1\},
\qquad
V_B=\{v:d_B(v)\ge n-1\}.
\]

则

\[
V_R\cup V_B=V(K_N).
\]

于是

\[
|V_R|+|V_B|\ge N=2n-2.
\]

故至少一个颜色满足：有至少

\[
\frac N2=n-1
\]

个顶点度数至少

\[
n-1=\frac N2.
\]

这一步完全正确，是 Zhao/Loebl 路线的标准 Ramsey 化入口。

### 2.3 关于 $S_4$：调用 LKS

结论：**参数对齐正确，但“完整闭环”表述错误。**

Loebl 的 $(N/2-N/2-N/2)$ 猜想说：若一个 $N$ 顶点图中至少 $N/2$ 个顶点度数至少 $N/2$，则该图包含所有至多 $N/2$ 条边的树。

如果这个命题对所有 $N$ 成立，则对 $N=2n-2$ 可推出：任意 $n$ 顶点树 $T$ 满足

\[
e(T)=n-1=\frac N2,
\]

因此某个颜色图含有 $T$，从而

\[
R(T)\le 2n-2.
\]

但是，公开文献和官网目前可直接引用的是：Zhao 证明了该 Loebl 型命题对充分大的 $N$ 成立，从而推出 #547 对充分大的 $n$ 成立。

因此，外部代理稿中如下说法过强：

- “Loebl--Komlós--Sós 定理”若被当作全参数定理使用，是未获公开全闭环支持的；
- “完成 $n\ge2$ 时的证明闭环”不成立；
- “等价规约”表述不严谨。这里得到的是

\[
\text{Loebl 型嵌入命题}\Longrightarrow \text{树 Ramsey 上界},
\]

而不是反向等价。

---

## 3. 严格数学部分

### 3.1 字面命题的反例

**命题（字面版）**：若 $T$ 是 $n$ 个顶点的树，则 $R(T)\le2n-2$。

**反例**：取 $T=K_1$。

则

\[
n=1.
\]

由于 $K_1$ 自身已经包含 $K_1$，且 $K_0$ 不含顶点，故

\[
R(K_1)=1.
\]

但

\[
2n-2=0.
\]

所以

\[
R(K_1)=1>0=2n-2.
\]

因此字面全称命题为假。

\[
\boxed{\text{证毕。}}
\]

### 3.2 修正命题的 Loebl/Zhao 推导

**修正命题**：若 $n\ge2$ 且 $T$ 是 $n$ 顶点树，则 $R(T)\le2n-2$。

这个修正命题的完整全参数证明目前不能从公开已知结果直接宣称完成；但其大 $n$ 版本可由 Zhao 的结果推出。

证明机制如下。

令

\[
N=2n-2.
\]

任取 $K_N$ 的红蓝染色。对每个顶点 $v$，

\[
d_R(v)+d_B(v)=N-1=2n-3.
\]

于是

\[
d_R(v)\ge n-1
\quad\text{或}\quad
 d_B(v)\ge n-1.
\]

定义

\[
V_R=\{v:d_R(v)\ge n-1\},
\qquad
V_B=\{v:d_B(v)\ge n-1\}.
\]

则

\[
V_R\cup V_B=V(K_N),
\]

从而

\[
|V_R|+|V_B|\ge N=2n-2.
\]

所以某个颜色图 $G$ 中至少有

\[
\frac N2=n-1
\]

个顶点的度数至少

\[
n-1=\frac N2.
\]

而 $T$ 是 $n$ 顶点树，故

\[
e(T)=n-1=\frac N2.
\]

若可调用 Loebl 的 $(N/2-N/2-N/2)$ 嵌入命题，则 $G$ 含有 $T$。于是染色中存在单色 $T$，即

\[
R(T)\le N=2n-2.
\]

Zhao 已证明上述 Loebl 型命题对充分大的 $N$ 成立，所以得到：

\[
\boxed{\text{对充分大的 } n\text{，修正命题成立。}}
\]

---

## 4. 可以提交什么，不能提交什么

### 4.1 可以提交

可以向问题库或形式化项目提交如下边界修正意见：

```text
There is a boundary issue in the literal statement of Problem #547.
Under the site definition of R(G), finite graphs are not restricted to have at least one edge.
Taking T = K_1 gives n = 1 and R(K_1) = 1, while 2n - 2 = 0.
Hence the displayed statement is literally false unless one adds n >= 2 or restricts to nontrivial trees.
This does not refute the intended Burr--Erdos tree Ramsey problem; it only shows that the formal statement needs a boundary condition.
```

中文版本：

```text
#547 的字面表述存在边界漏洞。按官网对 R(G) 的定义，并没有显式排除单点图。
取 T=K_1，则 n=1，R(K_1)=1，而 2n-2=0，因此题面不等式字面为假。
建议补充 n>=2 或“非平凡树”。这不是推翻 Burr--Erdos 树 Ramsey 问题本身，而是指出当前形式化表述漏了边界条件。
```

### 4.2 不应提交

不应提交如下说法：

```text
I disproved the Burr--Erdos tree Ramsey conjecture.
```

原因：$n=1$ 只是边界形式化漏洞。该反例不会影响 $n\ge2$ 的数学本体，也不会构造出任何非平凡树 $T$ 满足

\[
R(T)>2n-2.
\]

### 4.3 对“有人号称证明出来”的审稿意见

若对方证明只包含以下链条：

\[
\text{度数鸽巢}\Rightarrow\text{Loebl 条件}\Rightarrow\text{单色 }T,
\]

则应要求其明确：

1. 调用的是哪个版本的 Loebl--Komlós--Sós 命题；
2. 该版本是否为全参数已发表定理；
3. 是否覆盖所有 $n\ge2$；
4. 若只覆盖充分大 $n$，剩余有限 $n$ 的检查证书在哪里。

如果没有第 2--4 项，则该证明不是 #547 的完整证明。

---

## 5. 当前闭环状态

| 版本 | 状态 | 说明 |
|---|---:|---|
| 字面命题，允许 $n=1$ | false | 反例 $T=K_1$，$R(K_1)=1>0=2n-2$ |
| 修正命题 $n\ge2$ | 未完全纸面闭环 | 官网标为 `DECIDABLE`，即充分大 $n$ 已处理，剩有限检查 |
| 修正命题，充分大 $n$ | true | Zhao 2011 由 Loebl 型定理推出 |
| 外部代理稿所谓“完全闭环证明” | 不成立 | LKS 被过度当成全参数定理；“等价规约”也过强 |

最终建议：

\[
\boxed{\text{提交“边界条件漏洞/形式化反例”可以；提交“著名猜想被证伪”不可以。}}
\]

---

## 6. 原统一提问提示词（保留）

请直接贴给模型的提示词（用于 GPT-5.5 Pro 和 Gemini 同时）：

你是数学证明代理，任务是把上面的题目一步一步完整解出来，不要写“这题很困难”或停留在难度评价。  
按这个流程输出：  

1. 先给“命题状态与目标”：明确是要证明存在/不存在，或给等价命题。  
2. 先检索并提取该题在官方网站/评论区/相关网页中的公开证明、反例、讨论；若存在别人的证明或关键思路，要逐条对齐后再决策是否采用。  
3. 列出全部输入与边界：变量范围、定义、已知条件、退化情形。  
4. 给出整体策略，并拆成子目标 $S_1,S_2,\dots,S_m$。  
5. 对每个 $S_i$ 按“前提 → 推导 → 结论”完整写出，不得跳步。  
6. 每完成一个 $S_i$，立刻做局部复核：  
   5.1 是否用了未声明假设；  
   5.2 是否漏掉小参数边界；  
   5.3 是否可直接推到下一步。  
7. 若发现漏洞，返回该步重写后再继续；不要跳过。  
8. 在整题末尾做一次“反向复核”：从结论反推关键引理，确认与题面一致。  
9. 最后给“当前闭环状态”。闭环即输出完整证明；未闭环则给下一步修复动作并继续。
