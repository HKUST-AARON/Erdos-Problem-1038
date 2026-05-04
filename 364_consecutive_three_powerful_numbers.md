# 364 - 连续三正整数是否全为 powerful 数

## 题号
364

## 精确题目
Are there any triples of consecutive positive integers all of which are powerful (i.e. if $p\mid n$ then $p^2\mid n$)?

来源/语境：  
https://www.erdosproblems.com/364  
https://www.erdosproblems.com/latex/364  
状态：verifiable（有一定计算与理论约束）

## 统一提问提示词（可直接粘贴）

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

## 2026-05-02 推进记录

### 已严格证明的核心降维

设潜在三连 powerful 数为

$$
x,\ x+1,\ x+2.
$$

则中间项必为偶数且被 $4$ 整除。等价地，若改写为

$$
P-1,\ P,\ P+1,
$$

则 $P$ 必为偶 powerful 数，且原问题严格等价于：

> 是否存在偶 powerful 数 $P$，使得 $P^2-1$ 也是 powerful 数？

证明要点：

1. 三个连续整数不能呈“偶-奇-偶”，否则两个偶端点相差 $2$，其中一个只含一个因子 $2$，不是 powerful。
2. 因此只能呈“奇-偶-奇”，中间项 $P$ 为偶 powerful，故 $4\mid P$。
3. $P-1$ 与 $P+1$ 是相差 $2$ 的奇数，故互素。
4. 互素整数 $A,B$ 满足：$AB$ powerful 当且仅当 $A,B$ 分别 powerful。
5. 因而 $P-1,P,P+1$ 全 powerful 当且仅当 $P$ powerful 且 $(P-1)(P+1)=P^2-1$ powerful。

### 模 36 必要条件

由 $4\mid P$ 与三个连续整数中恰有一个被 $3$ 整除，而 powerful 条件迫使该项被 $9$ 整除，可得起点 $x=P-1$ 必满足

$$
x\equiv 7,\ 27,\ 35 \pmod {36}.
$$

这只是必要条件，不是充分条件。

### 有限局部筛不可能单独闭合

对任意素数 $p$，三连组起点 $x$ 的局部 powerful 条件是：

$$
\text{不存在 } i\in\{0,1,2\}\text{ 使 }p\mid x+i\text{ 但 }p^2\nmid x+i.
$$

因此在模 $p^2$ 下，坏类为

$$
x\equiv -i+tp \pmod {p^2},
\quad i\in\{0,1,2\},\quad t=1,\dots,p-1.
$$

当 $p\ge 3$ 时，三个 $i$ 对应的坏类互不相交，所以允许类数量为

$$
p^2-3(p-1)=p^2-3p+3.
$$

当 $p=2$ 时，唯一允许类为

$$
x\equiv 3\pmod 4.
$$

更重要的是：对任意有限素数集合 $S$，这些局部条件永远不会推出矛盾。证明如下。

取

$$
x\equiv 3\pmod 4
$$

并且对每个奇素数 $p\in S$ 取

$$
x\equiv 0\pmod {p^2}.
$$

由于模数两两互素，中国剩余定理保证存在这样的 $x$。此时对每个奇素数 $p$，$x$ 被 $p^2$ 整除，而 $x+1,x+2$ 不被 $p$ 整除；对 $p=2$，$x,x+1,x+2$ 的模 $4$ 形态为 $3,0,1$，也没有只含一个因子 $2$ 的项。

所以任何“只靠有限多个模 $p^2$ 约束”的路线都不能证明不存在三连 powerful 数；必须引入全局机制。

### 标准全局参数化

每个 powerful 数可唯一写成

$$
n=a^2b^3,
$$

其中 $b$ 平方因子自由。于是三连 powerful 数等价于存在正整数 $a,c,e$ 与平方因子自由正整数 $b,d,f$，满足

$$
c^2d^3-a^2b^3=1,
$$

$$
e^2f^3-c^2d^3=1.
$$

这把问题变成两个相邻 generalized Pell/Mordell 型方程的交叉问题。固定 $b,d,f$ 后可进入 Pell 方程、椭圆曲线或 Thue 方程工具；但 $b,d,f$ 不固定，因此仍是开放难点。

### abc 条件下的有限性证明

若假设 abc 猜想，则三连 powerful 数至多有限个。

证明：由恒等式

$$
x(x+2)+1=(x+1)^2
$$

对三元组

$$
A=x(x+2),\quad B=1,\quad C=(x+1)^2
$$

应用 abc。因 $x,x+1,x+2$ 均 powerful，有

$$
\operatorname{rad}(x+i)\le \sqrt{x+i}.
$$

所以

$$
\operatorname{rad}(ABC)
=\operatorname{rad}(x(x+1)(x+2))
\le \sqrt{x(x+1)(x+2)}
\le (x+2)^{3/2}.
$$

取任意 $\varepsilon<1/3$，abc 给出常数 $K_\varepsilon$ 使

$$
(x+1)^2
\le K_\varepsilon\,\operatorname{rad}(ABC)^{1+\varepsilon}
\le K_\varepsilon (x+2)^{\frac32(1+\varepsilon)}.
$$

由于

$$
\frac32(1+\varepsilon)<2,
$$

上式只能对有限多个 $x$ 成立。因此 abc 猜想推出潜在反例有限。

这仍不是无条件证明，因为 abc 本身未解决。

### 当前计算边界

用表示

$$
n=a^2b^3,\quad b\text{ squarefree}
$$

生成所有不超过 $10^{13}$ 的 powerful 数，并检查连续三项，未发现反例。

本地运行结果：

```text
N=10000000000000
powerful_count=6840384
triple_hits_count=0
```

该计算支持猜想，但不构成证明。

### 当前判断

同余筛方向是正确的必要条件方向，但已经证明它无法靠有限局部条件闭合。若继续推进，必须转向全局路线：

1. 固定平方因子自由核 $(b,d,f)$ 后做 Pell/椭圆/Thue 分解；
2. 寻找能控制可变核 $(b,d,f)$ 的高度或 radical 不等式；
3. 尝试把 $P^2-1$ powerful 转化为关于 $P-1,P+1$ 的互素 squarefull pair 交叉定理。
