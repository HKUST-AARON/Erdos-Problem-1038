# 835 - 二元超图着色覆盖问题

## 题号
835

## 精确题目
Does there exist a $k>2$ such that the $k$-sized subsets of $\{1,\ldots,2k\}$ can be coloured with $k+1$ colours such that for every $A\subset \{1,\ldots,2k\}$ with $|A|=k+1$, all $k+1$ colours appear among the $k$-sized subsets of $A$?

来源/语境：  
https://www.erdosproblems.com/835  
https://www.erdosproblems.com/latex/835  
状态：verifiable

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
