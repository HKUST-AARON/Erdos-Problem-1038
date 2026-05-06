# Erdős 数学问题 — Code Wiki

## 1. 项目概述

本仓库是一个面向 **Erdős 开放数学问题** 的形式化验证与数值探索项目，核心聚焦于 **Erdős Problem #1038**（首一多项式正集测度的下界问题），同时包含对 Erdős Problem #364（连续三个 powerful 数）和 Erdős Problem #547（树 Ramsey 数上界）的辅助研究。

项目采用 **Lean 4 + Mathlib** 进行形式化证明，**Python + NumPy/SciPy** 进行数值验证与候选搜索，形成"数值搜索 → 证书生成 → 形式化验证"的完整闭环。

### 核心数学问题

**Erdős Problem #1038**：对于所有根为实数且落在 $[-1,1]$ 中的非常数首一多项式 $f$，确定

$$|\{x \in \mathbb{R} : |f(x)| < 1\}|$$

的下确界与上确界。当前已知下界约为 1.519，上确界为 $2\sqrt{2}$。本仓库通过有限原子对偶强制（finite-atom dual forcing）路线，将下界推进至 **1.814600**。

---

## 2. 项目整体架构

```
erdos数学问题/
├── README.md                          # 项目主入口文档
├── lakefile.toml                      # Lean 4 项目配置（根级）
├── lean-toolchain                     # Lean 工具链版本 v4.30.0-rc2
├── lake-manifest.json                 # Lean 依赖锁定文件
├── .gitignore
│
├── 1038/                              # Problem 1038 早期/实验性工作区
│   ├── README.md
│   ├── FormalSkeleton.lean            # 条件性下界的逻辑骨架
│   ├── LeanCertificates.lean          # Float 诊断性证书检查器
│   ├── FiveAtom1806304Formal.lean     # 五原子形式化骨架
│   ├── FiveAtom1806304Mathlib.lean    # 五原子 Mathlib 层
│   ├── certificates/                  # JSON/MD 证书文件
│   ├── scripts/                       # 证书生成与验证脚本
│   ├── two_interval_finite_gap_small_eta/  # 双区间有限间隙求解器
│   └── *.py                           # 各类数值验证脚本
│
├── finite_atoms/                      # ★ 核心形式化验证模块
│   ├── check_all.sh                   # 全量验证入口脚本
│   ├── common/                        # 共享有限原子框架
│   │   ├── lean/
│   │   │   ├── FiniteAtomFramework.lean
│   │   │   ├── StandardReduction.lean
│   │   │   └── OuterBridges.lean
│   │   └── README.md
│   ├── forcing_1708/                  # 强制分支证书 (M=1.708)
│   │   ├── lean/                      # Lean 形式化（含 chunk 分片）
│   │   ├── scripts/
│   │   ├── lakefile.toml
│   │   └── README.md
│   ├── five_atom_1807100/             # 五原子尾部证书 (M=1.807100)
│   │   ├── lean/
│   │   ├── lakefile.toml
│   │   └── README.md
│   ├── piecewise_five_atom_181460_560/ # 分段五原子证书 (M=1.814600, 560块)
│   │   ├── lean/
│   │   │   ├── box_list_chunks/       # 560 个生成的 Lean chunk 文件
│   │   │   ├── PiecewiseFiveAtom181460Mathlib.lean
│   │   │   ├── PiecewiseFiveAtom181460Formal.lean
│   │   │   ├── PiecewiseFiveAtom181460BoxCore.lean
│   │   │   ├── PiecewiseFiveAtom181460BoxListCore.lean
│   │   │   └── PiecewiseFiveAtom181460Weights.lean
│   │   ├── certificates/
│   │   ├── data/
│   │   ├── scripts/
│   │   └── README.md
│   ├── route_1807100/                 # M=1.807100 路由闭包
│   │   └── lean/Route1807100Closure.lean
│   └── route_181460_560/              # M=1.814600 路由闭包
│       └── lean/Route181460Closure.lean
│
├── remote_364/                        # Erdős Problem #364 研究
│   ├── powerful_triples_search.py     # 连续 powerful 数搜索
│   ├── openevolve_initial.py          # OpenEvolve 过滤器初始程序
│   ├── openevolve_evaluator.py        # OpenEvolve 评估器
│   ├── check_filter_shrink.py         # 过滤器收缩检查
│   ├── openevolve_config.yaml         # OpenEvolve 配置
│   └── run_openevolve.sh
│
├── scripts/
│   └── odd_cover_z3.py                # 奇数模覆盖系统 Z3 验证器
│
├── erdos_open_problems_2026-05-01.md  # 694 道开放问题完整索引
├── 547_tree_ramsey_bound-pro.md       # Problem #547 树 Ramsey 上界分析
│
├── check_*.lean                       # 根级 Lean 辅助检查文件（~40个）
├── tmp_*.lean                         # 临时 Lean 实验文件（~30个）
├── SRtailCheck.lean                   # 尾部检查
└── ScratchCheck.lean                  # 临时验证
```

---

## 3. 主要模块职责

### 3.1 `finite_atoms/common/` — 共享有限原子框架

**职责**：提供所有有限原子证书路线共享的基础引理和接口。

| 文件 | 职责 |
|------|------|
| `FiniteAtomFramework.lean` | 有限对偶强制核心引理：若正权重有限原子和为正，且正集外原势非正，则至少一个原子落在正集内 |
| `StandardReduction.lean` | 标准归约结论：归一化端点质量条件下，基线区间 $(-\sqrt{2}, 0) \setminus \{-1\}$ 被强制进入正集 |
| `OuterBridges.lean` | 外层桥接引理：多项式-势函数恒等式、紧致性/下半连续性极小化子存在性 |

#### 关键定义与定理

- **`Atom`** 结构体：包含位置 `x : ℝ` 和权重 `w : ℝ`
- **`weightedPotentialSum`**：加权势和计算
- **`finite_dual_forcing`**：有限对偶强制定理
- **`finite_atom_selector_from_duality`**：对偶到选择子的桥接定理
- **`three_atom_selector_from_duality`** / **`five_atom_selector_from_duality`**：三原子/五原子选择子
- **`PositiveSet`**：正集定义 $\{x : 0 < U(x)\}$
- **`BaselineInterval`**：基线区间 $Ioo(-\sqrt{2}, 0)$
- **`NormalizedEndpointPotential`**：归一化端点势接口
- **`StandardMinimizerReduction`**：标准极小化子归约接口

### 3.2 `finite_atoms/forcing_1708/` — 强制分支证书

**职责**：证明两参数强制分支，为长区间贡献 $1.708$ 的长度。

该分支使用参数 $a \in [-1.7, -\sqrt{2}]$，$s \in [0,1]$，构造三原子测度

$$\nu_{a,b} = \delta_a + (1.395 - b)\delta_b + C(a,b)\delta_{1.071-b}$$

其中 $b = s(1.82 + a)$，$C(a,b)$ 由 $U_{\nu_{a,b}}(-1) = 10^{-4}$ 确定。

| 文件 | 职责 |
|------|------|
| `Forcing1708Formal.lean` | 固定常数与域算术的形式化 |
| `Forcing1708Mathlib.lean` | 强制势函数定义与通用区间盒可靠性引理 |
| `Forcing1708AnalyticKernel.lean` | 可复用解析区间引理：Taylor/atanh 上下界、距离到对数界、系数 $C(a,b)$ 区间界 |
| `Forcing1708BoxData.lean` | 980 个有理盒的精确算术证明 |
| `Forcing1708CoverageIndex.lean` + `coverage_chunks/` | 有限覆盖见证表（15 个板片，23010 个单元） |
| `Forcing1708GeometryIndex.lean` + `geometry_chunks/` | 980 个盒的有理几何检查 |
| `Forcing1708AnalyticPreconditionsIndex.lean` + `analytic_precondition_chunks/` | 逐盒解析前提（12 项 atanh 展开） |
| `Forcing1708Aggregate.lean` | 聚合入口：导入并检查四个索引 |

#### 关键定义

- **`forcingPotential`**：两参数强制势函数
- **`cWeight`**：归一化系数 $C(a,b)$
- **`ADomain`** / **`SDomain`** / **`XDomain`**：参数域定义
- **`atanhLowerRat`** / **`atanhUpperRat`**：有理 atanh 上下界

### 3.3 `finite_atoms/five_atom_1807100/` — 五原子尾部证书

**职责**：证明五原子尾部块，贡献 $1.807100 - 1.708 = 0.099100$ 的长度。

对 $a \in [-1.807100, -1.708]$，使用五原子测度

$$\lambda_a = \delta_a + 1.18287976\delta_{a+1.80710376} + 0.03349753\delta_{a+2.57979789} + 0.11739956\delta_{a+2.69319012} + 0.17267833\delta_{a+2.79229832}$$

| 文件 | 职责 |
|------|------|
| `FiveAtom1807100Mathlib.lean` | 定义 $V(y)$、极点无关正性目标、可复用 Mathlib 对数估计 |
| `FiveAtom1807100BoxCertificate.lean` | 主形式化证书：通过有理区间盒覆盖证明极点无关正性 |
| `FiveAtom1807100Formal.lean` | 精确整数算术：临界括号、端点排序、扫过区间常数 |
| `FiveAtom1807100Route.lean` | 路由层：尾部长度、扫过区间不相交性、与强制阈值的兼容性 |

#### 关键定理

- **`poleFreeOneVariableLogPositivity_from_boxes`**：通过有理区间盒覆盖证明极点无关一变量对数正性
- **`tailSelector_measure_sum_lower_bound`** / **`tailSelector_length_sum_lower_bound`**：扫过长度下界

### 3.4 `finite_atoms/piecewise_five_atom_181460_560/` — 分段五原子证书

**职责**：证明 560 块分段五原子尾部证书，贡献 $1.814600 - 1.708 = 0.106600$ 的长度。

这是当前最强的证书包，使用 required-domain 解释：仅需在 $\{-1\} \cup [0,1]$ 上证明正性。

| 文件 | 职责 |
|------|------|
| `PiecewiseFiveAtom181460Mathlib.lean` | 定义分段五原子势、块参数化、required-domain 映射 |
| `PiecewiseFiveAtom181460Formal.lean` | 精确几何检查、块覆盖、扫过区间不相交性 |
| `PiecewiseFiveAtom181460BoxCore.lean` | 有理盒到实对数正性的 Mathlib 桥接 |
| `PiecewiseFiveAtom181460BoxListCore.lean` | 列式有理盒证书框架：`RatBox` 结构、覆盖判定、正性桥接 |
| `PiecewiseFiveAtom181460Weights.lean` | 560 个块的精确权重定义（10^12 缩放整数） |
| `box_list_chunks/PiecewiseFiveAtom181460BoxList*.lean` | 560 个生成的 Lean chunk，每个证明一个块的盒有效性、覆盖和正性 |

#### 关键定义

- **`RatBox`** 结构体：包含权重 `w1-w4`、区间 `[L,R]`、距离界 `D0-D4`
- **`RatBox.Valid`**：盒有效性谓词（权重非负、区间有序、距离正、下界正）
- **`RatBox.CoversFrom`**：递归覆盖判定（可由 `native_decide` 判定）
- **`requiredDomain`**：required-domain 定义 $[C-1, A-1] \cup [C, A+1]$
- **`V`**：五原子对数势函数

### 3.5 `finite_atoms/route_1807100/` 与 `route_181460_560/` — 路由闭包

**职责**：将强制分支贡献与尾部块贡献合并，完成最终路由闭包。

| 文件 | 职责 |
|------|------|
| `Route1807100Closure.lean` | $M=1.807100$ 路由闭包：$1.708 + 0.099100 = 1.807100$ |
| `Route181460Closure.lean` | $M=1.814600$ 路由闭包：$1.708 + 0.106600 = 1.814600$，含尾部选择子与扫过引理 |

#### 关键定理

- **`route_closure`**：条件性路由闭包定理
- **`route_arithmetic_certificate`**：路由算术证书束
- **`TailSelector`**：尾部选择子谓词

### 3.6 `1038/` — 早期/实验性工作区

**职责**：Problem 1038 的早期探索、诊断脚本和条件性证书骨架。

| 文件 | 职责 |
|------|------|
| `FormalSkeleton.lean` | 条件性下界的逻辑骨架（Lean 4 + Std，不依赖 Mathlib） |
| `LeanCertificates.lean` | Float 诊断性证书检查器（三原子/五原子候选验证） |
| `solve_two_interval_finite_gap.py` | 双区间有限间隙数值求解器 |
| `search_stronger_finite_atom_block.py` | 更强有限原子块的探索性优化器 |
| `verify_piecewise_tail_correct_domain.py` | required-domain 正性验证器 |
| `two_interval_finite_gap_small_eta/` | 小 ε 双区间有限间隙诊断与验证工具集 |

### 3.7 `remote_364/` — Erdős Problem #364

**职责**：研究"是否存在三个连续 powerful 数"问题。

| 文件 | 职责 |
|------|------|
| `powerful_triples_search.py` | 确定性搜索连续 powerful 数（计算证据，非证明） |
| `openevolve_initial.py` | OpenEvolve 过滤器初始程序（模 36 基线） |
| `openevolve_evaluator.py` | OpenEvolve 评估器 |
| `check_filter_shrink.py` | 检查过滤器是否严格收缩候选残差集 |

### 3.8 `scripts/` — 通用脚本

| 文件 | 职责 |
|------|------|
| `odd_cover_z3.py` | 奇数模覆盖系统 Z3 有界验证器 |

### 3.9 根级 Lean 文件

根目录包含约 70 个 `check_*.lean` 和 `tmp_*.lean` 文件，这些是开发过程中的临时验证和实验文件，主要涉及：

- 对数势函数的各种性质检查（`check_integral_log.lean`、`check_log_div.lean` 等）
- 集合可测性验证（`check_measurableset.lean`）
- 区间积分可积性（`check_intervalIntegrable_*.lean`）
- 标准归约相关引理搜索（`check_sr_*.lean`）
- 尾部检查（`SRtailCheck.lean`、`check_tail.lean`）

---

## 4. 关键类与函数说明

### 4.1 Lean 核心类型与结构

#### `Erdos1038.FiniteAtomFramework.Atom`

```lean
structure Atom where
  x : ℝ    -- 原子位置
  w : ℝ    -- 原子权重（正）
```

有限原子测度的基本构建单元。

#### `Erdos1038.PiecewiseFiveAtom181460Mathlib.RatBox`

```lean
structure RatBox where
  w1 w2 w3 w4 : Rat   -- 四个附加原子权重
  L R : Rat            -- 区间端点
  D0 D1 D2 D3 D4 : Rat -- 到各极点的距离上界
```

有理区间盒证书的数据载体，用于将浮点数值搜索结果转化为可判定的有理验证。

#### `Erdos1038.PiecewiseFiveAtom181460Mathlib.V`

```lean
def V (w1 w2 w3 w4 : ℝ) (y : ℝ) : ℝ :=
    Real.log (|y|)⁻¹
  + w1 * Real.log (|y - d1|)⁻¹
  + w2 * Real.log (|y - d2|)⁻¹
  + w3 * Real.log (|y - d3|)⁻¹
  + w4 * Real.log (|y - d4|)⁻¹
```

五原子对数势函数，核心验证对象。

### 4.2 关键定理

| 定理 | 所在文件 | 含义 |
|------|----------|------|
| `finite_dual_forcing` | `FiniteAtomFramework.lean` | 有限对偶强制：正权重和 + 正集外非正 → 至少一个原子在正集内 |
| `finite_atom_selector_from_duality` | `FiniteAtomFramework.lean` | 对偶恒等式到选择子的桥接 |
| `poleFreeOneVariableLogPositivity_from_boxes` | `FiveAtom1807100BoxCertificate.lean` | 通过有理区间盒证明极点无关一变量正性 |
| `route_closure` | `Route1807100Closure.lean` | $M=1.807100$ 路由闭包 |
| `route_arithmetic_certificate` | `Route1807100Closure.lean` | 路由算术证书 |
| `baselinePunctured_volume` | `StandardReduction.lean` | 去除点不改变 Lebesgue 测度 |
| `standard_minimizer_reduction_baseline_length` | `StandardReduction.lean` | 标准极小化子归约的基线长度结论 |
| `tail_length` | `PiecewiseFiveAtom181460Mathlib.lean` | 尾部长度 $M - B = 0.106600$ |
| `aggregate_certificate` | `Forcing1708Aggregate.lean` | 强制分支聚合证书入口 |

### 4.3 Python 关键函数

| 函数 | 所在文件 | 含义 |
|------|----------|------|
| `V_value(y, weights, shifts)` | `verify_piecewise_tail_correct_domain.py` | 计算五原子对数势在点 y 的值 |
| `search(limit, ...)` | `powerful_triples_search.py` | 搜索连续 powerful 数 |
| `solve_weights(M, T, shifts, ...)` | `search_stronger_finite_atom_block.py` | 线性规划求解原子权重 |
| `integer_cuberoot(n)` | `powerful_triples_search.py` | 整数立方根 |
| `squarefree_sieve(n)` | `powerful_triples_search.py` | 无平方因子筛 |
| `density_bound(moduli)` | `odd_cover_z3.py` | 覆盖密度下界 |

---

## 5. 依赖关系

### 5.1 Lean 依赖图

```
Mathlib (v4.30.0-rc2)
  │
  ├── FiniteAtomFramework.lean
  ├── StandardReduction.lean
  ├── OuterBridges.lean
  │
  ├── Forcing1708Mathlib.lean
  │     └── Forcing1708BoxData.lean
  │     └── Forcing1708AnalyticKernel.lean
  │           └── analytic_precondition_chunks/*.lean
  │     └── Forcing1708CoverageIndex.lean ← coverage_chunks/*.lean
  │     └── Forcing1708GeometryIndex.lean ← geometry_chunks/*.lean
  │     └── Forcing1708Aggregate.lean
  │
  ├── FiveAtom1807100Mathlib.lean
  │     └── FiveAtom1807100BoxCertificate.lean
  ├── FiveAtom1807100Formal.lean
  ├── FiveAtom1807100Route.lean
  │
  ├── PiecewiseFiveAtom181460Mathlib.lean
  │     └── PiecewiseFiveAtom181460BoxCore.lean
  │           └── PiecewiseFiveAtom181460BoxListCore.lean
  │                 └── box_list_chunks/*.lean (×560)
  ├── PiecewiseFiveAtom181460Weights.lean (仅依赖 Std)
  ├── PiecewiseFiveAtom181460Formal.lean
  │
  ├── Route1807100Closure.lean
  └── Route181460Closure.lean ← StandardReduction + PiecewiseFiveAtom181460Formal
```

### 5.2 模块间逻辑依赖

```
                    ┌─────────────────────┐
                    │  StandardReduction   │  (归一化支撑基线区间)
                    └──────────┬──────────┘
                               │
              ┌────────────────┼────────────────┐
              │                │                │
    ┌─────────▼─────────┐    │    ┌─────────────▼──────────────┐
    │  Forcing Branch    │    │    │  Five-Atom Tail Block      │
    │  (M = 1.708)       │    │    │  (M = 1.807100 / 1.814600) │
    └─────────┬─────────┘    │    └─────────────┬──────────────┘
              │                │                │
              │    ┌───────────▼───────────┐    │
              │    │  FiniteAtomFramework   │    │
              │    │  (对偶强制选择子)       │    │
              │    └───────────┬───────────┘    │
              │                │                │
              └────────┬───────┴────────┬───────┘
                       │                │
              ┌────────▼────────┐ ┌─────▼──────────────┐
              │ Route1807100    │ │ Route181460         │
              │ Closure         │ │ Closure             │
              │ (1.807100)      │ │ (1.814600)          │
              └─────────────────┘ └─────────────────────┘
```

### 5.3 Python 依赖

| 包 | 用途 | 所需文件 |
|----|------|----------|
| `numpy` | 数值计算 | `verify_piecewise_tail_correct_domain.py`、`solve_two_interval_finite_gap.py`、`search_stronger_finite_atom_block.py` |
| `scipy` | 数值优化与积分 | `solve_two_interval_finite_gap.py`（`scipy.optimize.root`、`scipy.integrate.quad`）、`search_stronger_finite_atom_block.py`（`scipy.optimize.differential_evolution`、`scipy.optimize.linprog`） |
| `z3-solver` | SMT 求解 | `odd_cover_z3.py` |

### 5.4 Lean 构建依赖

- **Lean 4**：`leanprover/lean4:v4.30.0-rc2`
- **Mathlib**：`leanprover-community/mathlib:v4.30.0-rc2`
- **Std**：通过 Mathlib 传递依赖

各子项目（`forcing_1708`、`five_atom_1807100`）有独立的 `lakefile.toml` 和 `lean-toolchain`，但共享相同的 Mathlib 版本。

---

## 6. 项目运行方式

### 6.1 前置条件

1. **Lean 4 环境**：安装 [elan](https://github.com/leanprover/elan)，Lean 工具链版本 `v4.30.0-rc2`
2. **Mathlib 工作区**：需要一个本地 Mathlib 预编译工作区
3. **Python 3**：用于数值验证脚本
4. **Python 依赖**：`numpy`、`scipy`（可选 `z3-solver`）

### 6.2 全量验证

```bash
# 设置 Mathlib 工作区路径
export MATHLIB_WORKSPACE=/path/to/mathlib

# 运行全量验证（Lean 形式化 + Python 数值验证）
bash finite_atoms/check_all.sh
```

`check_all.sh` 执行以下步骤：

1. 检查 `common/` 下的共享框架（`FiniteAtomFramework.lean`、`StandardReduction.lean`）
2. 检查 `route_1807100/` 路由闭包
3. 编译 `piecewise_five_atom_181460_560/` 的 Mathlib 层、权重层、盒核心层
4. 并行检查 560 个 Lean box-list chunk（默认 8 并发）
5. 检查分段五原子形式化层和路由闭包
6. 检查 `five_atom_1807100/` 的所有 Lean 文件
7. 检查 `forcing_1708/` 的形式化层、解析核、Mathlib 层
8. 运行 `forcing_1708/` 聚合证书检查
9. 运行 Python required-domain 验证

### 6.3 单模块验证

```bash
# 仅验证强制分支聚合证书
LEAN_JOBS=6 MATHLIB_WORKSPACE=/path/to/mathlib \
  bash finite_atoms/forcing_1708/scripts/check_aggregate.sh

# 仅验证分段五原子 Python 证书
bash finite_atoms/piecewise_five_atom_181460_560/scripts/verify_piecewise_181460_560_test.sh

# 跳过 560 chunk 检查（已通过后的快速验证）
SKIP_PIECEWISE_BOX_CHUNKS=1 MATHLIB_WORKSPACE=/path/to/mathlib \
  bash finite_atoms/check_all.sh
```

### 6.4 Python 数值工具

```bash
# Required-domain 正性验证
python3 1038/verify_piecewise_tail_correct_domain.py

# 双区间有限间隙求解
python3 1038/solve_two_interval_finite_gap.py

# 搜索更强有限原子块
python3 1038/search_stronger_finite_atom_block.py

# 连续 powerful 数搜索
python3 remote_364/powerful_triples_search.py --limit 1000000000

# 奇数模覆盖系统验证
pip install -r requirements-odd-cover.txt
python3 scripts/odd_cover_z3.py --moduli 3,5,7,9,11
```

---

## 7. 证明策略与数学框架

### 7.1 有限原子对偶强制路线

整个证明路线遵循以下结构：

1. **标准归约**：通过 Tao/natso 归一化，将问题归约到 $\operatorname{supp}(\mu) \subseteq \{-1\} \cup [0,1]$ 的情形，此时基线区间 $(-\sqrt{2}, 0)$ 被强制进入正集

2. **强制分支**：构造两参数三原子测度族，在对偶域上证明正性，强制长区间 $(-1.708, 0)$ 进入正集，贡献长度 $1.708$

3. **尾部块**：构造五原子测度族 $\lambda_a$，对 $a \in [-M, -1.708]$ 证明正性，扫过五个不相交区间，贡献额外长度 $M - 1.708$

4. **路由闭包**：合并两部分贡献，$1.708 + (M - 1.708) = M$

### 7.2 证书验证方法

- **有理区间盒**：将连续正性问题离散化为有理区间覆盖，每个盒通过精确有理算术验证
- **Taylor/atanh 界**：用截断 Taylor 级数给出 `Real.log` 的有理上下界
- **native_decide**：利用 Lean 的可判定性机制，对有理谓词进行自动化验证
- **Chunk 分片**：将大规模证书（980 盒 / 560 块）拆分为独立文件，支持并行检查

### 7.3 Required-Domain 解释

对于 $M = 1.814600$ 的证书，采用 required-domain 解释：仅需在归一化支撑 $\{-1\} \cup [0,1]$ 上证明正性，而非整个 $[-1, 1]$。在 $y = x - a$ 变量下，这对应两个不相交域：

$$[C-1, A-1] \cup [C, A+1]$$

中间区间 $(A-1, C)$ 对应 $x \in (-1, 0)$，不属于归一化支撑，因此不要求正性。

---

## 8. 验证状态

| 证书包 | 目标 M | 状态 | 最差裕度 |
|--------|--------|------|----------|
| 五原子尾部 | 1.807100 | ✅ Lean/Mathlib 完全验证 | — |
| 分段五原子 560 块 | 1.814600 | ✅ Required-domain 验证 | $9.534 \times 10^{-6}$ |
| 强制分支 | 1.708 | ✅ 980 盒聚合验证 | $2.392 \times 10^{-5}$ |

**注意**：1.814600 证书是条件性 required-domain 证书，不是完整的 $[-1,1]$ 正性证书。560 个对数正性块仍通过生成证书检查，而非展开为 560 个独立 Lean 证明项。

---

## 9. 文件统计

| 类别 | 数量 |
|------|------|
| Lean 形式化文件（核心） | ~30 |
| Lean 生成 chunk 文件 | ~600 |
| Python 验证/搜索脚本 | ~20 |
| Shell 验证脚本 | 4 |
| JSON 证书/数据文件 | ~6 |
| Markdown 文档 | ~8 |
| 根级临时 Lean 文件 | ~70 |

---

## 10. 术语表

| 术语 | 含义 |
|------|------|
| **有限原子 (finite atom)** | 有限支撑的正测度，由离散点质量（Dirac delta）的加权和组成 |
| **对偶强制 (dual forcing)** | 通过构造正的对偶测度，强制原问题中至少一个原子落在目标集合 |
| **选择子 (selector)** | 对偶强制结论：对每个参数，至少一个扫过点落在正集 |
| **扫过 (sweep)** | 参数 $a$ 变化时，原子 $a + d_i$ 扫过的不相交区间 |
| **Required-domain** | 归一化支撑条件下的最小正性域，而非整个 $[-1,1]$ |
| **有理区间盒 (rational interval box)** | 用有理数端点和距离界表示的区间覆盖单元 |
| **路由闭包 (route closure)** | 将强制分支和尾部块的贡献合并的顶层算术定理 |
| **极点无关 (pole-free)** | 在对数势的奇点处不要求有限值，只要求在极点之间正性 |
| **Powerful 数** | 满足：若素数 $p$ 整除 $n$，则 $p^2$ 也整除 $n$ 的正整数 |
