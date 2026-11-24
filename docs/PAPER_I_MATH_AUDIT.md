# Paper I 数学审计（独立复核，2026-11-22）

> **Historical record.** This file documents a stage of the work and is kept for provenance.
> Gaps it describes may have been closed since; do not read it as the current status.
> Current status and the reading entry point: [START_HERE.md](START_HERE.md).


> 只读审计，不改 Lean、不改正文。状态定义：PROVED = 陈述与证明自洽（仅措辞问题）；PAPER-ONLY = 看起来正确但只有论文层面/依赖外部未形式化成分；NEEDS REPAIR = 按现状有缺陷但可局部修复；SUSPECT = 按现状很可能为假。

## 1. 主要发现（按严重度）

### 1.1 Eq. (1) 的“每个可行阶 q ≤ n₀−p”**字面为假**（tex 228–240）

论文同时写了“every feasible order satisfies q ≤ n₀−p”（232–234）与“Claim 7 … every order at or above n₀−p is feasible”（236–237），二者矛盾；Claim 7（495–497）正是反证。

反例 1（精确验证）：`n=2, A=[[0,1],[0,0]], C=[1,0], L₀=[0,1]`。`[C;CA]=I₂`，故 `p=1, k=0, n₀=2, n₀−p=1`；但 `L=[[0,1],[1,0]]`（q=2）满足 (5a)(5b)，且 k=0 时所有 L 都可行。故“q ≤ n₀−p”为假。

**修复**：只保留 `q_min ≤ n₀−p`，删掉“every feasible order …”，并用 Claim 7 的单调性解释“停在 n₀−p”只对最小值成立。

### 1.2 Claim 19（`app:zero`, tex 2050–2056）的 `(HᵀH)⁻¹` 隐含 **ω = k**

`H = L₀N` 是 `r₀×k`，满列秩时 `HᵀH` 可逆只在 `ω = k`。反例 2（精确验证）：`n=4`，`A` 的两条 Jordan 链、`C=[1,0,0,0]`、`L₀=[0,0,1,0]`、`r=0`，得 `k=2, H=(1,0), ω=1 < k`，`HᵀH=diag(1,0)` 奇异。

**修复**：直接解 `FH = H_A`（Cramer 给出子式之比），不用 `HᵀH`；`poly(n,L)` 的结论仍成立，只有显式常数链 `τ₀ = 230n⁴L` 与 Prop 4 的 `n²³L²` 需要重推。

### 1.3 §III-D 的 `K` 用 `J ⊆ [ℓ]`（tex 819–823、836），而 `rem:algo` 写 `J ⊆ [k]`（tex 873）

数学上等价（碰补集的列集行列式为 0），但 FPT 的成本 `C(ℓ,ω) ≤ 2^ℓ`（843–847）与 `ℓ` 参数化都依赖 `[ℓ]`。

**修复**：873 改为 `[ℓ]`；843–847 的“no hidden enumeration”应限定为“每个 C(ℓ,ω) 行列式本身仍需 ω!·poly”，对 `exp(O(ℓ²log ℓ))` 无害。

### 1.4 Theorem 2 的证明步骤 (v)（tex 1205–1208）只引了 Claim 2 与 Claim 10

完整链条应为 `(5b) ⇔ 无公共复根 ⇔ 有界 Bézout（Claim 9）⇔ e₀∈row Z（Claim 10）⇔ ZᵀZx=e₀（Claim 11）`，且需要 §III-D(ii) 的系数恒等式把 `ZᵀZ` 与 `K` 的系数对应起来。

**修复**：补引 Claim 9、11 与 §III-D(ii)。

### 1.5 Algorithm 1（tex 941–961）缺 `q < r₀ ⇒ infeasible` 保护；Theorem 1 的 `q ≥ 1` 范围过宽

反例 3（精确验证）：`n=3, A=[[0,1,0],[0,0,0],[0,0,1]], C=[1,0,0], L₀=[[1,0,0],[0,1,0]]`（`r₀=2`），`q=1` 时算法落入 `h⁰=g⁰=0` 分支返回 FEASIBLE，但 `DEC(1)` 按定义为假。

**修复**：加 `q < r₀` 保护；Theorem 1 限定 `r₀ ≤ q ≤ n`。

## 2. 其余问题

- **Table 5 证据表**（1867–1910）漏了 Claim 7、10、12；Claim 11 只标 "ingredient"；与 §VI（1955）自相矛盾。应从 `PAPER_I_FORMALIZATION_MAP.md` 重新生成。
- **Claim 15(i)**（1424–1500）的“X, G 系数界”只对**指定**分解成立（r=0），对 r ≥ 1 的量化变量不成立；证明里说了（1457–1459），陈述里没说。
- **Claim 22**（2101–2119）行列角色写反（应为 `2k` 行、`d₀+2ℓ ≤ 3n` 列），常数仍成立。
- **Claim 16** 的 (i)–(iii) 引用了 Claim 2(iii) 的 (5a) 假设，但其实无条件成立；应改引无条件论证。
- **Claim 2(iii)** 的 gcd 陈述需 `ω ≥ 1` 或显式 `0×0` 行列式约定。
- **Theorem 1** 应写成“for fixed q, DEC_q ∈ P（L^{O(q²)}）”，并显式 `D = O(qk)`；∃B 消元的拆分需写清。
- **Corollary 3** 是 Theorem 2 的弱推论，无独立内容。

## 3. Lean 对象 vs 论文对象

- **D1**（最重要）：Claim 11/12 的 Z 用**子集**索引（`C(q,ω)·C(k,ω)` 个），Lean 的 `minorFamily` 用**注入映射**索引；每个子式重复 `(ω!)²` 次并带符号，故 `ZᵀZ_Lean = (ω!)² ZᵀZ_paper`、行空间相同。`claim11_iff_gram`/`claim12_iff_gram` 证的是同一个**谓词**，但不是论文的**矩阵**；桥接引理是必需的。
- **D5/D6**：`[k]→[ℓ]` 零列约化是论文级；`rem:algo` 的 `[k]` 与定义的 `[ℓ]` 矛盾。
- **域约定**：Lean 的 `DECℂ`（实设计、ℂ 上算秩）与论文（tex 419–422、125）一致。

## 4. 精确验证（0 mismatch）

- Claim 11 等价性：60 组随机 `H, H_A = FH`（q,k ≤ 4, ω ≤ 4）；
- Claim 12：200 组随机 `(X,G)`，`rank X = ω`；
- Claim 16 (i)⇔(v)：120 组随机 `(X,G)`，最小次数从未超过 `2ω−2`；
- Claim 6：1050 组可行 `(H,H_A)`（q=k=2 全枚举 + 随机），`ω+1 ≤ dim W ≤ 2ω` 无违反。

## 5. 未发现的（负面结果）

- 未发现 Claim 1–12、16 的反例；`(5a) ⟹ dim W = ω` 为假（行空间包含不决定行配对），故 Theorem 2 的 W 范围非空；∃ℝ 编码（Theorem 5）sound & complete，规模 O(n³)、次数 ≤ 2；附录常数链除 Claim 19 外自洽。
- 两个真正条件性的复杂度主张是 Theorem 1 与 Theorem 2（都依赖 Renegar 的 Part II 位界，未形式化）；Theorem 2 是真 FPT，Theorem 1 只是 XP(q)——摘要与 §limits 写对了，定理陈述应改。
