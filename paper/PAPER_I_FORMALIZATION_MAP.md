# Paper I 形式化对照表（2026-11-22）

> 基线：论文 `paper/current/paper_I_dec.tex`（commit `1c19b9f`，18 页）；Lean 仓库 `Q1Paper/`（`main`）。
> 本表只覆盖 **Paper I**；Paper II–IV 的模块（`MinOrder`、`TightDim`、`Strata`、`FullRank`、`Hyperplane*`）
> 不计入本表，也不进入 `PaperI.lean` 的依赖闭包。
> 入口：`PaperI.lean` → `Q1Paper/PaperI/MainTheorems.lean`；审计：`Q1Paper/PaperI/Audit.lean`。

## 0. 状态定义

| 状态 | 含义 |
|---|---|
| **complete** | 有 Lean 声明，假设/结论与论文一致，证明闭合，且公理审计通过（仅 `propext`, `Classical.choice`, `Quot.sound`） |
| **partial** | 已有 Lean 声明，但只覆盖论文陈述的一部分（例如抽象线性映射版、或某个证明步骤），或假设/结论与论文有差距 |
| **paper_only** | 论文有完整陈述与证明，Lean 中尚无对应声明 |

"有文件"不等于"已形式化"。本表按**论文条目**记状态，不按文件记。

## 1. 逐项对照

| 论文条目（PDF 编号） | Lean 声明 | 文件 | 状态 | 差距 |
|---|---|---|---|---|
| 定义 (5a)/(5b)、DEC、MINDEC | `Q1Paper.PaperI.rawAlgebraic`, `rawSpectral`, `compressedAlgebraic`, `compressedSpectral`, `DEC`, `MINDEC` | `PaperI/Interface.lean` | **partial** | 只有定义层；与压缩条件的等价尚未证明 |
| Claim 1 秩恒等式 `rank[P;M]=rank P+rank(MN_P)` | `Q1Paper.rank_vstack_add_rank_mul`（矩阵版）、`rank_fromRows_add_map` | `G4RankIdentity.lean` | **complete** | — |
| Claim 2 压缩与铅笔判据 | `Q1Paper.ker_compressed_iff`（核包含，抽象）、`Q1Paper.G_form_iff`（`H_A=FH`） | `Compression.lean`, `FixedOrder.lean` | **partial** | 缺矩阵级四条等价（行包含、`H_A=FH`、复化铅笔常秩、`rank H_A=rank H`）及与原始 (5a)/(5b) 的桥 |
| Claim 3 可达行对与 `κ_obs=rd_0` | `KappaObs.pairMap`, `finrank_ker_inf_add_finrank_range_pairMap`, `Q1Paper.freePairSpace`, `kappaObs_eq_mul_freePairSpace`, `finrank_domain_le_freePairSpace` | `KappaObs.lean`, `FreeRows.lean` | **partial** | 缺与具体矩阵 `M=[N AN]`、`d_0=rank[N AN]` 的连接，以及 `k≤d_0` |
| Claim 4 沙包与可实现性 | `Q1Subspace.rowSpan_fromRows_left`, `mem_rowSpan_iff_exists_vecMul` | `Q1Subspace.lean` | **partial** | 缺"每个满足 `W_0⊆W⊆T`、`dim(W/W_0)≤r` 的 `W` 由 `t` 行实现"的完整逆向构造（商空间基 + 原像 + 补零） |
| Claim 5 条件只依赖 `W` | `Q1Subspace.pi1`, `pi2`, `Q1Pencil.SpectralCondition`, `hasConstantRank_iff_rankIndependent` | `Q1Projection.lean`, `Q1Pencil.lean`, `Q1Step3.lean` | **partial** | 缺 `π_λ(W)` 的复化、与 `rank(λH−H_A)=ω` 的严格等价 |
| Claim 6 结构界 `ω+1≤dim W≤2ω` | `finrank_le_two_mul_of_pi1_eq_pi2`（上界）、`finrank_add_one_le_of_spectral`（下界） | `Q1Projection.lean`, `BoundLower.lean` | **partial** | 两半都在抽象层；缺 `dim W=ω ⇒ W=graph(F)` 的矩阵化与 `ω>0` 边界 |
| Claim 7 单调性 | `rank_fromRows_zero`, `rowSpan_fromRows_zero`, `conditions_fromRows_zero`, `spectralCondition_append_zero_rows` | `Monotone.lean`, `MonotoneBlocks.lean` | **partial** | 矩阵块层面已有；缺以 `DEC` 为谓词的 `DEC(q)⇒DEC(q+1)` |
| Claim 8 秩一致性 | `exists_mulVec_eq_iff_rank_gram`, `exists_solution_iff_mem_range` | `G5GramRank.lean`, `RankConsistency.lean` | **partial** | 秩形式完整；缺初等对称多项式析取 `∨_t[e_t(Γ)>0 ∧ e_{t+1}(Γ)=0 ∧ e_{t+1}(Γ')=0]` |
| Claim 9 Bézout 次数界 | `exists_bezout_family_real`（实系数，`deg<ω`） | `BezoutReal.lean` | **complete** | — |
| Claim 10 窗口关系 | `windowMatrix`, `rowSpace_windowMatrix_eq_windowSet`, `mem_rowSpace_iff_exists_window`, `toFn_injOn_degree_lt_two_mul` | `Window.lean` | **complete** | 索引/边界已在文件内核对（`j<ω`, `t<2ω`, 零系数约定） |
| Claim 11 Gram 证书 | `sum_sq_eq_zero_iff` | `SpectralCertificate.lean` | **partial（仅 ingredient）** | 缺 `row Z = im Zᵀ`、`ker(ZᵀZ)=ker Z`、`e_0∈row Z ⟺ ∃x, ZᵀZx=e_0` 的完整等价 |
| Claim 12 满列秩铅笔证书 | — | — | **paper_only** | 需 `X` 满列秩时把 Claim 11 用于 `(X,G)` |
| Claim 13 有理基与位长 | — | — | **paper_only** | 需清分母 + Bareiss + Hadamard 的形式化 |
| Claim 14 图表数据 | — | — | **paper_only** | 需 `V=T∩(S×S)` 的核表示（转置写法） |
| Claim 15 系数位长 | — | — | **paper_only** | 需显式常数链（附录 A） |
| Claim 16 零自由行五条件 | `adjRowInverse_mul`, `exists_leftInverse`, `exists_leftInverse_linear`, `spoly_mul_pencil_eq_one`, `natDegree_det_le`, `natDegree_adjugate_le` | `G3Adjugate.lean`, `G3LeftInverse.lean`, `G3Coeff.lean`, `DegreeBounds.lean` | **partial** | 左逆存在与次数界已有；缺 (iii)⇒(iv) 的有理化、(iv)⇒(v) 的系数比较、(v)⇒(i) 的复点代入的完整五条链 |
| Proposition 4（`r=0` 算法） | — | — | **paper_only** | 需把 Claim 16 的五条链组装成算法并证明正确性与位复杂度 |
| Theorem 1（固定阶） | `G_form_iff` 只是代数接口 | `FixedOrder.lean` | **paper_only** | 需算法定义、终止性、soundness/completeness、复杂度 |
| Theorem 2（FPT） | — | `FPT.lean`（仅参数维数代数引理） | **paper_only** | 需图表枚举、覆盖性、变量计数、正确性、参数界 |
| Corollary 3（算术界） | — | — | **paper_only** | 由 Theorem 2 导出 |
| Theorem 5（`∃ℝ`） | — | — | **paper_only** | 需多项式公式语法、`Φ_ω` 构造、双向正确性、规模界 |
| Corollary 6（时间界） | — | — | **paper_only** | 由 Theorem 1/2 导出 |

## 2. 模块清单（Paper I 依赖闭包）

| 模块 | 内容 | 论文条目 |
|---|---|---|
| `Basic` | 对偶映射、核、秩-零化度 | 压缩基础 |
| `RankIdentity`, `G4RankIdentity` | 抽象与矩阵秩恒等式 | Claim 1 |
| `Compression`, `Q1Compression` | 核压缩判据（抽象/矩阵形式） | Claim 2 |
| `Q1RankInclusion`, `Q1RowSpace`, `Q1Subspace` | 行空间、秩-行空间桥、沙包与可实现性 | Claims 2, 4 |
| `KappaObs`, `FreeRows` | 自由行对空间、`κ_obs` | Claim 3 |
| `Q1Projection`, `Q1Pencil`, `Q1Step3`, `BoundLower` | 投影、常秩铅笔、结构界上下半 | Claims 5, 6 |
| `Monotone`, `MonotoneBlocks` | 零行扩充不变性 | Claim 7 |
| `RankConsistency`, `G5GramRank` | 线性系统可解性、Gram 秩判据 | Claim 8 |
| `BezoutDeg`, `BezoutReal` | Bézout 次数界（实系数） | Claim 9 |
| `Window` | 窗口矩阵与行空间 | Claim 10 |
| `SpectralCertificate` | 平方和判据（Gram 的一步） | Claim 11 |
| `G3Adjugate`, `G3LeftInverse`, `G3Coeff`, `DegreeBounds` | 伴随、左逆、系数方程、次数界 | Claim 16 |
| `FixedOrder`, `FPT` | 算法代数接口 | Theorems 1, 2 |
| `PaperI/Interface` | (5a)/(5b)、压缩条件、DEC/MINDEC 的**定义** | 定义层 |

## 3. 公理审计

- `Q1Paper/PaperI/Audit.lean` 对 41 条声明执行 `#print axioms`。
- 本机结果：全部为 `[propext, Classical.choice, Quot.sound]`（部分为 `[propext, Quot.sound]`）。
- CI 新增步骤：`lake env lean Q1Paper/PaperI/Audit.lean > paperI_audit.log` 后运行
  `scripts/check_paperI_axioms.py paperI_audit.log`，出现白名单外的公理或**没有任何审计行**都会失败。
- `sorry`/`admit` 未使用；`PaperI.lean` 的依赖里不含项目自定义公理。

## 4. 下一轮必须补的证明（按依赖顺序）

### 4.1 交付物 3：`DEC ⟺ 压缩条件`

`PaperI/Interface.lean` 只给出定义。要闭合 Claim 2 的矩阵版，还缺四个引理：

1. **`rowSpace_mul`**：`rowSpace (X * N) = (rowSpace X).map (vecMulLinear N)`。
   行空间在右乘 `N` 下的像。
2. **`ker_eq_dualAnnihilator_rowSpace`**：`(rowSpace M)ᗮ = ker M`。
   这是行空间与核的对偶桥（行空间是 `(n→K)` 的对偶里的子空间，需要**求值配对**，
   不能用点积硬套；Mathlib 的 `Submodule.dualAnnihilator` + `Module.Dual.evalEquiv` 是入口）。
3. **`rowSpace_sum`**：`rowSpace [A;B] = rowSpace A ⊔ rowSpace B`（`Q1RowSpace.rowSpace_fromRows` 已有）。
4. **`factor_through`**：若 `range N₁ ≤ range N`，则 `∃ W, N₁ = N * W`（用 `N` 在像上的单射取原像）。

组装后：
- `interface_algebraic`：`rawAlgebraic C CA L LA ↔ compressedAlgebraic (L*N) (LA*N)`，假设 `range N = ker [CA;C]`；
- `interface_spectral`：`rawSpectral ... ↔ compressedSpectral (L*N) (LA*N)`。

另需**域转移**：论文输入在 `ℚ`、设计在 `ℝ`、谱条件在 `ℂ`。Lean 里先在一般域 `K` 证，
再用 `Matrix.rank` 在标量扩张下的不变性把 `ℚ→ℝ→ℂ` 接起来（Mathlib 有 `Matrix.rank_map`
一类的引理需要核对）。

### 4.2 之后的顺序

1. Claim 11 的完整 Gram 证书（`row Z = im Zᵀ`，`ker(ZᵀZ)=ker Z`）；
2. Claim 12（满列秩铅笔）与 Cauchy–Binet 压缩（Mathlib 无矩形 Cauchy–Binet，需自证）；
3. Claim 13–15 的有理位长（清分母 + Hadamard + Bareiss）；
4. Claim 16 五条链 + Proposition 4 算法；
5. Theorems 1、2 的算法与复杂度；Theorem 5 的 `∃ℝ` 编码。

## 5. 边界

- 本表不含 Paper II–IV 的定理；`MinOrder`、`Strata` 等模块即使被复用，也不计入 Paper I 完成度。
- 复杂度部分依赖 Renegar 界；若不在 Lean 中证明该界，只能称"条件性复杂度形式化"，
  不能称 Paper I 完整形式化。
