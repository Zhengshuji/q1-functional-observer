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
| 定义 (5a)/(5b)、DEC、MINDEC | `Q1Paper.PaperI.rawAlgebraic`, `rawSpectral`, `compressedAlgebraic`, `compressedSpectral`, `DEC`, `MINDEC` | `PaperI/Interface.lean` | **complete（定义层）** | 定义与论文一致；等价性见下一行 |
| Claim 1 秩恒等式 `rank[P;M]=rank P+rank(MN_P)` | `Q1Paper.rank_vstack_add_rank_mul`（矩阵版）、`rank_fromRows_add_map`（任意有限索引类型） | `G4RankIdentity.lean`, `PaperI/CompressionMatrix.lean` | **complete** | — |
| Claim 2 压缩与铅笔判据 | `rawAlgebraic_iff_compressed`, `rawAlgebraic_iff_rowSpace`, `rawSpectral_iff_compressed`, `DEC_iff_compressed`, `exists_factor_of_rawAlgebraic`, `rank_HA_eq_rank_H_of_rawSpectral`；**`DEC_complex_iff_compressed`（实设计 + 复秩）** | `PaperI/CompressionMatrix.lean`, `Compression.lean`, `FixedOrder.lean` | **complete（含域约定）** | 无（见 §4.1 关于 `ℂ` 上秩的说明） |
| Claim 3 可达行对与 `κ_obs=rd_0` | `KappaObs.pairMap`, `finrank_ker_inf_add_finrank_range_pairMap`, `Q1Paper.freePairSpace`, `kappaObs_eq_mul_freePairSpace`, `finrank_domain_le_freePairSpace` | `KappaObs.lean`, `FreeRows.lean` | **partial** | 缺与具体矩阵 `M=[N AN]`、`d_0=rank[N AN]` 的连接，以及 `k≤d_0` |
| Claim 4 沙包与可实现性 | `Q1Subspace.rowSpan_fromRows_left`, `mem_rowSpan_iff_exists_vecMul` | `Q1Subspace.lean` | **partial** | 缺"每个满足 `W_0⊆W⊆T`、`dim(W/W_0)≤r` 的 `W` 由 `t` 行实现"的完整逆向构造（商空间基 + 原像 + 补零） |
| Claim 5 条件只依赖 `W` | `Q1Subspace.pi1`, `pi2`, `Q1Pencil.SpectralCondition`, `hasConstantRank_iff_rankIndependent` | `Q1Projection.lean`, `Q1Pencil.lean`, `Q1Step3.lean` | **partial** | 缺 `π_λ(W)` 的复化、与 `rank(λH−H_A)=ω` 的严格等价 |
| Claim 6 结构界 `ω+1≤dim W≤2ω` | `finrank_le_two_mul_of_pi1_eq_pi2`（上界）、`finrank_add_one_le_of_spectral`（下界） | `Q1Projection.lean`, `BoundLower.lean` | **partial** | 两半都在抽象层；缺 `dim W=ω ⇒ W=graph(F)` 的矩阵化与 `ω>0` 边界 |
| Claim 7 单调性 | `rank_fromRows_zero`, `rowSpan_fromRows_zero`, `conditions_fromRows_zero`, `spectralCondition_append_zero_rows` | `Monotone.lean`, `MonotoneBlocks.lean` | **partial** | 矩阵块层面已有；缺以 `DEC` 为谓词的 `DEC(q)⇒DEC(q+1)` |
| Claim 8 秩一致性 | `exists_mulVec_eq_iff_rank_gram`, `exists_solution_iff_mem_range` | `G5GramRank.lean`, `RankConsistency.lean` | **partial** | 秩形式完整；缺初等对称多项式析取 `∨_t[e_t(Γ)>0 ∧ e_{t+1}(Γ)=0 ∧ e_{t+1}(Γ')=0]` |
| Claim 9 Bézout 次数界 | `exists_bezout_family_real`（实系数，`deg<ω`） | `BezoutReal.lean` | **complete** | — |
| Claim 10 窗口关系 | `windowMatrix`, `rowSpace_windowMatrix_eq_windowSet`, `mem_rowSpace_iff_exists_window`, `toFn_injOn_degree_lt_two_mul` | `Window.lean` | **complete** | 索引/边界已在文件内核对（`j<ω`, `t<2ω`, 零系数约定） |
| Claim 11 Gram 证书 | `claim11_iff_gram`（最终定理：(5b) ⟺ ∃x, ZᵀZx=e₀）；`gram_certificate`（Gram）；`mem_rowSpace_window_iff_no_common_complex_root`（Bézout/窗口）；`spectral_real_iff_minors`, `spectral_iff_minors`（秩-子式/铅笔）；`exists_det_submatrix_ne_zero_of_rank`（秩=最大非零子式）；`rank_map_ofReal`（复化秩不变）；`natDegree_maximalMinor_le`（次数界）；`maximalMinor_map`（系数映射） | `PaperI/Gram.lean`, `PaperI/Claim11.lean`, `PaperI/MinorRank.lean`, `PaperI/BasisExtraction.lean`, `PaperI/SpectralMinor.lean`, `PaperI/Complexify.lean`, `PaperI/Claim11Final.lean` | **complete（含最终 Gram 证书定理）** | 说明：`claim11_iff_gram` 以 `H_A = F H`（Claim 2(ii)）与 `1 ≤ ω`、`rank H = ω` 为假设；这与论文 Claim 11 的假设一致 |
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
| `PaperI/CompressionMatrix` | 矩阵级 Claim 2：`DEC_iff_compressed`、`rawAlgebraic_iff_compressed`、`rawSpectral_iff_compressed`、`rawAlgebraic_iff_rowSpace` | 定义层 + Claim 2(i)(iii) |
| `PaperI/Gram` | Gram 证书：`e₀ ∈ row Z ⟺ ∃x, ZᵀZx = e₀`（任意有限行索引类型） | Claim 11（Gram 边） |
| `PaperI/Claim11` | `windowOne`、Bézout/窗口等价、实系数无公共根 | Claim 11（Bézout/窗口边） |
| `PaperI/MinorRank` | 可求值极大子式、秩 = 最大非零子式（含硬方向） | Claim 11（秩-子式桥） |
| `PaperI/BasisExtraction` | 有限张成族抽基、满行秩 ⟹ 可逆列子矩阵 | Claim 11（支撑） |
| `PaperI/SpectralMinor` | 铅笔 `λH − H_A`、`pencil_map_eval`、`spectral_iff_minors` | Claim 11（中间等价） |
| `PaperI/Complexify` | 复化不改变秩（`rank_map_ofReal`） | Claim 11（域桥） |
| `PaperI/Claim11Final` | **`claim11_iff_gram`**、次数界、实谱等价 | **Claim 11 完整** |

## 3. 公理审计

- `Q1Paper/PaperI/Audit.lean` 对 **89 条**声明执行 `#print axioms`。
- 本机结果：全部为 `[propext, Classical.choice, Quot.sound]`（部分为 `[propext, Quot.sound]`）。
- CI 步骤：`lake env lean Q1Paper/PaperI/Audit.lean > paperI_audit.log` 后运行
  `scripts/check_paperI_axioms.py paperI_audit.log`，出现白名单外的公理或**没有任何审计行**都会失败。
- `sorry`/`admit` 未使用；`PaperI.lean` 的依赖里不含项目自定义公理。

## 4. 下一轮必须补的证明（按依赖顺序）

### 4.1 交付物 3：`DEC ⟺ 压缩条件`（已闭合）

`PaperI/CompressionMatrix.lean` 给出（任意域 `K`，`N` 是 `ker [CA; C]` 的基矩阵）：

- `rank_fromRows_comm`：`rank [A; B] = rank [B; A]`；
- `rank_fromRows_add_map`：秩恒等式在任意有限索引类型上的版本；
- `rank_vstack_add_rank_mul'`、`rank_fromRows_eq_rank_add_mul`：`rank [P; M] = rank P + rank (M N)`；
- `ker_fromRows_eq_map`：`ker [L; P] = N (ker (L N))`；
- `map_ker_eq`：`Submodule.map` 的复合；
- `rawAlgebraic_iff_compressed`：`(5a) ⟺ rank [H_A; H] = rank H`；
- `rawAlgebraic_iff_rowSpace`：`(5a) ⟺ row H_A ⊆ row H`；
- `rawSpectral_iff_compressed`：`(5b) ⟺ ∀λ, rank (λH−H_A) = order H`；
- `DEC_iff_compressed`：`DEC ⟺ ∃ R，压缩块满足两条压缩条件`；
- `exists_factor_of_rawAlgebraic`：Claim 2(ii)，`H_A = F H`；
- `rank_HA_eq_rank_H_of_rawSpectral`：Claim 2(iv)，`rank H_A = rank H`。

证明只用秩恒等式与核-压缩恒等式，**不需要对偶/点积**（原先估计的
`ker = dualAnnihilator(rowSpace)` 被绕开了）。

剩余（都不影响固定域上的 DEC 接口）：

1. ~~Claim 2(ii) 的显式 `F`~~：已由 `exists_factor_of_rowSpace_le` / `exists_factor_of_rawAlgebraic` 给出；
2. ~~Claim 2(iv) `rank H_A = rank H`~~：已由 `rank_eq_of_compressedSpectral`（`λ=0`）与 `rank_neg_eq` 给出；
3. ~~域转移~~：**已按论文的约定解决**。`Interface.DECℂ` 把问题定义为"实设计 `R` + 在 `ℂ` 上算秩"：
   实 `R` 经 `Matrix.map (algebraMap ℝ ℂ)` 进入 `ℂ`，条件在 `ℂ` 上求值；
   `DEC_complex_iff_compressed` 用 `K = ℂ` 的接口定理，因此**不需要**"标量扩张下秩不变"的引理。
   一点说明：`(5a)` 在 `ℂ` 上求值；对实矩阵而言，秩在 `ℝ` 与 `ℂ` 上相同（实子式在 `ℝ` 中非零 ⟺ 在 `ℂ` 中非零），
   论文本身也把秩按 `ℂ` 计算，所以这是论文的约定而不是近似。

### 4.2 之后的顺序

1. ~~Claim 11 的完整 Gram 证书~~：已由 `claim11_iff_gram` 闭合（见 §4.3）；
2. Claim 12（满列秩铅笔）与 Cauchy–Binet 压缩（Mathlib 无矩形 Cauchy–Binet，需自证）；
3. Claim 13–15 的有理位长（清分母 + Hadamard + Bareiss）；
4. Claim 16 五条链 + Proposition 4 算法；
5. Theorems 1、2 的算法与复杂度；Theorem 5 的 `∃ℝ` 编码。

### 4.3 Claim 11：原文步骤 ↔ Lean 定理（已完整）

原文链条 (2) ⟺ `e₀ᵀ ∈ row Z` ⟺ `∃x, ZᵀZx = e₀`，逐句对应：

| 原文步骤 | Lean 定理 |
|---|---|
| `(2)`（复谱条件，`z ∈ ℂ`，`H, H_A` 实） | `spectral_real_iff_minors` |
| 复谱条件 ⟺ 极大子式无公共复根（铅笔层） | `spectral_iff_minors` + `pencil_map_eval` + `maximalMinor_map` + `rank_map_ofReal` |
| 无公共复根 ⟺ 有界 Bézout（Claim 9） | `mem_rowSpace_window_iff_no_common_complex_root`（方向 `⟸` 用 `exists_bezout_family_real`） |
| 有界 Bézout ⟺ `e₀ ∈ row Z`（Claim 10） | `exists_bezout_iff_mem_rowSpace_window` |
| `e₀ ∈ row Z ⟺ ∃x, ZᵀZx = e₀`（Gram） | `gram_certificate`（`row Z = range Zᵀ = range ZᵀZ`，用 `rank_transpose_mul_self`） |
| 次数界 `deg f_{ρ,κ} ≤ ω` | `natDegree_maximalMinor_le` |
| 秩 = 最大非零子式 | `exists_det_submatrix_ne_zero_of_rank`（+ `exists_injective_linearIndependent`, `exists_invertible_cols`） |
| **最终定理** | **`claim11_iff_gram`** |

> **Important distinction.** Claim 11 is formalised using the *full finite family* of
> maximal minors (`minorFamily`, indexed by all pairs of injective row/column maps).
> This establishes the **mathematical** Gram-certificate equivalence.  The subsequent
> Cauchy–Binet-based compression of the Gram kernel (the algorithmic statement that the
> certificate can be computed without enumerating all `C(q,ω)·C(k,ω)` minors) is a
> **separate** result and is **not** implied by this formalisation.

`Claim11Final.lean` 已冻结：后续轮次不再修改其中的核心定理，只在需要时追加新文件。

## 5. 验证记录（可复现）

- Claim 11 完成：commit `e28ee61`（`Paper I: Claim 11 complete`）；
- 修复仓库与 WSL 不同步：commit `7101d1d`（同步 `SpectralMinor.lean` 的注入性版本）；
- CI run `#45026225331` 全绿（lean / Paper I axiom audit / 三篇论文 / verify）；
- 公理审计：89 条声明，允许集 `{propext, Classical.choice, Quot.sound}`；
- 同步检查：`diff` 核对 WSL 工程与仓库的 11 个 Paper I 文件，全部一致。

## 6. 边界

- 本表不含 Paper II–IV 的定理；`MinOrder`、`Strata` 等模块即使被复用，也不计入 Paper I 完成度。
- 复杂度部分依赖 Renegar 界；若不在 Lean 中证明该界，只能称"条件性复杂度形式化"，
  不能称 Paper I 完整形式化。
