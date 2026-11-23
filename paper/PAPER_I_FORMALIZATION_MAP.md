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
| Claim 12 满列秩铅笔证书 | `claim12_iff_gram`, `exists_left_inverse_of_rank_eq` | `PaperI/Claim12.lean` | **complete** | 与 Claim 11 相同：用的是注入映射族的 `Z`；与论文子集族 `Z_Q` 的桥接见 §6 的 D1 |
| Claim 13 有理基与位长 | `bitLenInt`, `bitLenRat`, `bitLenMat`, `mat_num_entries_bounded`；`bitLenRat_add`, `abs_det_le_factorial_mul_pow`, `bitLenInt_det_le`, `bitLenInt_det_num_le_bitLenMat` | `PaperI/BitLen.lean`, `PaperI/BitLenAdd.lean` | **partial（位长基础 + 加法界 + Leibniz 界完成）** | 剩：Bareiss 中间量子式表示、总 bit complexity、输入长度接口 `bitLenMat ≤ L_input` |
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
| `PaperI/Claim12` | `claim12_iff_gram`、`exists_left_inverse_of_rank_eq` | **Claim 12 完整** |
| `PaperI/CauchyBinet` | 方形 Cauchy–Binet（移植，Apache-2.0）：`Matrix.det_mul_eq_sum_det_submatrix` | §III-D 压缩的代数基础 |
| `PaperI/GramKernel` | `selectedCols`、`gramKernelEval`、**`gramKernelEval_eq_double_sum`**、ω>ℓ 边界 | §III-D 第 1–2 层 |

## 3. 公理审计

- `Q1Paper/PaperI/Audit.lean` 对 **233 条**声明执行 `#print axioms`。
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
2. ~~Claim 12~~、~~方形 Cauchy–Binet~~：已完成；下一步是 gramKernel 与系数恒等式（§III-D）；
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

### 4.4 §III-D：方形 Cauchy–Binet（已移植）

`PaperI/CauchyBinet.lean` 给出 §III-D 需要的方形 Cauchy–Binet：

```
Matrix.det_mul_eq_sum_det_submatrix (A : Matrix (Fin m) ι R) (B : Matrix ι (Fin m) R) :
  (A * B).det = ∑ s : Set.powersetCard ι m,
    (A.submatrix id ((s : Finset ι).orderEmbOfFin …)).det *
    (B.submatrix ((s : Finset ι).orderEmbOfFin …) id).det
```

- 来源：Ralf Stephan，
rwst/Subspace-Theorems，ArithmeticHeights/{Plucker,RowSpace,CauchyBinet}.lean，**Apache-2.0**；
  本仓库的移植去掉 `module`/`public`/`[expose]`，只保留所需切片，文件头保留归属与许可证说明。
- 上游 toolchain 为 `v4.35.0-rc3`（与本项目 4.35.0 基本一致），移植只改了变量声明，证明未改。
- 主要声明：exteriorPower.plucker, exteriorPower.plucker_apply,
  Matrix.plucker_row_eq_det_submatrix, exteriorPower.sum_plucker_mul_plucker,
  Matrix.det_mul_eq_sum_plucker, Matrix.det_mul_eq_sum_det_submatrix。

### 4.5 §III-D：gramKernel（第 1–2 层已闭）

PaperI/GramKernel.lean，维数约定与论文一致：P : Matrix (Fin q) (Fin ℓ) K[X]，列子集 J : Set.powersetCard (Fin ℓ) ω，行子集 I : Set.powersetCard (Fin q) ω。

- selectedCols P J：P 的第 J 列（q × ω，orderEmbOfFin 规范枚举）；
- gramKernelEval ω P lam mu = ∑_J det (P(lam)_{:,J}ᵀ P(mu)_{:,J})（ω 显式参数，因为它不出现在 P 的类型里）；
- **gramKernelEval_eq_double_sum**：K(lam,mu) = ∑_I ∑_J f_{I,J}(lam) f_{I,J}(mu)，对每个 J 调用移植的方形 Cauchy–Binet 再交换求和；
- gramKernelEval_eq_zero_of_lt：ω > ℓ 时 K = 0（列子集索引类型为空）。

下一步（§III-D 第 3 层）：系数恒等式 S_{a,b} = ∑_i c_{i,a}c_{i,b} 与 ZᵀZ 的逐项对应。

### 4.6 §III-D：系数恒等式（已闭）

`PaperI/GramCoefficients.lean`：

- `eval_eq_sum_fin_coeff`：`natDegree p ≤ ω` 时 `p.eval x = ∑_{a : Fin (ω+1)} coeff p a · x^a`（固定次数窗口，避免零多项式的 `natDegree` 约定问题）；
- `minorCoeff P ω a I J`：子式 `f_{I,J}` 的 `X^a` 系数；
- `coeffGram P ω a b = ∑_I ∑_J c_{I,J,a} c_{I,J,b}`；
- **`gramKernelEval_eq_coeff_sum`**：在 `deg f_{I,J} ≤ ω` 下，
  `K(lam,mu) = ∑_{a,b : Fin (ω+1)} S_{a,b} lam^a mu^b`（先 `gramKernelEval_eq_double_sum`，再逐项展开系数、两次 `Finset.sum_comm` 换序、`Finset.sum_mul` 提出常数）。

下一步（§III-D 最后一层）：窗口矩阵的逐项 `(ZᵀZ)_{t,t'} = ∑_j S_{t-j,t'-j}`，再用 `Matrix.ext` 得矩阵等式。

### 4.7 §III-D：窗口 Gram 逐项恒等式（已闭）

`PaperI/GramCompression.lean`：

- `windowMinorFamily P ω`：把极大子式族按 `(行子集, 列子集)` 对索引（**注意**：与 Claim 11/12 用的 `minorFamily`（注入映射索引）不是同一个索引族；两者关系见 §6 的 D1 —— 每个子式在注入族里出现 `(ω!)²` 次并带符号，行空间相同，但 `ZᵀZ` 相差正因子 `(ω!)²`；桥接引理尚未形式化）；
- **`windowGram_entry`**：
  `(ZᵀZ)_{t,t'} = ∑_{j : Fin ω} if j ≤ t ∧ j ≤ t' then S_{t-j,t'-j} else 0`，
  其中 `Z = windowMatrix (windowMinorFamily P ω) ω`。

证明分三步（按评审建议拆分）：矩阵乘法展开 `(ZᵀZ)_{t,t'} = ∑_p Z p t · Z p t'`；`Fintype.sum_prod_type` + `Finset.sum_comm` 把 `∑_{p=(i,j)}` 拆成 `∑_j ∑_i`；对 `j ≤ t`、`j ≤ t'` 分支，两项的 `windowMatrix` 截断条件化简为系数，内层 `∑_i c c` 用 `Finset.sum_product'` 回到 `coeffGram`（`Fin` 减法只在条件成立时取，越界项为零，不用 `Fin` 的模减法）。

- `compressedGram P ω`：压缩系数矩阵，`G_comp(t,t') = ∑_j (if j≤t 且 j≤t' 则 S_{t-j,t'-j} 否则 0)`；
- **`windowGram_eq_compressed`**：`ZᵀZ = compressedGram P ω`（`Matrix.ext` + `windowGram_entry`）。

§III-D 的代数链条到此闭环：极大子式族 → 双重展开 → 系数恒等式 → 窗口 Gram 矩阵等式。下一步：端到端核验，然后进 Claim 13。

## 5. 验证记录（可复现）

- Claim 11 完成：commit `e28ee61`（`Paper I: Claim 11 complete`）；
- 修复仓库与 WSL 不同步：commit `7101d1d`（同步 `SpectralMinor.lean` 的注入性版本）；
- CI run `#45026225331` 全绿（lean / Paper I axiom audit / 三篇论文 / verify）；
- 公理审计：233 条声明，允许集 `{propext, Classical.choice, Quot.sound}`；
- 同步检查：`diff` 核对 WSL 工程与仓库的 11 个 Paper I 文件，全部一致。

## 6. 边界

- 本表不含 Paper II–IV 的定理；`MinOrder`、`Strata` 等模块即使被复用，也不计入 Paper I 完成度。
- 复杂度部分依赖 Renegar 界；若不在 Lean 中证明该界，只能称"条件性复杂度形式化"，
  不能称 Paper I 完整形式化。

## 7. 审计发现（子 agent 复核）

一个只读子 agent 逐条核对 §III-D 与论文（未改文件）；确认维数未交换、CB 方向正确、`K` 定义、窗口索引、`2ω` 列数均一致。发现与处置：

**D1（已闭合，commit `2d29702`）**：`windowMinorFamily`（子集索引）与 Claim 11/12 用的 `minorFamily`（注入映射索引）不是同一个族。六步全部完成：`maximalMinor_injective_eq_signed_image`（符号）→ `maximalMinor_injective_coeff_eq`（系数）→ `windowRow_inj_eq_sign_mul`（窗口行）→ `gram_inj_eq_factorial_smul`（Gram `(ω!)²`）→ `gram_certificate_iff_subset`（证书等价）→ `rowSpan_windowInj_eq`（行空间相等）。原始诊断：对每个子集对，注入族里有 `(ω!)²` 个带符号重复，故 `ZᵀZ_Lean = (ω!)² · ZᵀZ_paper`、行空间相同。Claim 11/12 的等价在数学上不受影响（正因子/行空间不变），但“证书矩阵”与论文的 `Z_Q` 字面上不同，且 §III-D 压缩恒等式只对子集族成立。下一步：证桥接引理 `rowSpace (windowMatrix minorFamily) = rowSpace (windowMatrix windowMinorFamily)`（`windowSet` 相同 + 每个注入子式 = ± 对应子集子式）。

**D2**：Claim 12 只形式化了复合形式（`rank ⟺ ∃x, ZᵀZx=e0`）；中间 `e0 ∈ rowZ` 由 `gram_certificate` 可得但未单独声明。可接受。

**D3（部分已修）**：系数恒等式需显式次数界；本轮加 `gramKernelEval_pencil_eq_coeff_sum` 实例化到铅笔（用 `natDegree_maximalMinor_le`）。剩余：§III-D 未端到端组装；`K_P = det(BBᵀ)K_Q` 与共轭/公共根恒等式未形式化。

**D4**：`windowMatrix` 用真实系数（不截断到 `ω`），与论文 `c_{i,a}=0 (a>ω)` 只在 `deg f_i ≤ ω` 下一致；该一致性目前是注释而非引理。需要时补 `windowMatrix_eq_of_natDegree_le`。

**D5**：`[k] → [ℓ]` 零列约化未形式化（Lean 直接从 `q×ℓ` 出发）；记为论文级假设。

**D6**：论文 `rem:algo` (i) 写 `J ⊆ [k]`，与定义 `J ⊆ [ℓ]` 不一致（碰补集的列集行列式为零，故数学等价）；下一轮论文修订改为 `[ℓ]`。

**D7（已修）**：对照表曾有陈旧陈述（Claim 12 标 paper_only、`windowMinorFamily` 标“与 Claim 11 同族”、审计条数 101）；本轮已改。

**D8**：`gramKernelEval_eq_zero_of_lt`（`ℓ < ω`）为 Lean 侧边界引理，论文无对应；无害。

**D10（Bareiss 设计复核，2026-11-23）**：论文 Claim 21 的 Bareiss 中间量界 `Mτ + (M/2)log₂M + 1` 依赖 **Hadamard 不等式**；仓库里只有 **Leibniz 界**（`abs_det_le_factorial_mul_pow`，给出 `nτ + bitLen(n!)`，其中 `bitLen(n!)` 约为 `n log₂ n`）。两者差常数因子 2，**复杂度结论不变**，但论文的显式常数不能从现有形式化推出。处置：附录改写成 `nτ + bitLen(n!)`（可检查的精确对象），注明 Hadamard 可锐化为 `(n/2)log₂n`；若坚持论文形式，须补 Hadamard 引理（Mathlib 无）。

Bareiss 的其余结论（来自同一设计复核）：Bareiss 子式恒等式 = 带边 Desnanot–Jacobi（Sylvester）恒等式，是唯一实质数学缺口；仓库的 Cauchy–Binet 与 Mathlib 的 Schur 补引理都可支撑；无主元情形仅需「所有前主子式非零」；完全主元化只需 `±` 置换符号（已有 `det_submatrix_perm`）；秩亏情形建议只证「每个中间量是 ± 子式」，不形式化可执行的主元搜索。

**D11（Claim 15(iv) 算术骨架复核，2026-11-23）**：附录里极大子式系数的 `22n³L` 是**绑定在 `X` 块的 `18n²L` 上**的；若子式含 `G` 块（界 `20n²L`），同一 Leibniz 论证给出的是 **`24n³L`**（`Claim15iv.minorBound_24_of_twenty`）。对最终 `n²¹L²` 无影响，但论文的显示常数应注明这一点。

**D12（Theorem 5 完备性复核，2026-11-23）**：Lean 的 `PaperI.DEC` 对 `λ : K`（实）量化，而论文的 (5b) 是**复 λ**。两者**严格不等价**：旋转铅笔 `λ²+1` 在实 λ 上无根，但 `rank(i−A)=1`，故 `encodes` 的 S-块（强制每个复 z 满秩）在该例下无实解。因此完备性方向**不能从 `DEC` 推出**，`T5Complete.lean` 用复 λ 假设（论文约定）陈述；从 `DECℂ` 出发只差一条标准复化事实（实 `N` 是复化后 `ker[C_ℂA_ℂ; C_ℂ]` 的复基）。
