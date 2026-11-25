import Mathlib

/-!
# 子空间（商）归约的代数骨架（OPT / FIND 的 FPT 性依赖的那一步）

`M` 是压缩行对矩阵；一行 `u` 经过 `M` 给出压缩行对 `u M`。本文件证明：

* `rowSpan_le_range`、`range_le_rowSpan`：行空间恰是行映射 `u ↦ u M` 的像；
* `mem_rowSpan_iff_exists_vecMul`：**可实现性**——行空间里每个向量都是某个自由行的像；
* `rowSpan_fromRows_left`：**沙包**——给定行的行空间包含在 `[L0; R]` 的行空间里。

这三条合起来就是"自由行块可换成子空间选择"的线性代数内容。
-/

namespace Q1Subspace

open Module

variable {K : Type*} [Field K]
  {n m n0 r : Type*} [Fintype n] [Fintype m] [Fintype n0] [Fintype r]
  [DecidableEq n] [DecidableEq n0]

/-- 行空间：`M` 的各行张成的子空间。 -/
def rowSpan (M : Matrix n m K) : Submodule K (m → K) :=
  Submodule.span K (Set.range (fun i : n => M i))

/-- 每一行都在行映射的像里。 -/
theorem rowSpan_le_range (M : Matrix n m K) :
    rowSpan M ≤ LinearMap.range (Matrix.vecMulLinear M) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨Pi.single i 1, ?_⟩
  funext j
  simp [Matrix.vecMulLinear, Matrix.vecMul]

/-- 行映射的像在行空间里。 -/
theorem range_le_rowSpan (M : Matrix n m K) :
    LinearMap.range (Matrix.vecMulLinear M) ≤ rowSpan M := by
  rintro _ ⟨u, rfl⟩
  have h : Matrix.vecMulLinear M u = ∑ i, u i • M i := by
    ext j
    simp only [Matrix.vecMulLinear, Matrix.vecMul, Finset.sum_apply]
    exact Finset.sum_congr rfl fun x _ => by simp [Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- 行空间等于行映射的像。 -/
theorem range_eq_rowSpan (M : Matrix n m K) :
    LinearMap.range (Matrix.vecMulLinear M) = rowSpan M :=
  le_antisymm (range_le_rowSpan M) (rowSpan_le_range M)

/-- **可实现性**：行空间里的每个向量都是某个自由行的像。 -/
theorem mem_rowSpan_iff_exists_vecMul (M : Matrix n m K) (w : m → K) :
    w ∈ rowSpan M ↔ ∃ u : n → K, Matrix.vecMul u M = w := by
  rw [← range_eq_rowSpan M]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩

/-- **沙包**：`L0` 的行空间包含在 `[L0; R]` 的行空间里。 -/
theorem rowSpan_fromRows_left (L0 : Matrix n0 m K) (R : Matrix r m K) :
    rowSpan L0 ≤ rowSpan (Matrix.fromRows L0 R) := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Sum.inl i, rfl⟩

end Q1Subspace
