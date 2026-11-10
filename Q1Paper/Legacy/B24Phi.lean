import Mathlib
import Q1Paper.Legacy.Prelude

/-!
# B.24：偏算子 $\Phi$ 的良定义（商映射泛性质）

B.24 的数学内容：$W=\mathcal LV$ 上的偏算子 $\Phi(xL):=x\Lambda$ 是**良定义**的 ——
若 $xL=0$（且 $x\in V$）则 $x\Lambda=0$。其纯代数内核是商映射的泛性质：

> 设 $\pi:E\to F$、$\sigma:E\to F'$ 线性且 $\ker\pi\le\ker\sigma$，则存在**唯一**线性
> $\Phi:E/\ker\pi\to F'$ 使 $\Phi([x])=\sigma x$。

这正是"$x\mapsto x\Lambda$ 沿 $x\mapsto xL$ 因子化"：良定义性只需 $\ker\pi\le\ker\sigma$，
**不需要** $\pi$ 满射（即不需要 $L$ 行满秩）——这是 B.24 与旧版（要求 $L$ 满行秩）的差别。
-/

variable {K E F F' : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F] [AddCommGroup F'] [Module K F']

/-- **良定义的因子化**：$\ker\pi\le\ker\sigma$ ⟹ $\sigma$ 沿 $\pi$ 因子化（在商上）。 -/
theorem b24_factor (π : E →ₗ[K] F) (σ : E →ₗ[K] F') (h : LinearMap.ker π ≤ LinearMap.ker σ) :
    ∃ Φ : (E ⧸ LinearMap.ker π) →ₗ[K] F', ∀ x : E, Φ (Submodule.Quotient.mk x) = σ x :=
  ⟨Submodule.liftQ _ σ h, fun x => by simp⟩

/-- **唯一性**：这样的 $\Phi$ 唯一。 -/
theorem b24_factor_unique (π : E →ₗ[K] F) (σ : E →ₗ[K] F')
    (Φ Ψ : (E ⧸ LinearMap.ker π) →ₗ[K] F')
    (hΦ : ∀ x : E, Φ (Submodule.Quotient.mk x) = σ x)
    (hΨ : ∀ x : E, Ψ (Submodule.Quotient.mk x) = σ x) : Φ = Ψ := by
  refine LinearMap.ext fun u => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep u
  exact (hΦ x).trans (hΨ x).symm

/-- **不需要行满秩**：$\ker\pi\le\ker\sigma$ 时因子化存在，无论 $\pi$ 是否满射。 -/
theorem b24_no_full_row_rank (π : E →ₗ[K] F) (σ : E →ₗ[K] F')
    (h : LinearMap.ker π ≤ LinearMap.ker σ) :
    ∃ Φ : (E ⧸ LinearMap.ker π) →ₗ[K] F', ∀ x : E, Φ (Submodule.Quotient.mk x) = σ x :=
  b24_factor π σ h
