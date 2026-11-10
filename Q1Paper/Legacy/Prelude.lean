import Mathlib

/-!
# Prelude：共享维数引理（2026-11-01）

以前每个 Lean 文件各抄一份同样的维数引理（A3sem / QuotientEquivalence / RankBarrier /
D0Boundary / PencilEquivalence / Eigen / A3Bound 共 6–7 份），因为 `check_lean.sh` 逐文件
`lake env lean`、不产生 `.olean`，无法 `import`。

现在改为：本文件先用 `lake build MyProof.Prelude` 生成 `.olean`，其余文件 `import MyProof.Prelude`。

两条引理是项目全部维数记账的基础：

1. `finrank_inter_add_finrank_map_mkQ`：$\dim(T\sqcap B)+\dim(T/B)=\dim T$（A.1 的全部内容）；
2. `finrank_map_add_finrank_inf_ker`：$\dim(TV)+\dim(V\cap\ker T)=\dim V$（限制的秩-零化度，D0/A.2 用）。
-/

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- $\dim(T\sqcap B)+\dim(T/B)=\dim T$（$T/B$ 指 `T` 在 $E/B$ 中的像）。 -/
lemma finrank_inter_add_finrank_map_mkQ (T B : Submodule K E) :
    Module.finrank K ↥(T ⊓ B) + Module.finrank K ↥(Submodule.map (Submodule.mkQ B) T)
      = Module.finrank K ↥T := by
  have h := LinearMap.finrank_range_add_finrank_ker (Submodule.mkQ B ∘ₗ T.subtype)
  have hr : LinearMap.range (Submodule.mkQ B ∘ₗ T.subtype) = Submodule.map (Submodule.mkQ B) T := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(y : E), y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hk : LinearMap.ker (Submodule.mkQ B ∘ₗ T.subtype) = Submodule.comap T.subtype B := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hf : Module.finrank K ↥(Submodule.comap T.subtype B) = Module.finrank K ↥(T ⊓ B) := by
    have e : ↥(Submodule.comap (Submodule.subtype T) B) ≃ₗ[K] ↥(T ⊓ B) :=
      { toFun := fun x => ⟨(x.1 : E), ⟨x.1.2, x.2⟩⟩
        invFun := fun y => ⟨⟨(y : E), y.2.1⟩, y.2.2⟩
        map_add' := by intro x y; ext; rfl
        map_smul' := by intro a x; ext; rfl
        left_inv := by intro x; ext; rfl
        right_inv := by intro y; ext; rfl }
    exact LinearEquiv.finrank_eq e
  rw [hr, hk, hf] at h
  omega

/-- 限制的秩-零化度：$\dim(TV)+\dim(V\cap\ker T)=\dim V$。 -/
lemma finrank_map_add_finrank_inf_ker (T : E →ₗ[K] E) (V : Submodule K E) :
    Module.finrank K ↥(Submodule.map T V) + Module.finrank K ↥(V ⊓ LinearMap.ker T)
      = Module.finrank K ↥V := by
  have h := LinearMap.finrank_range_add_finrank_ker (T.comp V.subtype)
  have hr : LinearMap.range (T.comp V.subtype) = Submodule.map T V := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(y : E), y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hk : LinearMap.ker (T.comp V.subtype) = Submodule.comap V.subtype (LinearMap.ker T) := by
    rw [LinearMap.ker_comp]
  have hf : Module.finrank K ↥(Submodule.comap V.subtype (LinearMap.ker T))
      = Module.finrank K ↥(V ⊓ LinearMap.ker T) := by
    have e : ↥(Submodule.comap V.subtype (LinearMap.ker T)) ≃ₗ[K] ↥(V ⊓ LinearMap.ker T) :=
      { toFun := fun x => ⟨(x.1 : E), ⟨x.1.2, x.2⟩⟩
        invFun := fun y => ⟨⟨(y : E), y.2.1⟩, y.2.2⟩
        map_add' := by intro a b; ext; rfl
        map_smul' := by intro a x; ext; rfl
        left_inv := by intro x; ext; rfl
        right_inv := by intro y; ext; rfl }
    exact LinearEquiv.finrank_eq e
  rw [hr, hk, hf] at h
  omega

/-- 子模非零 ⟹ 维数 $>0$。 -/
lemma finrank_pos_of_ne_bot {p : Submodule K E} (h : p ≠ ⊥) :
    0 < Module.finrank K ↥p := by
  rcases Nat.eq_zero_or_pos (Module.finrank K ↥p) with h0 | h0
  · exact absurd (Submodule.finrank_eq_zero.mp h0) h
  · exact h0
