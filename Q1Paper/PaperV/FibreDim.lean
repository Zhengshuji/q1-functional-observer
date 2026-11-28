import Mathlib

/-!
Q1Paper/PaperV/FibreDim.lean

§II, Theorem 2 — the dimension step: **the space of `q` rows all lying in one and the same
subspace `S` has dimension `q * dim S`**.

In the paper the fibre is a product over the `q` rows of cosets of `T ⊓ U`; its dimension is
`q · a` with `a = dim(U ∩ T)`.  The per-row coset description is `Fibre.lean`
(`fibre_eq_coset`, `fibre_nonempty_iff`); this file supplies the product step, in two
equivalent shapes (`Submodule.pi` over `Set.univ` and the intersection of the coordinate
preimages).

No `sorry`, no axioms beyond Lean's three standard ones.
-/

namespace Q1Paper.PaperV

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

/-- The "every row lies in `S`" space is linearly isomorphic, row by row, to `Fin q → ↥S`. -/
noncomputable def piConstEquiv (S : Submodule K E) (q : ℕ) :
    ↥(Submodule.pi (Set.univ : Set (Fin q)) (fun _ : Fin q => S)) ≃ₗ[K] (Fin q → ↥S) where
  toFun f := fun i => ⟨f.1 i, (Submodule.mem_pi.mp f.2) i (Set.mem_univ i)⟩
  invFun g := ⟨fun i => (g i : E), by
    rw [Submodule.mem_pi]
    intro i _
    exact (g i).2⟩
  map_add' f g := by ext i; rfl
  map_smul' c f := by ext i; rfl
  left_inv f := by ext i; rfl
  right_inv g := by ext i; rfl

/-- Semantic form: a `q`-row matrix lies in the constant fibre space iff each row lies in `S`. -/
theorem mem_pi_const (S : Submodule K E) (q : ℕ) (x : Fin q → E) :
    x ∈ Submodule.pi (Set.univ : Set (Fin q)) (fun _ : Fin q => S) ↔ ∀ i, x i ∈ S := by
  simp [Submodule.mem_pi]

/-- **Theorem 2 (product dimension).** The space of `q` rows all lying in `S` has dimension
`q * dim S`. -/
theorem finrank_pi_const [FiniteDimensional K E] (S : Submodule K E) (q : ℕ) :
    Module.finrank K ↥(Submodule.pi (Set.univ : Set (Fin q)) (fun _ : Fin q => S))
      = q * Module.finrank K ↥S := by
  rw [LinearEquiv.finrank_eq (piConstEquiv S q), Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp

/-- The same statement in the `⨅ comap proj` shape (equivalent by `Submodule.iInf_comap_proj`). -/
theorem finrank_iInf_comap_proj [FiniteDimensional K E] (S : Submodule K E) (q : ℕ) :
    Module.finrank K ↥(⨅ i, Submodule.comap (LinearMap.proj (φ := fun _ : Fin q => E) i) S)
      = q * Module.finrank K ↥S := by
  rw [Submodule.iInf_comap_proj]
  exact finrank_pi_const S q

/-- **Theorem 2 (dimension).** The direction of the fibre is `(T ⊓ U)^q`, whose dimension is
`q` times `dim (T ⊓ U)`: this is the paper's `dim F_U = q a`. -/
theorem fibre_dir_finrank {q : ℕ} (T U : Submodule K E) [FiniteDimensional K E] :
    Module.finrank K ↥(Submodule.pi Set.univ (fun _ : Fin q => T ⊓ U))
      = q * Module.finrank K ↥(T ⊓ U) := by
  simpa using Q1Paper.PaperV.finrank_pi_const (S := T ⊓ U) (q := q)


end Q1Paper.PaperV
