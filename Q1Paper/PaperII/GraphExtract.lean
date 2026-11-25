/-
Q1Paper/PaperII/GraphExtract.lean

Paper II, Proposition `prop:tight`, the converse direction — the setup.

A feasible subspace `W` with `dim W = dim (π₁ W) + 1` projects onto `U = π₁ W` with a
one-dimensional kernel; this file constructs the projection, shows it is onto, and
produces the kernel direction `b ≠ 0` that the graph extension `W(G, b)` needs.

Contents.
* `projW` — the first projection `W → E`.
* `projW_range` — its range is `π₁ W`.
* `projU` — the projection `W → π₁ W` (codomain restricted).
* `projU_surjective` — it is onto.
* `ker_finrank_eq_one` — `dim ker (π₁|_W) = 1` when `dim W = dim (π₁ W) + 1`.
* `exists_kernel_direction` — there is `x ∈ ker`, `x ≠ 0`.
* `exists_kernel_b` — hence `b = x₂ ≠ 0` in `π₁ W` (the paper's direction `b`).

Next step (not in this file): the section `sec` of `projU` and the induced
`G = π₂ ∘ sec`, giving `W = W(G, b)` (`PaperII/GraphExtension.lean` defines that
subspace and its pencil).

Reuses: `Q1Subspace.mem_pi1`, `Q1Subspace.mem_pi2`,
`LinearMap.finrank_range_add_finrank_ker`, `Submodule.exists_mem_ne_zero_of_ne_bot`.
-/

import Q1Paper.PaperII.GraphExtension

open Module Matrix

namespace Q1Paper.PaperII

variable {K : Type*} [Field K] {k : ℕ}

/-- The first projection `W → E`. -/
noncomputable def projW (W : Submodule K ((Fin k → K) × (Fin k → K))) :
    W →ₗ[K] (Fin k → K) :=
  (LinearMap.fst K (Fin k → K) (Fin k → K)).comp W.subtype

theorem projW_range (W : Submodule K ((Fin k → K) × (Fin k → K))) :
    (projW W).range = Q1Subspace.pi1 W := by
  rw [projW, LinearMap.range_comp, Submodule.range_subtype, Q1Subspace.pi1]

/-- The projection `W → π₁ W`. -/
noncomputable def projU (W : Submodule K ((Fin k → K) × (Fin k → K))) :
    W →ₗ[K] ↥(Q1Subspace.pi1 W) :=
  (projW W).codRestrict (Q1Subspace.pi1 W) (fun x => by
    rw [← projW_range]
    exact LinearMap.mem_range_self (projW W) x)

theorem projU_surjective (W : Submodule K ((Fin k → K) × (Fin k → K))) :
    Function.Surjective (projU W) := by
  intro u
  obtain ⟨y, hy⟩ := Q1Subspace.mem_pi1.mp u.2
  refine ⟨⟨(u.1, y), hy⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- **The kernel of the projection is one-dimensional** under
`dim W = dim (π₁ W) + 1`. -/
theorem ker_finrank_eq_one (W : Submodule K ((Fin k → K) × (Fin k → K)))
    (hdim : finrank K ↥W = finrank K ↥(Q1Subspace.pi1 W) + 1) :
    finrank K ↥(LinearMap.ker (projU W)) = 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (projU W)
  have hrange : finrank K ↥(projU W).range = finrank K ↥(Q1Subspace.pi1 W) := by
    have htop : (projU W).range = ⊤ :=
      LinearMap.range_eq_top.mpr (projU_surjective W)
    rw [htop]
    simp
  rw [hrange, hdim] at hrn
  omega

/-- A nonzero element of the kernel exists. -/
theorem exists_kernel_direction (W : Submodule K ((Fin k → K) × (Fin k → K)))
    (hdim : finrank K ↥W = finrank K ↥(Q1Subspace.pi1 W) + 1) :
    ∃ x : W, x ∈ LinearMap.ker (projU W) ∧ x ≠ 0 := by
  have hdim1 : finrank K ↥(LinearMap.ker (projU W)) = 1 := ker_finrank_eq_one W hdim
  have hne : LinearMap.ker (projU W) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim1
    omega
  exact Submodule.exists_mem_ne_zero_of_ne_bot hne

/-- **The paper's direction `b`**: the second component of a nonzero kernel element
lies in `π₁ W` and is nonzero. -/
theorem exists_kernel_b (W : Submodule K ((Fin k → K) × (Fin k → K)))
    (hfeas : IsFeasible W)
    (hdim : finrank K ↥W = finrank K ↥(Q1Subspace.pi1 W) + 1) :
    ∃ b : ↥(Q1Subspace.pi1 W), b ≠ 0 := by
  obtain ⟨x, hxker, hxne⟩ := exists_kernel_direction W hdim
  have hx1 : ((x : W) : (Fin k → K) × (Fin k → K)).1 = 0 := by
    have h0 : projU W x = 0 := LinearMap.mem_ker.mp hxker
    have h1 := congrArg Subtype.val h0
    simpa [projU, projW] using h1
  have hx2 : ((x : W) : (Fin k → K) × (Fin k → K)).2 ≠ 0 := by
    intro h
    apply hxne
    apply Subtype.ext
    exact Prod.ext hx1 h
  refine ⟨⟨((x : W) : (Fin k → K) × (Fin k → K)).2, ?_⟩, ?_⟩
  · exact hfeas.1 (Q1Subspace.mem_pi2.mpr ⟨_, x.2⟩)
  · intro h
    exact hx2 (congrArg Subtype.val h)

end Q1Paper.PaperII
