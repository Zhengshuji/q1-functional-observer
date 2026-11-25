/-
Q1Paper/PaperII/GraphExtension.lean

Paper II, Proposition `prop:tight`, the `(G, b)` construction: the graph-like subspace

  `W(G, b) = { (h, G h + α b) : h ∈ U, α ∈ K }`

of `E × E`, `E = Fin k → K`, and the structural facts that make it feasible with
quotient dimension `dim U + 1 − dim W₀`:

* `pi1 (W(G,b)) = U`;
* `pi2 (W(G,b)) ≤ U`;
* `dim W(G,b) = dim U + 1` when `b ≠ 0`.

Next step (not yet in this file): the pencil identity
`piLam λ (W(G,b)) = (λI − G)U + span {b}`, hence the paper's rank condition
`rank[λI − G  b] = dim U` gives `dim piLam λ W = dim U` and `W(G,b)` is feasible;
with `W₀ ⊆ W(G,b) ⊆ T` the numerical half (`t_eq_of_finrank`) then gives
`t = a + 1 − s₀`.

Reuses: `Q1Subspace.pi1`, `pi2`, `piLam`, `LinearMap.range_comp`,
`LinearMap.finrank_range_add_finrank_ker`.
-/

import Q1Paper.PaperII.LowerBound

open Module Matrix

namespace Q1Paper.PaperII

variable {K : Type*} [Field K] {k : ℕ}

/-- The linear map `(h, α) ↦ (h, G h + α b)`. -/
noncomputable def graphMap (U : Submodule K (Fin k → K)) (G : U →ₗ[K] U) (b : U) :
    (U × K) →ₗ[K] ((Fin k → K) × (Fin k → K)) where
  toFun p := ((p.1 : Fin k → K), ((G p.1 + p.2 • b : U) : Fin k → K))
  map_add' p q := by
    apply Prod.ext
    · rfl
    · show (((G (p.1 + q.1) + (p.2 + q.2) • b : U)) : Fin k → K)
        = ((G p.1 + p.2 • b : U) : Fin k → K) + ((G q.1 + q.2 • b : U) : Fin k → K)
      simp only [map_add, add_smul, Submodule.coe_add]
      abel
  map_smul' c p := by
    apply Prod.ext
    · rfl
    · show (((G (c • p.1) + (c * p.2) • b : U)) : Fin k → K)
        = c • ((G p.1 + p.2 • b : U) : Fin k → K)
      simp only [map_smul, smul_add, smul_smul, Submodule.coe_add, Submodule.coe_smul, mul_comm]

/-- **The graph-like subspace** `W(G,b) = {(h, G h + α b)}`. -/
noncomputable def graphExt (U : Submodule K (Fin k → K)) (G : U →ₗ[K] U) (b : U) :
    Submodule K ((Fin k → K) × (Fin k → K)) :=
  (graphMap U G b).range

theorem mem_graphExt {U : Submodule K (Fin k → K)} {G : U →ₗ[K] U} {b : U}
    {x y : Fin k → K} :
    (x, y) ∈ graphExt U G b ↔ ∃ (h : U) (α : K), x = (h : Fin k → K) ∧ y = ((G h + α • b : U) : Fin k → K) := by
  rw [graphExt, LinearMap.mem_range]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1, p.2, (congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩
  · rintro ⟨h, α, rfl, rfl⟩
    exact ⟨(h, α), rfl⟩

theorem graphExt_pi1 (U : Submodule K (Fin k → K)) (G : U →ₗ[K] U) (b : U) :
    Q1Subspace.pi1 (graphExt U G b) = U := by
  have hmap : LinearMap.fst K (Fin k → K) (Fin k → K) ∘ₗ graphMap U G b
      = (Submodule.subtype U) ∘ₗ LinearMap.fst K U K := by
    apply LinearMap.ext
    intro p
    rfl
  rw [graphExt, Q1Subspace.pi1, ← LinearMap.range_comp, hmap, LinearMap.range_comp,
    show (LinearMap.fst K U K).range = ⊤ from
      LinearMap.range_eq_top.mpr (fun u => ⟨(u, 0), rfl⟩),
    Submodule.map_top, Submodule.range_subtype]

theorem graphExt_pi2_le (U : Submodule K (Fin k → K)) (G : U →ₗ[K] U) (b : U) :
    Q1Subspace.pi2 (graphExt U G b) ≤ U := by
  intro y hy
  rw [Q1Subspace.mem_pi2] at hy
  obtain ⟨x, hxy⟩ := hy
  rw [mem_graphExt] at hxy
  obtain ⟨h, α, -, rfl⟩ := hxy
  exact Submodule.coe_mem _

theorem graphExt_finrank (U : Submodule K (Fin k → K)) (G : U →ₗ[K] U) (b : U)
    (hb : b ≠ 0) :
    finrank K ↥(graphExt U G b) = finrank K ↥U + 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (graphMap U G b)
  have hker : LinearMap.ker (graphMap U G b) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨h, α⟩ hp
    have h1 : (h : Fin k → K) = 0 := congrArg Prod.fst hp
    have h2 : ((G h + α • b : U) : Fin k → K) = 0 := congrArg Prod.snd hp
    have hh : h = 0 := Subtype.ext h1
    rw [hh, map_zero, zero_add] at h2
    have hsb : α • b = 0 := Subtype.ext h2
    have hα : α = 0 := by
      rcases smul_eq_zero.mp hsb with h | h
      · exact h
      · exact absurd h hb
    exact Prod.ext hh hα
  rw [hker, finrank_bot, add_zero] at hrn
  have hdim : finrank K (U × K) = finrank K ↥U + 1 := by
    rw [Module.finrank_prod, Module.finrank_self]
  rw [hdim] at hrn
  exact hrn

end Q1Paper.PaperII
