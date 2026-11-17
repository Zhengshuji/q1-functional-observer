import Q1Paper.Q1Projection

/-!
# The lower half of the structural bound: `ω + 1 ≤ dim W`

Let `K` be a field, `F` a finite-dimensional `K`-vector space and `W ≤ F × F` a subspace whose
second projection is contained in its first (`pi2 W ≤ pi1 W`, the paper's algebraic condition).
Write `ω = finrank K (pi1 W)` and let `piLam λ W` be the image of `W` under the pencil
`(h, g) ↦ λ h - g` (the paper's `λ L - L A`).  Then the spectral condition
`finrank (piLam λ W) = ω` for **every** `λ` forces `ω + 1 ≤ finrank K W`.

This is the step `ω + 1 ≤ dim W` of the paper's structural bound `ω + 1 ≤ dim W ≤ 2 ω`; the paper
uses it for `t_min ≤ 2ℓ` and for `ω ≤ s₀ + t - 1`.  The proof is the "graph + eigenvalue" argument:
`dim W = ω` would make `W` the graph of an endomorphism `G` of `pi1 W`; over an algebraically
closed field (the paper's `ℂ`) `G` has an eigenvalue `λ₀`, and an eigenvector `v` yields the nonzero
kernel element `(v, G v)` of `piLam λ₀`, contradicting the spectral condition.

The sign in `piLam` is the paper's `λ L - L A`, i.e. `(h, g) ↦ λ h - g`.  This is what makes
`piLam 0 W = pi2 W` and makes an eigenvector of the graph map die under `piLam λ₀`.  With the
opposite sign `(h, g) ↦ h - λ g` the claim is **false** (the graph of a nilpotent endomorphism of a
nonzero space satisfies the spectral condition with `dim W = ω`), so the choice is not cosmetic.
-/

namespace Q1Subspace

open Module

variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- The pencil `λ • fst - snd : F × F →ₗ[K] F`, `(h, g) ↦ λ h - g`, applied to a subspace
`W ≤ F × F`.  This is the paper's pencil `λ L - L A`. -/
noncomputable def piLam (lam : K) (W : Submodule K (F × F)) : Submodule K F :=
  W.map (lam • LinearMap.fst K F F - LinearMap.snd K F F)

/-- Membership in the pencil: `x ∈ piLam lam W` iff `x = lam h - g` for some `(h, g) ∈ W`. -/
theorem mem_piLam {lam : K} {W : Submodule K (F × F)} {x : F} :
    x ∈ piLam lam W ↔ ∃ p : F × F, p ∈ W ∧ lam • p.1 - p.2 = x := by
  rw [piLam, Submodule.mem_map]
  exact ⟨fun ⟨p, hp, hpx⟩ => ⟨p, hp, hpx⟩, fun ⟨p, hp, hpx⟩ => ⟨p, hp, hpx⟩⟩

/-- At `lam = 0` the pencil is the second projection.  (This is why the spectral condition at
`lam = 0` is the paper's "`rank [H_A; H] = rank H`" statement: `piLam 0 W = pi2 W`.) -/
theorem piLam_zero (W : Submodule K (F × F)) : piLam 0 W = pi2 W := by
  rw [piLam, pi2, zero_smul, zero_sub]
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    exact ⟨-p, W.neg_mem hp, by simpa using hpx⟩
  · rintro ⟨p, hp, hpx⟩
    exact ⟨-p, W.neg_mem hp, by simpa using hpx⟩

/-- **The `lam = 0` step of the paper.**  The algebraic condition plus the spectral condition at
`lam = 0` already give `pi1 W = pi2 W`. -/
theorem pi1_eq_pi2_of_spectral [FiniteDimensional K F] {W : Submodule K (F × F)}
    (hle : pi2 W ≤ pi1 W)
    (h0 : finrank K ↥(piLam 0 W) = finrank K ↥(pi1 W)) :
    pi1 W = pi2 W := by
  have h : finrank K ↥(pi2 W) = finrank K ↥(pi1 W) := by
    rwa [piLam_zero] at h0
  exact pi1_eq_pi2_of_le_of_finrank_eq hle h

/-- **Lower half of the structural bound.**  Let `W ≤ F × F` satisfy `pi2 W ≤ pi1 W`, let
`ω = finrank K (pi1 W) > 0`, and assume the spectral condition `finrank (piLam lam W) = ω` for
all `lam : K`.  Then `ω + 1 ≤ finrank K W`, i.e. `W` cannot be exactly as small as its first
projection.

Proof: `pi1 W` is a quotient of `W`, so `ω ≤ dim W`.  If `dim W = ω` then the first projection
`W → pi1 W` is bijective and `W` is the graph of an endomorphism `G` of `pi1 W`.  Over an
algebraically closed field `G` has an eigenvalue `lam₀` with eigenvector `v ≠ 0`; then
`(v, G v) ∈ W` is killed by `piLam lam₀`, so `finrank (piLam lam₀ W) < dim W = ω`, contradicting
the spectral condition. -/
theorem finrank_add_one_le_of_spectral [FiniteDimensional K F] [IsAlgClosed K]
    {W : Submodule K (F × F)} (hle : pi2 W ≤ pi1 W)
    (hω : 0 < finrank K ↥(pi1 W))
    (hspec : ∀ lam : K, finrank K ↥(piLam lam W) = finrank K ↥(pi1 W)) :
    finrank K ↥(pi1 W) + 1 ≤ finrank K ↥W := by
  classical
  -- The first projection exhibits `pi1 W` as a quotient of `W`.
  let φ : ↥W →ₗ[K] ↥(pi1 W) :=
    ((LinearMap.fst K F F).comp W.subtype).codRestrict (pi1 W)
      (fun x => mem_pi1.mpr ⟨x.val.2, x.property⟩)
  have hφ_coe : ∀ x : ↥W, (φ x : F) = x.val.1 := fun x => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := mem_pi1.mp hx
    exact ⟨⟨(x, y), hy⟩, Subtype.ext rfl⟩
  have hquot : finrank K ↥(pi1 W) ≤ finrank K ↥W := by
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    have htop : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
    rw [htop, finrank_top] at hrn
    omega
  -- Suppose `dim W = ω`; then the first projection is injective as well.
  by_contra hcon
  push Not at hcon
  have hdim : finrank K ↥W = finrank K ↥(pi1 W) := by omega
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  let e : ↥W ≃ₗ[K] ↥(pi1 W) := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he_apply : ∀ x : ↥W, e x = φ x := fun x => LinearEquiv.ofBijective_apply φ x
  have he_fst : ∀ h : ↥(pi1 W), (e.symm h).val.1 = (h : F) := by
    intro h
    have h1 := congrArg (fun z : ↥(pi1 W) => (z : F)) (LinearEquiv.apply_symm_apply e h)
    rw [he_apply] at h1
    simpa [hφ_coe] using h1
  -- The graph map `G : pi1 W →ₗ pi1 W`: `G h` is the second coordinate of `e.symm h`.
  let σF : ↥(pi1 W) →ₗ[K] F :=
    (LinearMap.snd K F F).comp (W.subtype.comp e.symm.toLinearMap)
  let σ : ↥(pi1 W) →ₗ[K] ↥(pi1 W) :=
    σF.codRestrict (pi1 W) (fun h => by
      have hmem : (e.symm h).val.2 ∈ pi2 W :=
        mem_pi2.mpr ⟨(e.symm h).val.1, (e.symm h).property⟩
      exact hle hmem)
  have hσ_coe : ∀ h : ↥(pi1 W), (σ h : F) = (e.symm h).val.2 := fun h => rfl
  -- An eigenvalue of the graph map.
  have hnt : Nontrivial ↥(pi1 W) := Module.finrank_pos_iff.mp hω
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue σ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv_ne : v ≠ 0 := (Module.End.hasEigenvector_iff.mp hv).2
  have hv_eig : σ v = μ • v := hv.apply_eq_smul
  -- The corresponding element of `W` dies under the `μ`-th pencil.
  let w : ↥W := e.symm v
  have hw_ne : w ≠ 0 := fun hw => hv_ne ((e.symm.map_eq_zero_iff).mp hw)
  have hw_fst : w.val.1 = (v : F) := he_fst v
  have hw_snd : w.val.2 = (μ • v : F) := by
    have h1 := congrArg (fun z : ↥(pi1 W) => (z : F)) hv_eig
    simpa [w, σF, hσ_coe] using h1
  let T : ↥W →ₗ[K] F := (μ • LinearMap.fst K F F - LinearMap.snd K F F).comp W.subtype
  have hTw : T w = 0 := by
    have h1 : T w = μ • w.val.1 - w.val.2 := rfl
    rw [h1, hw_fst, hw_snd]
    simp
  have hrangeT : piLam μ W = LinearMap.range T := by
    ext x
    rw [mem_piLam, LinearMap.mem_range]
    exact ⟨fun ⟨p, hp, hpx⟩ => ⟨⟨p, hp⟩, hpx⟩, fun ⟨⟨p, hp⟩, hpx⟩ => ⟨p, hp, hpx⟩⟩
  have hker : w ∈ LinearMap.ker T := LinearMap.mem_ker.mpr hTw
  have hntker : Nontrivial ↥(LinearMap.ker T) :=
    ⟨⟨⟨w, hker⟩, ⟨0, LinearMap.map_zero T⟩, fun h => hw_ne (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < finrank K ↥(LinearMap.ker T) := Module.finrank_pos_iff.mpr hntker
  -- Rank–nullity contradicts `finrank (piLam μ W) = ω = dim W`.
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  have hrange_dim : finrank K ↥(LinearMap.range T) = finrank K ↥W := by
    rw [← hrangeT, hspec μ, ← hdim]
  omega

end Q1Subspace
