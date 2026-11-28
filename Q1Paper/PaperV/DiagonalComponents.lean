import Mathlib

/-!
# Q1Paper/PaperV/DiagonalComponents.lean

Lean certificate for assertion **805** of the Q1 project (Paper V, simple-spectrum diagonal case).
This is **not** the full THIN-FEAS theorem; it isolates the linear-algebra core that 805 asserts.

## The assertion being certified

Set `T = 0`, `a = 0` and `Z'' = diag (1, …, k)`, whose eigenvalues `1, …, k` are pairwise distinct.
For a `d'`-dimensional subspace `U` the compatibility condition `U Z'' ⊆ U + T` collapses to
`Z''`-invariance of `U` (because `T = 0`).  The content of 805 is that in this situation the only
invariant `d'`-subspaces are the **coordinate** subspaces spanned by `d'` standard basis vectors;
hence there are exactly `C(k, d')` of them, so **no bound on the number of branches that is
independent of `k, d', t` can exist**.

## What is formalised here

* `diagZ k` — the endomorphism `diag (1, …, k)` of `ℂ^k`, with `diagZ k (stdE i) = (i+1) • stdE i`;
* `invariant_subspace_eq_coordinate` — **the classification theorem**: every `Z`-invariant
  subspace of `ℂ^k` (for any `Z` acting on the standard basis as `e_i ↦ (i+1) • e_i`) is the span
  of the standard basis vectors indexed by some `Finset (Fin k)`;
* `coordSub_invariant`, `coordSub_support`, `coordSub_injective`, `finrank_coordSub` — the
  converse and the structural properties of coordinate subspaces;
* `card_coordinate_indices`, `coordinateEquivInvariant`, `card_invariant_subspaces` — the count
  `C(k, d')` and the explicit finite bijection between `d'`-element index sets and invariant
  `d'`-dimensional subspaces.

## Proof idea

For each `i` use the Lagrange interpolation polynomial
`p_i(X) = ∏_{j ≠ i} (X - (j+1)) / (i - j)`, in the division-free form
`∏_{j ≠ i} (Z - (j+1) • 1)`.  On a vector `w` this operator is coordinatewise multiplication by
`m ↦ ∏_{j ≠ i} (λ_m - λ_j)`, which equals `∏_{j ≠ i} (λ_i - λ_j)` at `m = i` and `0` at `m ≠ i`
(the factor `j = m` vanishes).  Since `Z` preserves `W`, so does this operator, and the scalar
`∏_{j ≠ i} (λ_i - λ_j)` is nonzero because the eigenvalues are pairwise distinct.  Hence
`(w i) • e_i ∈ W` for every `w ∈ W`, and the classification follows by writing
`w = ∑ i, (w i) • e_i`.

No `sorry`, no custom axioms; the only axioms used are Lean's standard `propext`,
`Classical.choice` and `Quot.sound` (checked with `#print axioms` at the end of the file).
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Q1Paper.PaperV

variable {k : ℕ}

/-! ### The diagonal matrix `diag (1, …, k)` and the standard basis -/

/-- The `i`-th eigenvalue of `diag (1, …, k)`, namely `i + 1`. -/
def lam (i : Fin k) : ℂ := (i.val : ℂ) + 1

/-- The `i`-th standard basis vector `e_i` of `ℂ^k`. -/
def stdE (i : Fin k) : Fin k → ℂ := Pi.single i 1

/-- `diag (1, …, k)` as an endomorphism of `ℂ^k`: `v ↦ (i ↦ (i+1) * v i)`. -/
noncomputable def diagZ (k : ℕ) : Module.End ℂ (Fin k → ℂ) where
  toFun v := fun i => lam i * v i
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' c x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem lam_apply (i : Fin k) : lam i = (i.val : ℂ) + 1 := rfl

@[simp] theorem diagZ_apply (v : Fin k → ℂ) (i : Fin k) : diagZ k v i = lam i * v i := rfl

/-- Distinct indices give distinct eigenvalues. -/
theorem lam_injective : Function.Injective (fun i : Fin k => lam i) := by
  intro i j h
  have h1 : (i.val : ℂ) + 1 = (j.val : ℂ) + 1 := h
  have h2 : (i.val : ℂ) = (j.val : ℂ) := add_right_cancel h1
  exact Fin.ext (Nat.cast_injective h2)

/-- `diagZ` acts on the standard basis by the eigenvalue `i + 1`. -/
theorem diagZ_stdE (i : Fin k) : diagZ k (stdE i) = lam i • stdE i := by
  ext m
  by_cases hm : m = i
  · rw [hm]
    simp [stdE]
  · have h0 : stdE i m = 0 := Pi.single_eq_of_ne hm 1
    simp [h0]

/-! ### Coordinatewise scaling and the interpolation operators -/

/-- Coordinatewise scaling by `f : Fin k → ℂ`. -/
noncomputable def scale (k : ℕ) (f : Fin k → ℂ) : Module.End ℂ (Fin k → ℂ) where
  toFun v := fun i => f i * v i
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' c x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem scale_apply (f : Fin k → ℂ) (v : Fin k → ℂ) (i : Fin k) :
    scale k f v i = f i * v i := rfl

theorem scale_mul (f g : Fin k → ℂ) : scale k (f * g) = scale k f * scale k g := by
  ext v i
  simp [scale_apply, Module.End.mul_apply, Pi.mul_apply, mul_assoc]

theorem scale_one (k : ℕ) : scale k (fun _ => 1) = 1 := by
  ext v i
  simp [scale_apply]

theorem diagZ_eq_scale (k : ℕ) : diagZ k = scale k (fun i => lam i) := rfl

/-! ### Invariance under the interpolation factors -/

/-- `Z - c • 1` is coordinatewise scaling by `λ i - c`; it preserves `W` whenever `Z` does. -/
theorem scale_sub_const_mem (W : Submodule ℂ (Fin k → ℂ))
    (hW : ∀ w ∈ W, diagZ k w ∈ W) (c : ℂ) :
    ∀ w ∈ W, scale k (fun i => lam i - c) w ∈ W := by
  intro w hw
  have h : scale k (fun i => lam i - c) w = diagZ k w - c • w := by
    ext i
    simp [scale_apply, diagZ_apply, sub_mul]
  rw [h]
  exact W.sub_mem (hW w hw) (W.smul_mem c hw)

/-- `W` is preserved by any finite product of the factors `Z - (j+1) • 1`. -/
theorem invariant_scale_prod (W : Submodule ℂ (Fin k → ℂ))
    (hW : ∀ w ∈ W, diagZ k w ∈ W) (s : Finset (Fin k)) :
    ∀ w ∈ W, scale k (fun i => ∏ j ∈ s, (lam i - lam j)) w ∈ W := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro w hw
      have hfun : (fun i : Fin k => ∏ j ∈ (∅ : Finset (Fin k)), (lam i - lam j))
          = fun _ => 1 := by
        funext i
        simp
      rw [hfun, scale_one]
      simpa using hw
  | insert a s ha ih =>
      intro w hw
      have hfun : (fun i : Fin k => ∏ j ∈ insert a s, (lam i - lam j))
          = (fun i : Fin k => (lam i - lam a)) *
              (fun i : Fin k => ∏ j ∈ s, (lam i - lam j)) := by
        funext i
        simp [Finset.prod_insert ha, Pi.mul_apply]
      rw [hfun, scale_mul, Module.End.mul_apply]
      exact scale_sub_const_mem W hW (lam a) _ (ih w hw)

/-- **Key coordinate extraction.**  For `w ∈ W` and any index `i`, the vector `(w i) • e_i`
belongs to `W`.  This is the Lagrange interpolation step. -/
theorem smul_stdE_mem (W : Submodule ℂ (Fin k → ℂ))
    (hW : ∀ w ∈ W, diagZ k w ∈ W) {w : Fin k → ℂ} (hw : w ∈ W) (i : Fin k) :
    w i • stdE i ∈ W := by
  classical
  have hmem : scale k (fun m => ∏ j ∈ Finset.univ.erase i, (lam m - lam j)) w ∈ W :=
    invariant_scale_prod W hW (Finset.univ.erase i) w hw
  have hc : (∏ j ∈ Finset.univ.erase i, (lam i - lam j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact sub_ne_zero.mpr (fun h => hji (lam_injective h).symm)
  have hvec : scale k (fun m => ∏ j ∈ Finset.univ.erase i, (lam m - lam j)) w
      = (∏ j ∈ Finset.univ.erase i, (lam i - lam j)) • (w i • stdE i) := by
    ext m
    rw [scale_apply]
    by_cases hm : m = i
    · rw [hm]
      simp [stdE]
    · have hzero : (∏ j ∈ Finset.univ.erase i, (lam m - lam j)) = 0 := by
        apply Finset.prod_eq_zero (f := fun j => lam m - lam j)
          (i := m) (s := Finset.univ.erase i)
        · exact Finset.mem_erase.mpr ⟨hm, Finset.mem_univ m⟩
        · simp
      have h0 : stdE i m = 0 := Pi.single_eq_of_ne hm 1
      rw [hzero]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [h0]
      ring
  rw [hvec] at hmem
  have h2 : (∏ j ∈ Finset.univ.erase i, (lam i - lam j))⁻¹ •
      ((∏ j ∈ Finset.univ.erase i, (lam i - lam j)) • (w i • stdE i)) ∈ W :=
    W.smul_mem _ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

/-! ### The classification theorem -/

/-- Decomposition of a vector in the standard basis: `w = ∑ i, (w i) • e_i`. -/
theorem sum_stdE_smul (w : Fin k → ℂ) : (∑ i : Fin k, w i • stdE i) = w := by
  have h := (Pi.basisFun ℂ (Fin k)).sum_repr w
  simpa [stdE, Pi.basisFun_repr] using h

/-- **Classification of invariant subspaces of `diag (1, …, k)`.**  Every invariant subspace is
spanned by the standard basis vectors indexed by some finite set `S`. -/
theorem diagZ_invariant_subspace_eq_coordinate (W : Submodule ℂ (Fin k → ℂ))
    (hW : ∀ w ∈ W, diagZ k w ∈ W) :
    ∃ S : Finset (Fin k), W = Submodule.span ℂ (S.image (fun i => stdE i)) := by
  classical
  refine ⟨Finset.univ.filter (fun i => ∃ w ∈ W, w i ≠ 0), ?_⟩
  apply le_antisymm
  · -- `W` is contained in the span of the coordinates that occur.
    intro w hw
    have hdecomp : (∑ i : Fin k, w i • stdE i) ∈
        Submodule.span ℂ ((Finset.univ.filter (fun i => ∃ v ∈ W, v i ≠ 0)).image
          (fun i => stdE i)) := by
      refine Submodule.sum_mem _ (fun i _ => ?_)
      by_cases hwi : w i = 0
      · simp [hwi]
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span (Finset.mem_image.mpr
            ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨w, hw, hwi⟩⟩, rfl⟩))
    rwa [sum_stdE_smul] at hdecomp
  · -- The span of those coordinates is contained in `W`.
    rw [Submodule.span_le]
    intro x hx
    simp only [Finset.mem_coe] at hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, hwi⟩ := (Finset.mem_filter.mp hi).2
    have h1 : w i • stdE i ∈ W := smul_stdE_mem W hW hw i
    have h2 : (w i)⁻¹ • (w i • stdE i) ∈ W := W.smul_mem _ h1
    rwa [smul_smul, inv_mul_cancel₀ hwi, one_smul] at h2

/-- **Classification theorem, stated for an arbitrary `Z` acting on the standard basis by the
distinct eigenvalues `1, …, k`.**  This is the form used in assertion 805: `T = 0` makes
compatibility `U Z'' ⊆ U + T` equal to invariance, and then `U` must be a coordinate subspace. -/
theorem invariant_subspace_eq_coordinate (Z : Module.End ℂ (Fin k → ℂ))
    (hZ : ∀ i : Fin k, Z (stdE i) = lam i • stdE i)
    (W : Submodule ℂ (Fin k → ℂ)) (hW : ∀ w ∈ W, Z w ∈ W) :
    ∃ S : Finset (Fin k), W = Submodule.span ℂ (S.image (fun i => stdE i)) := by
  have hZeq : Z = diagZ k := by
    refine (Pi.basisFun ℂ (Fin k)).ext ?_
    intro i
    have h := (hZ i).trans (diagZ_stdE i).symm
    simpa [stdE] using h
  rw [hZeq] at hW
  exact diagZ_invariant_subspace_eq_coordinate W hW

/-! ### Coordinate subspaces: invariance, support, injectivity, dimension -/

/-- The coordinate subspace spanned by `{e_i : i ∈ S}`. -/
noncomputable def coordSub (S : Finset (Fin k)) : Submodule ℂ (Fin k → ℂ) :=
  Submodule.span ℂ (S.image (fun i => stdE i))

/-- Coordinate subspaces are invariant under `diag (1, …, k)`. -/
theorem coordSub_invariant (S : Finset (Fin k)) :
    ∀ w ∈ coordSub S, diagZ k w ∈ coordSub S := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      rw [diagZ_stdE]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih

/-- A vector in a coordinate subspace is supported in the corresponding index set. -/
theorem coordSub_support {S : Finset (Fin k)} {v : Fin k → ℂ}
    (hv : v ∈ coordSub S) {i : Fin k} (hi : i ∉ S) : v i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      exact Pi.single_eq_of_ne hji.symm 1
  | zero => rfl
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul c x hx ih => simp [ih]

/-- Different index sets give different coordinate subspaces. -/
theorem coordSub_injective : Function.Injective (fun S : Finset (Fin k) => coordSub S) := by
  intro S T hST
  change coordSub S = coordSub T at hST
  ext i
  constructor
  · intro hi
    by_contra hTi
    have hmem : stdE i ∈ coordSub T := by
      rw [← hST]
      exact Submodule.subset_span (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have h0 : (stdE i) i = 0 := coordSub_support hmem hTi
    have h1 : (stdE i) i = 1 := by simp [stdE]
    rw [h1] at h0
    exact one_ne_zero h0
  · intro hi
    by_contra hSi
    have hmem : stdE i ∈ coordSub S := by
      rw [hST]
      exact Submodule.subset_span (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have h0 : (stdE i) i = 0 := coordSub_support hmem hSi
    have h1 : (stdE i) i = 1 := by simp [stdE]
    rw [h1] at h0
    exact one_ne_zero h0

/-- The coordinate subspace indexed by `S` has dimension `#S`. -/
theorem finrank_coordSub (S : Finset (Fin k)) :
    Module.finrank ℂ (coordSub S) = S.card := by
  classical
  have hb : LinearIndependent ℂ (fun i : ↥S => stdE (k := k) i) := by
    have h := (Pi.basisFun ℂ (Fin k)).linearIndependent.comp
      (fun i : ↥S => i.val) Subtype.val_injective
    have hfun : (⇑(Pi.basisFun ℂ (Fin k)) ∘ fun i : ↥S => i.val)
        = fun i : ↥S => stdE (k := k) i := by
      funext i
      simp [stdE]
    rwa [hfun] at h
  have h := finrank_span_eq_card hb
  have hspan : coordSub S =
      Submodule.span ℂ (Set.range (fun i : ↥S => stdE (k := k) i)) := by
    simp only [coordSub]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span (Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩)
  rw [hspan]
  simpa [Fintype.card_coe] using h

/-! ### The branch count `C(k, d')` -/

/-- **Classification with the dimension of the index set**: `S.card` equals the dimension of the
invariant subspace.  This is the form needed for the branch count. -/
theorem diagZ_invariant_subspace_eq_coordinate_card (W : Submodule ℂ (Fin k → ℂ))
    (hW : ∀ w ∈ W, diagZ k w ∈ W) :
    ∃ S : Finset (Fin k), S.card = Module.finrank ℂ W ∧
      W = Submodule.span ℂ (S.image (fun i => stdE i)) := by
  obtain ⟨S, hS⟩ := diagZ_invariant_subspace_eq_coordinate W hW
  refine ⟨S, ?_, hS⟩
  have hcongr : Module.finrank ℂ W =
      Module.finrank ℂ (Submodule.span ℂ (S.image (fun i => stdE i))) :=
    congrArg (fun V : Submodule ℂ (Fin k → ℂ) => Module.finrank ℂ V) hS
  rw [hcongr]
  exact (finrank_coordSub S).symm

/-- `W` is an invariant subspace of dimension `d'`. -/
abbrev IsInvariantDim (d' : ℕ) (W : Submodule ℂ (Fin k → ℂ)) : Prop :=
  (∀ w ∈ W, diagZ k w ∈ W) ∧ Module.finrank ℂ W = d'

/-- The number of `d'`-element index sets is the binomial coefficient `C(k, d')`. -/
theorem card_coordinate_indices (d' : ℕ) :
    Fintype.card {S : Finset (Fin k) // S.card = d'} = Nat.choose k d' := by
  classical
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter (fun S : Finset (Fin k) => S.card = d')) =
      (Finset.univ : Finset (Fin k)).powersetCard d' := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **The branch count, as a finite bijection.**  Invariant `d'`-dimensional subspaces of
`ℂ^k` for `diag (1, …, k)` are in bijection with `d'`-element subsets of `{1, …, k}`. -/
noncomputable def coordinateEquivInvariant (d' : ℕ) :
    {S : Finset (Fin k) // S.card = d'} ≃
      {W : Submodule ℂ (Fin k → ℂ) // IsInvariantDim (k := k) d' W} where
  toFun S := ⟨coordSub S.val, coordSub_invariant S.val, by
    show Module.finrank ℂ (coordSub S.val) = d'
    rw [finrank_coordSub, S.property]⟩
  invFun W := ⟨Classical.choose
      (diagZ_invariant_subspace_eq_coordinate_card W.val W.property.1), by
    have h := Classical.choose_spec
      (diagZ_invariant_subspace_eq_coordinate_card W.val W.property.1)
    rw [h.1, W.property.2]⟩
  left_inv S := by
    apply Subtype.ext
    have h := Classical.choose_spec
      (diagZ_invariant_subspace_eq_coordinate_card (coordSub S.val) (coordSub_invariant S.val))
    exact (coordSub_injective h.2).symm
  right_inv W := by
    apply Subtype.ext
    exact (Classical.choose_spec
      (diagZ_invariant_subspace_eq_coordinate_card W.val W.property.1)).2.symm

/-- **The number of invariant `d'`-subspaces is `C(k, d')`** (in the finite-bijection form:
the invariant `d'`-subspaces are in bijection with `d'`-element index sets, which number
`C(k, d')`).  This is the branch-count statement of 805: the count depends on `k` and `d'`
only through the binomial coefficient, so no bound independent of `k, d', t` exists. -/
theorem card_invariant_subspaces (d' : ℕ) :
    Nonempty ({S : Finset (Fin k) // S.card = d'} ≃
        {W : Submodule ℂ (Fin k → ℂ) // IsInvariantDim (k := k) d' W}) ∧
      Fintype.card {S : Finset (Fin k) // S.card = d'} = Nat.choose k d' :=
  ⟨⟨coordinateEquivInvariant d'⟩, card_coordinate_indices d'⟩

end Q1Paper.PaperV

/-! ### Axiom audit -/

#print axioms Q1Paper.PaperV.invariant_subspace_eq_coordinate
#print axioms Q1Paper.PaperV.diagZ_invariant_subspace_eq_coordinate
#print axioms Q1Paper.PaperV.card_invariant_subspaces
