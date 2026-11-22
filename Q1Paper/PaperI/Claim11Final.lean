/-
Q1Paper/PaperI/Claim11Final.lean

The final assembly of Claim 11:

* `maximalMinor_map`: minors commute with coefficient maps;
* `natDegree_det_le`, `natDegree_maximalMinor_le`: the degree bound
  `deg (maximal minor) <= ω`;
* `spectral_real_iff_minors`: the real pencil condition over the complex
  spectral parameter is equivalent to the real minor family having no common
  complex root;
* `claim11_iff_gram`: `(5b)` is equivalent to solvability of `Zᵀ Z x = e₀`.
-/

import Q1Paper.PaperI.SpectralMinor
import Q1Paper.PaperI.Complexify
import Q1Paper.PaperI.Claim11
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations

namespace Q1Paper.PaperI

open Matrix Polynomial

variable {K : Type*} [Field K]

/-! ### A. Minors commute with coefficient maps -/

theorem maximalMinor_map {m n : Type*} {L : Type*} [Field L] (P : Matrix m n K[X]) {ω : ℕ}
    (ρ : Fin ω → m) (κ : Fin ω → n) (f : K →+* L) :
    maximalMinor (P.map (Polynomial.map f)) ρ κ = (maximalMinor P ρ κ).map f := by
  have hsub : (P.map (Polynomial.map f)).submatrix ρ κ
      = (P.submatrix ρ κ).map (Polynomial.map f) := by
    ext i j
    rfl
  rw [maximalMinor, hsub]
  have h := RingHom.map_det (Polynomial.mapRingHom f) (P.submatrix ρ κ)
  rw [show (Polynomial.mapRingHom f).mapMatrix (P.submatrix ρ κ)
      = (P.submatrix ρ κ).map (Polynomial.map f) from rfl] at h
  exact h.symm

/-! ### C. Degree bound for a determinant -/

theorem natDegree_det_le {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K[X])
    {d : ℕ} (h : ∀ i j, (M i j).natDegree ≤ d) :
    M.det.natDegree ≤ Fintype.card n * d := by
  classical
  rw [Matrix.det_apply']
  refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    (fun σ : Equiv.Perm n => ((Equiv.Perm.sign σ : ℤ) : K[X]) * ∏ i, M (σ i) i)
    (fun σ _ => ?_)
  have hε : (((Equiv.Perm.sign σ : ℤ) : K[X])).natDegree ≤ 0 := by
    simp
  have hprod : (∏ i : n, M (σ i) i).natDegree ≤ Fintype.card n * d := by
    refine le_trans (Polynomial.natDegree_prod_le (s := Finset.univ) (f := fun i => M (σ i) i)) ?_
    have hsum : (∑ i : n, (M (σ i) i).natDegree) ≤ ∑ _i : n, d :=
      Finset.sum_le_sum (fun i _ => h (σ i) i)
    simpa [Finset.sum_const, Finset.card_univ, smul_eq_mul] using hsum
  calc (((Equiv.Perm.sign σ : ℤ) : K[X]) * ∏ i, M (σ i) i).natDegree
      ≤ (((Equiv.Perm.sign σ : ℤ) : K[X])).natDegree
          + (∏ i : n, M (σ i) i).natDegree := Polynomial.natDegree_mul_le
    _ ≤ 0 + Fintype.card n * d := Nat.add_le_add hε hprod
    _ = Fintype.card n * d := Nat.zero_add _

/-- The entries of the pencil have degree at most one. -/
theorem pencil_natDegree_le {q k : ℕ} (H HA : Matrix (Fin q) (Fin k) K) (i : Fin q)
    (j : Fin k) :
    ((pencil H HA) i j).natDegree ≤ 1 := by
  have hsub : (pencil H HA) i j
      = Polynomial.C (H i j) * Polynomial.X - Polynomial.C (HA i j) := rfl
  rw [hsub]
  refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
  rw [max_le_iff]
  constructor
  · refine le_trans (Polynomial.natDegree_mul_le) ?_
    simp
  · simp

/-- The maximal minors of the pencil have degree at most `ω`. -/
theorem natDegree_maximalMinor_le {q k : ℕ} (H HA : Matrix (Fin q) (Fin k) K) {ω : ℕ}
    (ρ : Fin ω → Fin q) (κ : Fin ω → Fin k) :
    (maximalMinor (pencil H HA) ρ κ).natDegree ≤ ω := by
  rw [maximalMinor]
  have h : ∀ i j, ((pencil H HA).submatrix ρ κ i j).natDegree ≤ 1 :=
    fun i j => pencil_natDegree_le H HA (ρ i) (κ j)
  have := natDegree_det_le ((pencil H HA).submatrix ρ κ) h
  simpa using this

/-! ### B. The real pencil condition over the complex spectral parameter -/

theorem spectral_real_iff_minors {q k : ℕ} (H HA : Matrix (Fin q) (Fin k) ℝ) {ω : ℕ}
    (hω : H.rank = ω)
    (hF : ∃ F : Matrix (Fin q) (Fin q) ℝ, HA = F * H) :
    (∀ z : ℂ, (z • H.map (algebraMap ℝ ℂ) - HA.map (algebraMap ℝ ℂ)).rank = ω) ↔
      ∀ z : ℂ, ∃ (ρ : Fin ω → Fin q) (κ : Fin ω → Fin k),
        Function.Injective ρ ∧ Function.Injective κ ∧
          (Q1Paper.complexify (maximalMinor (pencil H HA) ρ κ)).eval z ≠ 0 := by
  have hc := spectral_iff_minors (K := ℂ) (ω := ω)
    (H.map (algebraMap ℝ ℂ)) (HA.map (algebraMap ℝ ℂ))
    (by rw [rank_map_ofReal]; exact hω)
    (by obtain ⟨F, hF⟩ := hF
        exact ⟨F.map (algebraMap ℝ ℂ), by rw [hF, Matrix.map_mul]⟩)
  rw [hc]
  have hminor : ∀ (ρ : Fin ω → Fin q) (κ : Fin ω → Fin k),
      maximalMinor (pencil (H.map (algebraMap ℝ ℂ)) (HA.map (algebraMap ℝ ℂ))) ρ κ
        = Q1Paper.complexify (maximalMinor (pencil H HA) ρ κ) := by
    intro ρ κ
    rw [show pencil (H.map (algebraMap ℝ ℂ)) (HA.map (algebraMap ℝ ℂ))
        = (pencil H HA).map (Polynomial.map (algebraMap ℝ ℂ)) from ?_]
    · exact maximalMinor_map (pencil H HA) ρ κ (algebraMap ℝ ℂ)
    · ext i j
      simp [pencil, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X]
  constructor
  · intro h z
    obtain ⟨ρ, κ, hρ, hκ, hz⟩ := h z
    exact ⟨ρ, κ, hρ, hκ, by rwa [hminor] at hz⟩
  · intro h z
    obtain ⟨ρ, κ, hρ, hκ, hz⟩ := h z
    exact ⟨ρ, κ, hρ, hκ, by rwa [hminor]⟩

/-! ### D/E. The final Claim 11 statement -/

/-- The index type of all ω × ω minors: pairs of injective row/column maps. -/
abbrev minorIndex (q k ω : ℕ) : Type :=
  {ρ : Fin ω → Fin q // Function.Injective ρ} ×
    {κ : Fin ω → Fin k // Function.Injective κ}

/-- The family of all maximal minors of λ H - H_A. -/
noncomputable def minorFamily {q k ω : ℕ} (H HA : Matrix (Fin q) (Fin k) ℝ) :
    minorIndex q k ω → ℝ[X] :=
  fun i => maximalMinor (pencil H HA) i.1.1 i.2.1

/-- **Claim 11, final form.**  The pencil λ H - H_A has rank ω at every complex
z exactly when the Gram system Zᵀ Z x = e₀ is solvable, where Z is the window
matrix of the maximal minors. -/
theorem claim11_iff_gram {q k : ℕ} (H HA : Matrix (Fin q) (Fin k) ℝ) {ω : ℕ}
    (hω : 1 ≤ ω) (hωr : H.rank = ω)
    (hF : ∃ F : Matrix (Fin q) (Fin q) ℝ, HA = F * H) :
    (∀ z : ℂ, (z • H.map (algebraMap ℝ ℂ) - HA.map (algebraMap ℝ ℂ)).rank = ω) ↔
      ∃ x : Fin (2 * ω) → ℝ,
        (Matrix.transpose (windowMatrix (minorFamily (q := q) (k := k) (ω := ω) H HA) ω) *
          windowMatrix (minorFamily (q := q) (k := k) (ω := ω) H HA) ω) *ᵥ x = windowOne (K := ℝ) ω := by
  rw [spectral_real_iff_minors H HA hωr hF]
  have hiff : (∀ z : ℂ, ∃ (ρ : Fin ω → Fin q) (κ : Fin ω → Fin k),
        Function.Injective ρ ∧ Function.Injective κ ∧
          (Q1Paper.complexify (maximalMinor (pencil H HA) ρ κ)).eval z ≠ 0)
      ↔ ∀ z : ℂ, ∃ i : minorIndex q k ω,
          (Q1Paper.complexify (minorFamily (q := q) (k := k) (ω := ω) H HA i)).eval z ≠ 0 := by
    constructor
    · intro h z
      obtain ⟨ρ, κ, hρ, hκ, hz⟩ := h z
      exact ⟨(⟨ρ, hρ⟩, ⟨κ, hκ⟩), hz⟩
    · intro h z
      obtain ⟨⟨⟨ρ, hρ⟩, ⟨κ, hκ⟩⟩, hz⟩ := h z
      exact ⟨ρ, κ, hρ, hκ, hz⟩
  rw [hiff]
  rw [← mem_rowSpace_window_iff_no_common_complex_root (minorFamily (q := q) (k := k) (ω := ω) H HA) hω
      (fun i => natDegree_maximalMinor_le H HA i.1.1 i.2.1)]
  exact gram_certificate (windowMatrix (minorFamily (q := q) (k := k) (ω := ω) H HA) ω) (windowOne (K := ℝ) ω)

end Q1Paper.PaperI

