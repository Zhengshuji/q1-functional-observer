/-
Q1Paper/PaperI/Claim11.lean

Claim 11 of Paper I, the Bézout/window half.  For `f : ι → K[X]` of degree at
most `ω` and `ω ≥ 1`, a degree-bounded Bézout representation of `1` exists if
and only if the constant window `e₀` lies in the row space of the window matrix
`Z` (Claim 10).  Over `ℝ` this is combined with Claim 9
(`exists_bezout_family_real`, whose hypothesis is already "no common complex
root") to obtain the equivalence with the pointwise no-common-root condition.

The remaining step of Claim 11, `(5b) ↔ no common complex root`, is the
rank/minors equivalence and is not part of this file.
-/

import Q1Paper.Window
import Q1Paper.BezoutReal
import Q1Paper.PaperI.Gram

namespace Q1Paper.PaperI

open Polynomial

variable {K : Type*} [Field K]

/-- The coefficient window of the constant polynomial `1`, i.e. the paper's
`e₀ = (1, 0, …, 0)ᵀ` in the length-`2ω` window. -/
noncomputable def windowOne (ω : ℕ) : Fin (2 * ω) → K :=
  fun t => if (t : ℕ) = 0 then 1 else 0

theorem windowOne_eq_toFn (ω : ℕ) :
    windowOne (K := K) ω = Polynomial.toFn (2 * ω) (1 : K[X]) := by
  funext t
  simp [windowOne, Polynomial.coeff_one]

/-- **Claim 11, window step.**  A degree-bounded Bézout representation of `1`
exists exactly when the constant window lies in the row space of `Z`. -/
theorem exists_bezout_iff_mem_rowSpace_window {ι : Type*} [Fintype ι]
    (f : ι → K[X]) {ω : ℕ} (hω : 1 ≤ ω) (hdeg : ∀ i, (f i).natDegree ≤ ω) :
    (∃ g : ι → K[X], (∑ i, g i * f i) = 1 ∧ ∀ i, (g i).natDegree < ω) ↔
      windowOne (K := K) ω ∈ Q1Subspace.rowSpace (windowMatrix f ω) := by
  rw [windowOne_eq_toFn]
  constructor
  · rintro ⟨g, hg1, hgd⟩
    refine (Q1Paper.mem_rowSpace_iff_exists_window f hω _).mpr ⟨g, hgd, ?_⟩
    rw [hg1]
  · intro hmem
    obtain ⟨g, hgd, hv⟩ := (Q1Paper.mem_rowSpace_iff_exists_window f hω _).mp hmem
    refine ⟨g, ?_, hgd⟩
    refine (Q1Paper.toFn_injective_of_natDegree_lt ?_ ?_ hv).symm
    · have h0 : (1 : K[X]).natDegree = 0 := by simp
      omega
    · have hterm : ∀ i, (g i * f i).natDegree ≤ 2 * ω - 1 := by
        intro i
        have hgi : (g i).natDegree ≤ ω - 1 := by
          have := hgd i
          omega
        calc (g i * f i).natDegree
            ≤ (g i).natDegree + (f i).natDegree := Polynomial.natDegree_mul_le
          _ ≤ (ω - 1) + ω := Nat.add_le_add hgi (hdeg i)
          _ = 2 * ω - 1 := by omega
      have hsum : (∑ i, g i * f i).natDegree ≤ 2 * ω - 1 :=
        Polynomial.natDegree_sum_le_of_forall_le Finset.univ (fun i => g i * f i) (fun i _ => hterm i)
      omega

/-- **Claim 11, Bézout side over `ℝ`.**  No common complex root implies that the
constant window lies in the row space (this is Claim 9 plus the window step). -/
theorem mem_rowSpace_window_of_no_common_complex_root {ι : Type*} [Fintype ι]
    (f : ι → ℝ[X]) {ω : ℕ} (hω : 1 ≤ ω) (hdeg : ∀ i, (f i).natDegree ≤ ω)
    (hroot : ∀ z : ℂ, ∃ i, (Q1Paper.complexify (f i)).eval z ≠ 0) :
    windowOne (K := ℝ) ω ∈ Q1Subspace.rowSpace (windowMatrix f ω) :=
  (exists_bezout_iff_mem_rowSpace_window (K := ℝ) f hω hdeg).mp
    (Q1Paper.exists_bezout_family_real hω hdeg hroot)

/-- **Claim 11, Bézout side over `ℝ`, converse.**  If the constant window lies in
the row space, the `f_i` have no common complex root. -/
theorem no_common_complex_root_of_mem_rowSpace_window {ι : Type*} [Fintype ι]
    (f : ι → ℝ[X]) {ω : ℕ} (hω : 1 ≤ ω) (hdeg : ∀ i, (f i).natDegree ≤ ω)
    (hmem : windowOne (K := ℝ) ω ∈ Q1Subspace.rowSpace (windowMatrix f ω)) :
    ∀ z : ℂ, ∃ i, (Q1Paper.complexify (f i)).eval z ≠ 0 := by
  intro z
  obtain ⟨g, hg1, hgd⟩ :=
    (exists_bezout_iff_mem_rowSpace_window (K := ℝ) f hω hdeg).mpr hmem
  by_contra h
  push_neg at h
  have hmap : Q1Paper.complexify (∑ i, g i * f i)
      = ∑ i, Q1Paper.complexify (g i) * Q1Paper.complexify (f i) := by
    change (∑ i, g i * f i).map (algebraMap ℝ ℂ)
      = ∑ i, (g i).map (algebraMap ℝ ℂ) * (f i).map (algebraMap ℝ ℂ)
    rw [Polynomial.map_sum]
    simp [Polynomial.map_mul]
  have hsum : (∑ i, Q1Paper.complexify (g i) * Q1Paper.complexify (f i)) = (1 : ℂ[X]) := by
    rw [← hmap, hg1]
    simp [Q1Paper.complexify]
  have hz : (∑ i, Q1Paper.complexify (g i) * Q1Paper.complexify (f i)).eval z = 0 := by
    rw [Polynomial.eval_finsetSum]
    simp [h]
  rw [hsum] at hz
  simp at hz

/-- **Claim 11, Bézout/window equivalence over `ℝ`.**  The constant window lies
in the row space of `Z` exactly when the `f_i` have no common complex root. -/
theorem mem_rowSpace_window_iff_no_common_complex_root {ι : Type*} [Fintype ι]
    (f : ι → ℝ[X]) {ω : ℕ} (hω : 1 ≤ ω) (hdeg : ∀ i, (f i).natDegree ≤ ω) :
    windowOne (K := ℝ) ω ∈ Q1Subspace.rowSpace (windowMatrix f ω) ↔
      ∀ z : ℂ, ∃ i, (Q1Paper.complexify (f i)).eval z ≠ 0 :=
  ⟨no_common_complex_root_of_mem_rowSpace_window f hω hdeg,
    mem_rowSpace_window_of_no_common_complex_root f hω hdeg⟩

end Q1Paper.PaperI
