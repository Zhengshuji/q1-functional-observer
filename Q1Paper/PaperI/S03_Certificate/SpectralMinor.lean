
import Q1Paper.PaperI.S03_Certificate.MinorRank
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
Q1Paper/PaperI/S03_Certificate/SpectralMinor.lean

The pencil-level rank/minors equivalence behind Claim 11:

  `(∀ z, rank (z • H - H_A) = ω)  ↔  ∀ z, some ω × ω minor of the pencil is nonzero`.

Here the pencil is the polynomial matrix `C (H i j) * X - C (H_A i j)`, so that
evaluating at `z` gives `z • H - H_A` (`pencil_map_eval`).  The two ingredients
are

* `exists_det_submatrix_ne_zero_of_rank` (rank `ω` forces a nonzero minor), and
* `rank_le_of_det_maximalMinor_ne_zero` (a nonzero minor forces rank `≥ ω`),

the latter combined with the rank bound `rank (z • H - H_A) ≤ rank H = ω` that
comes from `H_A = F * H` (Claim 2(ii)).
-/


namespace Q1Paper.PaperI

open Matrix Polynomial

variable {K : Type*} [Field K]

/-- The pencil `λ H - H_A` as a polynomial matrix. -/
noncomputable def pencil {q k : ℕ} (H HA : Matrix (Fin q) (Fin k) K) :
    Matrix (Fin q) (Fin k) K[X] :=
  fun i j => Polynomial.C (H i j) * Polynomial.X - Polynomial.C (HA i j)

/-- Evaluating the pencil at `z` gives `z • H - H_A`. -/
theorem pencil_map_eval {q k : ℕ} (H HA : Matrix (Fin q) (Fin k) K) (z : K) :
    (pencil H HA).map (Polynomial.eval z) = z • H - HA := by
  ext i j
  simp only [pencil, Matrix.map_apply, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **Claim 11, the middle equivalence.**  For `H_A = F H` and `rank H = ω`, the
pencil has rank `ω` at every `z` exactly when its maximal minors have no common
root. -/
theorem spectral_iff_minors {q k : ℕ} (H HA : Matrix (Fin q) (Fin k) K) {ω : ℕ}
    (hω : H.rank = ω)
    (hF : ∃ F : Matrix (Fin q) (Fin q) K, HA = F * H) :
    (∀ z : K, (z • H - HA).rank = ω) ↔
      ∀ z : K, ∃ (ρ : Fin ω → Fin q) (κ : Fin ω → Fin k),
        Function.Injective ρ ∧ Function.Injective κ ∧
          (maximalMinor (pencil H HA) ρ κ).eval z ≠ 0 := by
  constructor
  · intro h z
    obtain ⟨ρ, κ, hρ, hκ, hdet⟩ := exists_det_submatrix_ne_zero_of_rank (z • H - HA) (h z)
    exact ⟨ρ, κ, hρ, hκ, by rwa [eval_maximalMinor, pencil_map_eval]⟩
  · intro h z
    obtain ⟨ρ, κ, _, _, hdet⟩ := h z
    rw [eval_maximalMinor, pencil_map_eval] at hdet
    have hlow : ω ≤ (z • H - HA).rank := rank_le_of_det_maximalMinor_ne_zero _ ρ κ hdet
    obtain ⟨F, hF⟩ := hF
    have hle : (z • H - HA).rank ≤ ω := by
      have hz : z • H - HA = (z • 1 - F) * H := by
        rw [hF, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
      rw [hz, ← hω]
      exact Matrix.rank_mul_le_right _ _
    omega

end Q1Paper.PaperI
