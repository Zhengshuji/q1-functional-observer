
import Q1Paper.PaperI.S03_Certificate.FibreCard

/-!
Q1Paper/PaperI/S03_Certificate/WindowSign.lean

Window-row sign relation for the D1 bridge: an injective-indexed row of the
window matrix is the sign of the two reorderings times the corresponding
subset-indexed row.
-/


open Matrix Polynomial

namespace Q1Paper.PaperI

variable {K : Type*} [Field K]

noncomputable def pairSign {q ℓ ω : ℕ} (x : Inj q ω × Inj ℓ ω) : K :=
  ((Equiv.Perm.sign (permOfImage x.1.1 x.1.2) : ℤˣ) : K) *
    ((Equiv.Perm.sign (permOfImage x.2.1 x.2.2) : ℤˣ) : K)

/-- The sign has square one. -/
theorem pairSign_sq {q ℓ ω : ℕ} (x : Inj q ω × Inj ℓ ω) : pairSign (K := K) x ^ 2 = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign (permOfImage x.1.1 x.1.2)) with h1 | h1 <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign (permOfImage x.2.1 x.2.2)) with h2 | h2 <;>
    simp [pairSign, h1, h2]

/-- **Window-row relation**: an injective-indexed row is the sign times the
corresponding subset-indexed row. -/
theorem windowRow_inj_eq_sign_mul {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ)
    (x : Inj q ω × Inj ℓ ω) (j : Fin ω) (t : Fin (2 * ω)) :
    Q1Paper.windowMatrix (fun x : Inj q ω × Inj ℓ ω => maximalMinor P x.1.1 x.2.1) ω (x, j) t =
      pairSign (K := K) x *
        Q1Paper.windowMatrix (windowMinorFamily P ω) ω (imagePair x, j) t := by
  unfold Q1Paper.windowMatrix windowMinorFamily
  by_cases h : (j : ℕ) ≤ (t : ℕ)
  · rw [if_pos h, if_pos h]
    rw [maximalMinor_injective_coeff_eq_subset (P := P) (ρ := x.1.1) (hρ := x.1.2)
      (κ := x.2.1) (hκ := x.2.2) (a := (t : ℕ) - (j : ℕ))]
    rfl
  · rw [if_neg h, if_neg h]
    simp

end Q1Paper.PaperI




