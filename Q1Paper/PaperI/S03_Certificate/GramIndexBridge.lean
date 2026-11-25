
import Q1Paper.PaperI.S03_Certificate.GramFamilyBridge
import Q1Paper.PaperI.S03_Certificate.Claim11_MinorsGram
import Q1Paper.PaperI.S03_Certificate.Claim12

/-!
Q1Paper/PaperI/S03_Certificate/GramIndexBridge.lean

D1 step 7: which index family the maximal minors are indexed by does not change the
certificate.

`WindowSign.windowRow_inj_eq_sign_mul` says every row of the injective-indexed window matrix
is a *signed copy* of a row of the subset-indexed one, the sign being `±1`, and
`FibreCard.card_fibre_pair` says every subset pair has `(ω!)²` preimages, so no subset row is
missed.  Hence the two window matrices have the same row space over any field, and by
`GramSystem.gram_certificate` the two Gram systems are solvable under the same condition.

`Claim11_MinorsGram.claim11_iff_gram` states the certificate for the injective family; this
module restates it for the subset family, which is the family the paper's Cauchy–Binet
argument uses.  `Claim12.claim12_iff_gram` is the same statement for a full-column-rank
pencil, so its subset form follows by the same passage.

* imagePair_surjective — every subset pair is the image of an injective pair;
* rowSpace_windowInj_eq_windowSub — the two window matrices have the same row space;
* claim11_iff_gram_subset, claim12_iff_gram_subset — the certificates for the subsets.
-/


open Matrix Polynomial

namespace Q1Paper.PaperI

variable {K : Type*} [Field K]

/-- Every subset pair is the image of an injective pair: the fibre has `(ω!)²` elements, so
it is nonempty. -/
theorem imagePair_surjective {q ℓ ω : ℕ}
    (s : ↑(Set.powersetCard (Fin q) ω) × ↑(Set.powersetCard (Fin ℓ) ω)) :
    ∃ x : Inj q ω × Inj ℓ ω, imagePair x = s := by
  classical
  have hcard : Fintype.card {x : Inj q ω × Inj ℓ ω // imagePair x = s} =
      ω.factorial * ω.factorial := card_fibre_pair s.1 s.2
  have hpos : 0 < Fintype.card {x : Inj q ω × Inj ℓ ω // imagePair x = s} := by
    rw [hcard]
    exact Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  obtain ⟨⟨x, hx⟩⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨x, hx⟩

/-- The two window matrices have the same row space.

Each injective-indexed row is `±1` times a subset-indexed row, and every subset-indexed row
occurs, because the fibre cardinality is nonzero. -/
theorem rowSpace_windowInj_eq_windowSub {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X])
    (ω : ℕ) :
    Q1Subspace.rowSpace (windowInj P ω) = Q1Subspace.rowSpace (windowSub P ω) := by
  classical
  have hrow : ∀ (x : Inj q ω × Inj ℓ ω) (j : Fin ω),
      windowInj P ω (x, j) = pairSign (K := K) x • windowSub P ω (imagePair x, j) := by
    intro x j
    funext t
    exact windowRow_inj_eq_sign_mul P ω x j t
  apply le_antisymm
  · rw [Q1Subspace.rowSpace, Submodule.span_le]
    rintro _ ⟨⟨x, j⟩, rfl⟩
    change windowInj P ω (x, j) ∈ Q1Subspace.rowSpace (windowSub P ω)
    rw [hrow x j]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(imagePair x, j), rfl⟩)
  · rw [Q1Subspace.rowSpace, Submodule.span_le]
    rintro _ ⟨⟨s, j⟩, rfl⟩
    change windowSub P ω (s, j) ∈ Q1Subspace.rowSpace (windowInj P ω)
    obtain ⟨x, hx⟩ := imagePair_surjective (q := q) (ℓ := ℓ) (ω := ω) s
    rw [← hx]
    have h := hrow x j
    have hinv : windowSub P ω (imagePair x, j) = pairSign (K := K) x • windowInj P ω (x, j) := by
      rw [h, smul_smul, ← pow_two, pairSign_sq, one_smul]
    rw [hinv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(x, j), rfl⟩)

/-- **Claim 11 for the subset-indexed Gram matrix.**

The paper's Cauchy–Binet argument indexes the maximal minors by subsets; the formalisation
indexes them by injective maps.  The two indexings give window matrices with the same row
space, so the Gram certificate is the same statement for both. -/
theorem claim11_iff_gram_subset {q k : ℕ} (H HA : Matrix (Fin q) (Fin k) ℝ) {ω : ℕ}
    (hω : 1 ≤ ω) (hωr : H.rank = ω)
    (hF : ∃ F : Matrix (Fin q) (Fin q) ℝ, HA = F * H) :
    (∀ z : ℂ, (z • H.map (algebraMap ℝ ℂ) - HA.map (algebraMap ℝ ℂ)).rank = ω) ↔
      ∃ x : Fin (2 * ω) → ℝ,
        (Matrix.transpose (windowSub (pencil H HA) ω) *
          windowSub (pencil H HA) ω) *ᵥ x = windowOne (K := ℝ) ω := by
  rw [claim11_iff_gram H HA hω hωr hF]
  have hid : windowMatrix (minorFamily (q := q) (k := k) (ω := ω) H HA) ω =
      windowInj (pencil H HA) ω := rfl
  rw [hid]
  rw [← gram_certificate (windowInj (pencil H HA) ω) (windowOne (K := ℝ) ω),
      ← gram_certificate (windowSub (pencil H HA) ω) (windowOne (K := ℝ) ω),
      rowSpace_windowInj_eq_windowSub]

/-- **Claim 12 for the subset-indexed Gram matrix**, by the same passage. -/
theorem claim12_iff_gram_subset {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℝ)
    (hω : 1 ≤ ω) (hrank : X.rank = ω) :
    (∀ z : ℂ, (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank = ω) ↔
      ∃ x : Fin (2 * ω) → ℝ,
        (Matrix.transpose (windowSub (pencil X G) ω) *
          windowSub (pencil X G) ω) *ᵥ x = windowOne (K := ℝ) ω := by
  obtain ⟨X_L, hXL⟩ := exists_left_inverse_of_rank_eq X hrank
  have hF : ∃ F : Matrix (Fin q) (Fin q) ℝ, G = F * X :=
    ⟨G * X_L, by rw [Matrix.mul_assoc, hXL, Matrix.mul_one]⟩
  exact claim11_iff_gram_subset X G hω hrank hF

end Q1Paper.PaperI
