
import Q1Paper.PaperI.S03_Certificate.WindowSign

/-!
Q1Paper/PaperI/S03_Certificate/GramFamilyBridge.lean

D1 step 4: the Gram matrix of the injective-indexed window matrix is (ω!)²
times the Gram matrix of the subset-indexed one.

* windowInj, windowSub: the two window matrices;
* sum_prod_snd, sum_snd_prod: reindexing lemmas for the product index;
* gram_entry_inj_eq: the entrywise identity, via the fibre-count lemma
  (card_fibre_pair), the sign relation (windowRow_inj_eq_sign_mul) and
  pairSign_sq;
* gram_inj_eq_factorial_smul: the matrix identity by Matrix.ext.
-/


open Matrix Polynomial

namespace Q1Paper.PaperI

variable {K : Type*} [Field K]

/-- The injective-indexed window matrix of the maximal minors. -/
noncomputable def windowInj {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ) :
    Matrix ((Inj q ω × Inj ℓ ω) × Fin ω) (Fin (2 * ω)) K :=
  Q1Paper.windowMatrix (fun x : Inj q ω × Inj ℓ ω => maximalMinor P x.1.1 x.2.1) ω

/-- The subset-indexed window matrix of the maximal minors. -/
noncomputable def windowSub {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ) :
    Matrix ((Set.powersetCard (Fin q) ω × Set.powersetCard (Fin ℓ) ω) × Fin ω) (Fin (2 * ω)) K :=
  Q1Paper.windowMatrix (windowMinorFamily P ω) ω

/-- Split a sum over the product into a sum over the second coordinate first. -/
theorem sum_prod_snd {ι : Type*} [Fintype ι] {ω : ℕ} (f : ι × Fin ω → K) :
    (∑ p : ι × Fin ω, f p) = ∑ j : Fin ω, ∑ x : ι, f (x, j) := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Merge a sum over the second coordinate first into a sum over the product. -/
theorem sum_snd_prod {ι : Type*} [Fintype ι] {ω : ℕ} (g : ι × Fin ω → K) :
    (∑ j : Fin ω, ∑ x : ι, g (x, j)) = ∑ p : ι × Fin ω, g p := by
  rw [Finset.sum_comm]
  rw [← Fintype.sum_prod_type]

/-- **Entrywise Gram identity** for the injective-indexed window matrix. -/
theorem gram_entry_inj_eq {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ)
    (t t' : Fin (2 * ω)) :
    ((windowInj P ω)ᵀ * windowInj P ω) t t' =
      (ω.factorial * ω.factorial) • (((windowSub P ω)ᵀ * windowSub P ω) t t') := by
  classical
  have hL : ((windowInj P ω)ᵀ * windowInj P ω) t t'
      = ∑ p : (Inj q ω × Inj ℓ ω) × Fin ω, windowInj P ω p t * windowInj P ω p t' := by
    rw [Matrix.mul_apply]
    rfl
  have hR : ((windowSub P ω)ᵀ * windowSub P ω) t t'
      = ∑ p : (Set.powersetCard (Fin q) ω × Set.powersetCard (Fin ℓ) ω) × Fin ω,
          windowSub P ω p t * windowSub P ω p t' := by
    rw [Matrix.mul_apply]
    rfl
  rw [hL, hR]
  rw [sum_prod_snd (K := K) (f := fun p => windowInj P ω p t * windowInj P ω p t')]
  rw [sum_prod_snd (K := K) (f := fun p => windowSub P ω p t * windowSub P ω p t')]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc (∑ x : Inj q ω × Inj ℓ ω, windowInj P ω (x, j) t * windowInj P ω (x, j) t')
      = ∑ x : Inj q ω × Inj ℓ ω,
          (pairSign (K := K) x * windowSub P ω (imagePair x, j) t) *
            (pairSign (K := K) x * windowSub P ω (imagePair x, j) t') := by
        refine Finset.sum_congr rfl fun x _ => ?_
        unfold windowInj windowSub
        rw [windowRow_inj_eq_sign_mul P ω x j t, windowRow_inj_eq_sign_mul P ω x j t']
    _ = ∑ x : Inj q ω × Inj ℓ ω,
          windowSub P ω (imagePair x, j) t * windowSub P ω (imagePair x, j) t' := by
        refine Finset.sum_congr rfl fun x _ => ?_
        calc (pairSign (K := K) x * windowSub P ω (imagePair x, j) t) *
                (pairSign (K := K) x * windowSub P ω (imagePair x, j) t')
            = pairSign (K := K) x ^ 2 *
                (windowSub P ω (imagePair x, j) t * windowSub P ω (imagePair x, j) t') := by ring
          _ = windowSub P ω (imagePair x, j) t * windowSub P ω (imagePair x, j) t' := by
              rw [pairSign_sq (K := K), one_mul]
    _ = (ω.factorial * ω.factorial) •
          ∑ s : (Set.powersetCard (Fin q) ω × Set.powersetCard (Fin ℓ) ω),
            windowSub P ω (s, j) t * windowSub P ω (s, j) t' := by
        exact sum_comp_eq_card_smul_sum (imagePair (q := q) (ℓ := ℓ) (ω := ω))
          (ω.factorial * ω.factorial)
          (fun s => card_fibre_pair (q := q) (ℓ := ℓ) (ω := ω) s.1 s.2)
          (fun s => windowSub P ω (s, j) t * windowSub P ω (s, j) t')

/-- **Matrix form of the Gram scaling**: Z_injᵀZ_inj = (ω!)² • Z_subᵀZ_sub. -/
theorem gram_inj_eq_factorial_smul {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ) :
    (windowInj P ω)ᵀ * windowInj P ω =
      (ω.factorial * ω.factorial) • ((windowSub P ω)ᵀ * windowSub P ω) := by
  ext t t'
  exact gram_entry_inj_eq P ω t t'

end Q1Paper.PaperI

