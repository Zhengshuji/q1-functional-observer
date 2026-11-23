/-
Q1Paper/PaperI/T5Complete.lean

**Theorem 5 of Paper I, completeness direction**: the converse of
`Q1Paper.Thm5.DEC_of_encodes`.  From a feasible compressed pair we construct the
real solution `X G B XL BR S` of the paper's system `encodes`
(`Q1Paper/PaperI/Theorem5.lean`).

Everything here is proved: no `sorry`, no `admit`, no new axioms.

## What is proved

* `exists_encodes_of_blocks` --- the paper's construction at the level of the
  compressed blocks `(H, H_A)`.  If

  - `compressedAlgebraic H H_A`, i.e. `rank [H_A; H] = rank H` (this is (5a)), and
  - `compressedSpectral H_ℂ H_A_ℂ`, i.e. `rank (z • H_ℂ - H_A_ℂ) = rank H_ℂ` for
    every **complex** `z` (this is (5b) in the paper's convention), and
  - the rows of `(H, H_A)` are tied to the input by (B1) (the `r₀` prescribed
    rows) and (B2) (the `r` free rows lie in `row [N  AN]`),

  then there are `ω = rank H` and blocks `X G B XL BR S` with
  `encodes C A L₀ N X G B XL BR S`.

* `exists_encodes_of_compressed` --- the same for
  `H = L N`, `H_A = L A N` with `L = [L₀; R]`, where (B1)/(B2) are discharged
  from the row structure: the witness of (B2) for the row `Sum.inr i` is the row
  `(L) (Sum.inr i)` itself, because `(L N)_i = (L_i) · N` and
  `(L A N)_i = (L_i) · (A N)`.

* `exists_encodes_of_exists_compressed` --- the `∃ R` form, i.e. "if there is a
  feasible `R` for the compressed conditions then the system `Φ_ω` has a real
  solution".

* `exists_compressed_complex_of_encodes` --- the reverse transport: a real
  solution of `encodes` produces an `R` whose compressed pair satisfies (5a) and
  (5b) with the ranks taken at *complex* parameters.

* `exists_encodes_iff` --- the two together: the system `Φ_ω` has a real solution
  iff some feasible `R` satisfies (5a) and the complex-`λ` form of (5b).  So
  `encodes` is exactly the paper's `∃ℝ` formulation of the complex-`λ` reading
  of `DEC(q)`, at the level of the compressed blocks.

Route (the paper's, Section `sec:existsr`):

1. (5a) gives `H_A = F H` (`Q1Subspace.rank_fromRows_eq_rank_iff` +
   `PaperI.exists_factor_of_rowSpace_le`);
2. rank factorisation of `H` gives `X B XL BR` with `X * B = H`, `XL * X = 1`,
   `B * BR = 1` (`PaperI.RankFactorization.exists_rank_factorization_arb`);
3. `G = F * X`, so `G * B = F * H = H_A`;
4. (5b) transported through the right inverse `BR` gives full rank of
   `z • X_ℂ - G_ℂ` at every complex `z`, and `coeff_iff_spectral` produces the
   coefficient matrices `S` (this needs the full rank at every *complex*
   parameter, see below);
5. (B1)/(B2) are `L N = X B` and `L A N = G B` read row by row.

`ω = rank H` and the degenerate case `rank H = 0` is covered as well (`ω = 0`,
all blocks `0`); `exists_coeff_left_inverse_arb` is the `S`-block completeness
for an arbitrary finite row type (reindexing the rows of `coeff_iff_spectral`).

Remark (not stated as a separate lemma below): this witness satisfies the
paper's constraint `ω ≤ min(q,k)`, since `ω = rank H`, `rank H ≤ Fintype.card ι = r₀ + r`
(`Matrix.rank_le_card_height`), and `rank H ≤ k` (`Matrix.rank_le_card_width`).

## The hypothesis is the complex-`λ` condition, and that is necessary

`PaperI.compressedSpectral`, `PaperI.rawSpectral` and `PaperI.DEC` quantify over
`λ : K`, so with `K = ℝ` they are the real-parameter form, which is *strictly
weaker* than the paper's (5b) (`λ ∈ ℂ`).  Concretely, for `n = 2`, `A` the
quarter-turn `!![0, -1; 1, 0]` and `L = 1` one has `det (λ • 1 - A) = λ^2 + 1`,
hence `rank (λ • 1 - A) = 2` for every real `λ`, while `rank (i • 1 - A) = 1`:
the real spectral condition holds and the complex one fails.  But the `S`-block
of `encodes` forces `rank (z • X_ℂ - G_ℂ) = ω` at *every* `z : ℂ`
(`v_implies_i_real`), so for this pencil no real `S` exists.  Therefore the
completeness direction cannot be derived from `PaperI.DEC` (real `λ`) alone: it
needs the paper's complex-`λ` reading of (5b), which is the hypothesis used here.

## What is *not* done here

The only missing link to a statement starting from `PaperI.DECℂ` is the standard
fact that a real basis matrix `N` of `ker [CA; C]` complexifies to a complex
basis matrix of `ker [C_ℂ A_ℂ; C_ℂ]` (a dimension count).  Note that `DECℂ`
itself carries a *complex* `N`, whose rank factorisation is complex and
therefore cannot produce the *real* blocks `X G B XL BR` that `encodes` asks
for; with a real `N` and the complexified spectral condition, the statements
below apply verbatim.
-/

import Q1Paper.PaperI.Theorem5
import Q1Paper.PaperI.RankFactorization
import Q1Paper.PaperI.CompressionMatrix

namespace Q1Paper

open Matrix Polynomial

namespace Thm5

/-! ## 1.  The two rank lemmas over an arbitrary field -/

theorem rank_mul_rightInverse_field {K : Type*} [Field K] {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]
    (P : Matrix m n K) (Q : Matrix n p K) (Q' : Matrix p n K) (h : Q * Q' = 1) :
    (P * Q).rank = P.rank := by
  have hle : (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
  have hge : P.rank ≤ (P * Q).rank := by
    have h1 : P * Q * Q' = P := by rw [Matrix.mul_assoc, h, Matrix.mul_one]
    calc P.rank = (P * Q * Q').rank := by rw [h1]
      _ ≤ (P * Q).rank := Matrix.rank_mul_le_left (P * Q) Q'
  exact le_antisymm hle hge

theorem rank_of_leftInverse_field {K : Type*} [Field K] {ι : Type*} [Fintype ι] {ω : ℕ}
    (X : Matrix ι (Fin ω) K) (XL : Matrix (Fin ω) ι K) (h : XL * X = 1) :
    X.rank = ω := by
  have h1 : ω ≤ X.rank := by
    have h2 : (1 : Matrix (Fin ω) (Fin ω) K).rank ≤ X.rank := by
      rw [← h]
      exact Matrix.rank_mul_le_right XL X
    rwa [Matrix.rank_one, Fintype.card_fin] at h2
  have h3 : X.rank ≤ ω := by
    simpa using Matrix.rank_le_card_width X
  omega

/-! ## 2.  A real matrix of rank zero is zero -/

theorem eq_zero_of_rank_eq_zero {m n : Type*} [Fintype m] [Fintype n] [Finite m]
    (M : Matrix m n ℝ) (h : M.rank = 0) : M = 0 := by
  have hbot : Submodule.span ℝ (Set.range M.row) = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    rw [← Matrix.rank_eq_finrank_span_row]
    exact h
  ext i j
  have hmem : M.row i ∈ Submodule.span ℝ (Set.range M.row) := Submodule.subset_span ⟨i, rfl⟩
  rw [hbot] at hmem
  have hrow : M.row i = 0 := by simpa using hmem
  have h2 := congrFun hrow j
  simpa using h2

/-! ## 3.  Completeness of the coefficient system for an arbitrary row type -/

theorem exists_coeff_left_inverse_arb {ι : Type*} [Fintype ι] {ω : ℕ} (hω : 1 ≤ ω)
    (X G : Matrix ι (Fin ω) ℝ) (hXr : X.rank = ω)
    (hspec : ∀ z : ℂ, (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank = ω) :
    ∃ S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) ι ℝ,
      S 0 * G = -1 ∧
      (∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0) ∧
      S (Fin.last (2 * ω - 2)) * X = 0 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let N : ℕ := Fintype.card ι
  let X' : Matrix (Fin N) (Fin ω) ℝ := X.submatrix (⇑e.symm) id
  let G' : Matrix (Fin N) (Fin ω) ℝ := G.submatrix (⇑e.symm) id
  have hX'r : X'.rank = ω := by
    have h := Matrix.rank_submatrix X e.symm (Equiv.refl (Fin ω))
    exact h.trans hXr
  have hspec' : ∀ z : ℂ, (z • X'.map (algebraMap ℝ ℂ) - G'.map (algebraMap ℝ ℂ)).rank = ω := by
    intro z
    have hEq : z • X'.map (algebraMap ℝ ℂ) - G'.map (algebraMap ℝ ℂ)
        = (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).submatrix (⇑e.symm) id := by
      ext i j
      simp [X', G', Matrix.submatrix_apply, Matrix.map_apply, Matrix.sub_apply,
        Matrix.smul_apply]
    rw [hEq]
    exact (Matrix.rank_submatrix (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)) e.symm
      (Equiv.refl (Fin ω))).trans (hspec z)
  obtain ⟨S', hS'0, hS'j, hS'd⟩ :=
    (coeff_iff_spectral (q := N) hω X' G' hX'r).mpr hspec'
  have hXsub : X'.submatrix (⇑e) id = X := by
    simp [X', Matrix.submatrix_submatrix, Equiv.symm_comp_self]
  have hGsub : G'.submatrix (⇑e) id = G := by
    simp [G', Matrix.submatrix_submatrix, Equiv.symm_comp_self]
  have hmulX : ∀ (P : Matrix (Fin ω) (Fin N) ℝ),
      P.submatrix id (⇑e) * X = (P * X').submatrix id id := by
    intro P
    rw [← hXsub, Matrix.submatrix_mul P X' (id : Fin ω → Fin ω) (⇑e)
      (id : Fin ω → Fin ω) e.bijective]
  have hmulG : ∀ (P : Matrix (Fin ω) (Fin N) ℝ),
      P.submatrix id (⇑e) * G = (P * G').submatrix id id := by
    intro P
    rw [← hGsub, Matrix.submatrix_mul P G' (id : Fin ω → Fin ω) (⇑e)
      (id : Fin ω → Fin ω) e.bijective]
  have hsub : ∀ (P Q : Matrix (Fin ω) (Fin N) ℝ),
      P.submatrix id (⇑e) * X - Q.submatrix id (⇑e) * G
        = (P * X' - Q * G').submatrix id id := by
    intro P Q
    rw [hmulX P, hmulG Q]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.sub_apply]
  refine ⟨fun j => (S' j).submatrix id (⇑e), ?_, ?_, ?_⟩
  · show (S' 0).submatrix id (⇑e) * G = -1
    rw [hmulG (S' 0), Matrix.submatrix_id_id, hS'0]
  · intro j
    show (S' (Fin.castSucc j)).submatrix id (⇑e) * X
      - (S' (Fin.succ j)).submatrix id (⇑e) * G = 0
    rw [hsub (S' (Fin.castSucc j)) (S' (Fin.succ j)), hS'j j]
    ext i jj
    simp
  · show (S' (Fin.last (2 * ω - 2))).submatrix id (⇑e) * X = 0
    rw [hmulX (S' (Fin.last (2 * ω - 2))), Matrix.submatrix_id_id, hS'd]

/-! ## 4.  Completeness of the encoding, from the compressed conditions -/

theorem exists_encodes_of_blocks {p r0 r n k : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (H HA : Matrix (Fin r0 ⊕ Fin r) (Fin k) ℝ)
    (hAlg : PaperI.compressedAlgebraic H HA)
    (hSpec : PaperI.compressedSpectral (H.map (algebraMap ℝ ℂ)) (HA.map (algebraMap ℝ ℂ)))
    (hB1 : ∀ i : Fin r0, H (Sum.inl i) = (L0 * N) i ∧
      HA (Sum.inl i) = (L0 * A * N) i)
    (hB2 : ∀ i : Fin r, ∃ ri : Fin n → ℝ, Matrix.vecMul ri N = H (Sum.inr i) ∧
      Matrix.vecMul ri (A * N) = HA (Sum.inr i)) :
    ∃ (ω : ℕ) (X G : Matrix (Fin r0 ⊕ Fin r) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
      (XL : Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin ω) ℝ)
      (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ),
      encodes C A L0 N X G B XL BR S := by
  classical
  by_cases hω : H.rank = 0
  · have hH0 : H = 0 := eq_zero_of_rank_eq_zero H hω
    have hHA0 : HA = 0 := by
      have h1 : (Matrix.fromRows HA H).rank = 0 := hAlg.trans hω
      have h2 : HA = (Matrix.fromRows HA H).submatrix
          (Sum.inl : (Fin r0 ⊕ Fin r) → (Fin r0 ⊕ Fin r) ⊕ (Fin r0 ⊕ Fin r)) id := by
        ext i j
        simp
      have h3 : ((Matrix.fromRows HA H).submatrix
          (Sum.inl : (Fin r0 ⊕ Fin r) → (Fin r0 ⊕ Fin r) ⊕ (Fin r0 ⊕ Fin r)) id).rank = 0 := by
        refine le_antisymm ?_ (Nat.zero_le _)
        calc ((Matrix.fromRows HA H).submatrix
              (Sum.inl : (Fin r0 ⊕ Fin r) → (Fin r0 ⊕ Fin r) ⊕ (Fin r0 ⊕ Fin r)) id).rank
            ≤ (Matrix.fromRows HA H).rank := Matrix.rank_submatrix_le _ _ _
          _ = 0 := h1
      rw [h2]
      exact eq_zero_of_rank_eq_zero _ h3
    refine ⟨0, 0, 0, 0, 0, 0, fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · ext i j
      exact i.elim0
    · ext i j
      exact i.elim0
    · ext i j
      exact i.elim0
    · intro j
      exact j.elim0
    · ext i j
      exact i.elim0
    · have hLN : ∀ (i : Fin r0) (j : Fin k), (L0 * N) i j = 0 := by
        intro i j
        have h := congrFun (hB1 i).1 j
        rw [← h, hH0]
        exact Matrix.zero_apply _ _
      have hLAN : ∀ (i : Fin r0) (j : Fin k), (L0 * A * N) i j = 0 := by
        intro i j
        have h := congrFun (hB1 i).2 j
        rw [← h, hHA0]
        exact Matrix.zero_apply _ _
      intro i
      refine ⟨?_, ?_⟩
      · ext j
        simp [hLN i j]
      · ext j
        simp [hLAN i j]
    · intro i
      obtain ⟨ri, h1, h2⟩ := hB2 i
      refine ⟨ri, ?_, ?_⟩
      · ext j
        simp [h1, hH0]
      · ext j
        simp [h2, hHA0]
  · have hω1 : 1 ≤ H.rank := Nat.one_le_iff_ne_zero.mpr hω
    have hrow : Q1Subspace.rowSpace HA ≤ Q1Subspace.rowSpace H :=
      (Q1Subspace.rank_fromRows_eq_rank_iff HA H).mp hAlg
    obtain ⟨F, hF⟩ := PaperI.exists_factor_of_rowSpace_le H HA hrow
    obtain ⟨X, B, XL, BR, hXB, hXL, hBR⟩ :=
      PaperI.RankFactorization.exists_rank_factorization_arb (K := ℝ) (ω := H.rank) H rfl
    let G : Matrix (Fin r0 ⊕ Fin r) (Fin H.rank) ℝ := F * X
    have hGB : G * B = HA := by
      show (F * X) * B = HA
      rw [Matrix.mul_assoc, hXB]
      exact hF.symm
    have hXr : X.rank = H.rank := rank_of_leftInverse X XL hXL
    have hspecC : ∀ z : ℂ,
        (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank = H.rank := by
      intro z
      have hXBc : X.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ)
          = H.map (algebraMap ℝ ℂ) := by
        rw [← Matrix.map_mul, hXB]
      have hGBc : G.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ)
          = HA.map (algebraMap ℝ ℂ) := by
        rw [← Matrix.map_mul, hGB]
      have hBRc : B.map (algebraMap ℝ ℂ) * BR.map (algebraMap ℝ ℂ) = 1 := by
        rw [← Matrix.map_mul, hBR]
        simp [Matrix.map_one]
      have hXc : (X.map (algebraMap ℝ ℂ)).rank = H.rank := by
        have h1 : XL.map (algebraMap ℝ ℂ) * X.map (algebraMap ℝ ℂ) = 1 := by
          rw [← Matrix.map_mul, hXL]
          simp [Matrix.map_one]
        exact rank_of_leftInverse_field _ _ h1
      have hHc : (H.map (algebraMap ℝ ℂ)).rank = H.rank := by
        refine le_antisymm ?_ ?_
        · calc (H.map (algebraMap ℝ ℂ)).rank
              = (X.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ)).rank := by rw [hXBc]
            _ ≤ (X.map (algebraMap ℝ ℂ)).rank := Matrix.rank_mul_le_left _ _
            _ = H.rank := hXc
        · have h4 : H.map (algebraMap ℝ ℂ) * BR.map (algebraMap ℝ ℂ)
              = X.map (algebraMap ℝ ℂ) := by
            rw [← hXBc, Matrix.mul_assoc, hBRc, Matrix.mul_one]
          calc H.rank = (X.map (algebraMap ℝ ℂ)).rank := hXc.symm
            _ = (H.map (algebraMap ℝ ℂ) * BR.map (algebraMap ℝ ℂ)).rank := by rw [h4]
            _ ≤ (H.map (algebraMap ℝ ℂ)).rank := Matrix.rank_mul_le_left _ _
      calc (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank
          = ((z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ))
              * B.map (algebraMap ℝ ℂ)).rank :=
            (rank_mul_rightInverse_field _ _ _ hBRc).symm
        _ = (z • H.map (algebraMap ℝ ℂ) - HA.map (algebraMap ℝ ℂ)).rank := by
            rw [Matrix.sub_mul, Matrix.smul_mul, hXBc, hGBc]
        _ = (H.map (algebraMap ℝ ℂ)).rank := hSpec z
        _ = H.rank := hHc
    obtain ⟨S, hS0, hSj, hSd⟩ := exists_coeff_left_inverse_arb hω1 X G hXr hspecC
    exact ⟨H.rank, X, G, B, XL, BR, S, hXL, hBR, hS0, hSj, hSd,
      (fun i => by
        refine ⟨?_, ?_⟩
        · rw [hXB]; exact (hB1 i).1
        · rw [hGB]; exact (hB1 i).2),
      (fun i => by
        obtain ⟨ri, h1, h2⟩ := hB2 i
        exact ⟨ri, by rw [hXB]; exact h1, by rw [hGB]; exact h2⟩)⟩


/-! ## 5.  Completeness from a feasible compressed pair `(L N, L A N)` -/

theorem exists_encodes_of_compressed {p r0 r n k : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (R : Matrix (Fin r) (Fin n) ℝ)
    (hAlg : PaperI.compressedAlgebraic
      (Matrix.fromRows L0 R * N) (Matrix.fromRows L0 R * A * N))
    (hSpec : PaperI.compressedSpectral
      ((Matrix.fromRows L0 R * N).map (algebraMap ℝ ℂ))
      ((Matrix.fromRows L0 R * A * N).map (algebraMap ℝ ℂ))) :
    ∃ (ω : ℕ) (X G : Matrix (Fin r0 ⊕ Fin r) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
      (XL : Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin ω) ℝ)
      (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ),
      encodes C A L0 N X G B XL BR S := by
  refine exists_encodes_of_blocks C A L0 N
    (Matrix.fromRows L0 R * N) (Matrix.fromRows L0 R * A * N) hAlg hSpec ?_ ?_
  · intro i
    refine ⟨?_, ?_⟩
    · rw [fromRows_mul_row_inl]
    · rw [fromRows_mul, fromRows_mul_row_inl]
  · intro i
    have hR : (Matrix.fromRows L0 R) (Sum.inr i) = R i := by
      funext j
      exact Matrix.fromRows_apply_inr L0 R i j
    refine ⟨(Matrix.fromRows L0 R) (Sum.inr i), ?_, ?_⟩
    · rw [fromRows_mul_row_inr, hR]
      funext j
      simp [Matrix.vecMul, dotProduct, Matrix.mul_apply]
    · rw [fromRows_mul, fromRows_mul_row_inr, hR, Matrix.mul_assoc]
      funext j
      simp [Matrix.vecMul, dotProduct, Matrix.mul_apply]

/-! ## 6.  The `∃ R` form -/

theorem exists_encodes_of_exists_compressed {p r0 r n k : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (h : ∃ R : Matrix (Fin r) (Fin n) ℝ,
      PaperI.compressedAlgebraic
          (Matrix.fromRows L0 R * N) (Matrix.fromRows L0 R * A * N) ∧
        PaperI.compressedSpectral
          ((Matrix.fromRows L0 R * N).map (algebraMap ℝ ℂ))
          ((Matrix.fromRows L0 R * A * N).map (algebraMap ℝ ℂ))) :
    ∃ (ω : ℕ) (X G : Matrix (Fin r0 ⊕ Fin r) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
      (XL : Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin ω) ℝ)
      (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ),
      encodes C A L0 N X G B XL BR S := by
  obtain ⟨R, h1, h2⟩ := h
  exact exists_encodes_of_compressed C A L0 N R h1 h2


/-! ## 7.  The converse transport: `encodes` implies the complex-`λ` conditions

Read with `exists_encodes_of_compressed`, this says that the paper's system
`Φ_ω` is satisfiable exactly when some feasible `R` makes the compressed pair
satisfy (5a) and (5b) *with the ranks taken at complex parameters*. -/

theorem exists_compressed_complex_of_encodes {p r0 r n k ω : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (X G : Matrix (Fin r0 ⊕ Fin r) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
    (XL : Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin ω) ℝ)
    (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ)
    (henc : encodes C A L0 N X G B XL BR S) :
    ∃ R : Matrix (Fin r) (Fin n) ℝ,
      PaperI.compressedAlgebraic (Matrix.fromRows L0 R * N)
          (Matrix.fromRows L0 R * A * N) ∧
        PaperI.compressedSpectral
          ((Matrix.fromRows L0 R * N).map (algebraMap ℝ ℂ))
          ((Matrix.fromRows L0 R * A * N).map (algebraMap ℝ ℂ)) := by
  obtain ⟨hXL, hBR, hS0, hSj, hSd, hB1, hB2⟩ := henc
  choose R hR using hB2
  let Rm : Matrix (Fin r) (Fin n) ℝ := R
  have hLN : Matrix.fromRows L0 Rm * N = X * B := by
    ext i kk
    cases i with
    | inl i =>
        rw [fromRows_mul_row_inl]
        exact (congrFun (hB1 i).1 kk).symm
    | inr i =>
        rw [fromRows_mul_row_inr]
        have h := congrFun (hR i).1 kk
        simpa [Matrix.vecMul, dotProduct, Matrix.mul_apply] using h
  have hLAN : Matrix.fromRows L0 Rm * A * N = G * B := by
    have hLA : Matrix.fromRows L0 Rm * A = Matrix.fromRows (L0 * A) (Rm * A) :=
      fromRows_mul L0 R A
    ext i kk
    cases i with
    | inl i =>
        rw [hLA, fromRows_mul_row_inl]
        exact (congrFun (hB1 i).2 kk).symm
    | inr i =>
        rw [hLA, fromRows_mul_row_inr, Matrix.mul_assoc]
        have h := congrFun (hR i).2 kk
        simpa [Matrix.vecMul, dotProduct, Matrix.mul_apply] using h
  have hfac : G * B = (G * XL) * (X * B) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc XL X B, hXL, Matrix.one_mul]
  refine ⟨Rm, ?_, ?_⟩
  · show PaperI.compressedAlgebraic (Matrix.fromRows L0 Rm * N) (Matrix.fromRows L0 Rm * A * N)
    rw [hLN, hLAN]
    exact compressedAlgebraic_of_eq_mul (H := X * B) (HA := G * B) (F := G * XL) hfac
  · show PaperI.compressedSpectral ((Matrix.fromRows L0 Rm * N).map (algebraMap ℝ ℂ))
      ((Matrix.fromRows L0 Rm * A * N).map (algebraMap ℝ ℂ))
    rw [hLN, hLAN]
    intro z
    have hXBc : (X * B).map (algebraMap ℝ ℂ)
        = X.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ) := by
      rw [Matrix.map_mul]
    have hGBc : (G * B).map (algebraMap ℝ ℂ)
        = G.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ) := by
      rw [Matrix.map_mul]
    have hBRc : B.map (algebraMap ℝ ℂ) * BR.map (algebraMap ℝ ℂ) = 1 := by
      rw [← Matrix.map_mul, hBR]
      simp [Matrix.map_one]
    have hXc : (X.map (algebraMap ℝ ℂ)).rank = ω := by
      have h1 : XL.map (algebraMap ℝ ℂ) * X.map (algebraMap ℝ ℂ) = 1 := by
        rw [← Matrix.map_mul, hXL]
        simp [Matrix.map_one]
      exact rank_of_leftInverse_field _ _ h1
    have hXcBc : (X.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ)).rank = ω := by
      refine le_antisymm ?_ ?_
      · calc (X.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ)).rank
            ≤ (X.map (algebraMap ℝ ℂ)).rank := Matrix.rank_mul_le_left _ _
          _ = ω := hXc
      · have h4 : X.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ)
            * BR.map (algebraMap ℝ ℂ) = X.map (algebraMap ℝ ℂ) := by
          rw [Matrix.mul_assoc, hBRc, Matrix.mul_one]
        calc ω = (X.map (algebraMap ℝ ℂ)).rank := hXc.symm
          _ = (X.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ)
                * BR.map (algebraMap ℝ ℂ)).rank := by rw [h4]
          _ ≤ (X.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ)).rank :=
              Matrix.rank_mul_le_left _ _
    calc (z • (X * B).map (algebraMap ℝ ℂ) - (G * B).map (algebraMap ℝ ℂ)).rank
        = ((z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ))
            * B.map (algebraMap ℝ ℂ)).rank := by
          rw [hXBc, hGBc, Matrix.sub_mul, Matrix.smul_mul]
      _ = (z • X.map (algebraMap ℝ ℂ) - G.map (algebraMap ℝ ℂ)).rank :=
          rank_mul_rightInverse_field _ _ _ hBRc
      _ = ω := v_implies_i_real X G S hS0 hSj hSd z
      _ = (X.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ)).rank := hXcBc.symm
      _ = ((X * B).map (algebraMap ℝ ℂ)).rank := by rw [hXBc]


/-! ## 8.  The encoding is exactly the complex-`λ` conditions -/

theorem exists_encodes_iff {p r0 r n k : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ) :
    (∃ R : Matrix (Fin r) (Fin n) ℝ,
        PaperI.compressedAlgebraic (Matrix.fromRows L0 R * N)
            (Matrix.fromRows L0 R * A * N) ∧
          PaperI.compressedSpectral
            ((Matrix.fromRows L0 R * N).map (algebraMap ℝ ℂ))
            ((Matrix.fromRows L0 R * A * N).map (algebraMap ℝ ℂ))) ↔
      (∃ (ω : ℕ) (X G : Matrix (Fin r0 ⊕ Fin r) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
        (XL : Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin ω) ℝ)
        (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ),
        encodes C A L0 N X G B XL BR S) := by
  constructor
  · intro h
    exact exists_encodes_of_exists_compressed C A L0 N h
  · rintro ⟨ω, X, G, B, XL, BR, S, h⟩
    exact exists_compressed_complex_of_encodes C A L0 N X G B XL BR S h

end Thm5

end Q1Paper
