
import Q1Paper.PaperI.S07_ExistsReal.T5Complete
import Q1Paper.PaperI.S08_ChartEquivalence.Complexify
import Q1Paper.PaperI.S03_Certificate.MinorRank
import Q1Paper.RowSpaceAlgebraic
import Q1Paper.SubspaceQuotient
/-!
Q1Paper/PaperI/S07_ExistsReal/T5DecC.lean

Closing the remaining pieces of Theorem 5 of Paper I that are *not* covered by
`Q1Paper/PaperI/Theorem5.lean` and `Q1Paper/PaperI/T5Complete.lean`:

1. **The complex interface.**  `Q1Paper.PaperI.DECℂ` is the paper's decision
   problem: the design `R` is real, all ranks are taken over `ℂ`, and `(5b)`
   quantifies over `λ : ℂ`.  `T5Complete.exists_encodes_iff` relates `encodes`
   to the *existential-over-`R`* compressed conditions, but only over the real
   kernel basis `N` of `ker [CA; C]`.  The missing bridge is
   "the complexification of a real basis matrix `N` of `ker [CA; C]` is a
   complex basis matrix of `ker [C_ℂ A_ℂ; C_ℂ]`", a rank/dimension count.
   Here it is proved as `range_map_ofReal_of_ker` (it needs `N.rank = k`, i.e.
   the columns of `N` are independent — a genuine restriction, as it must be),
   and the complex form of Theorem 5 follows:

   `DECℂ_iff_exists_encodes` :
     `PaperI.DECℂ C A L₀ r ↔ ∃ ω X G B X_L B_R S, encodes C A L₀ N X G B X_L B_R S`.

   So the left-hand side is the paper's `DEC(q)` (complex `λ`), not the real-`λ`
   `PaperI.DEC`.

2. **The `D`-form of (B2).**  The paper writes (B2) as
   `D [(X_i B)ᵀ; (G_i B)ᵀ] = 0` with `ker D = row [N  AN]`; `encodes` uses the
   equivalent "there is a preimage" form.  `rowPairMatrix` is `[N  AN]` as a
   `n × (k ⊕ k)` matrix, `stackRows` stacks the two `k`-rows, and
   `mem_ker_rowPair_iff` proves, for a `D` with `ker D = row [N  AN]`,

     `D *ᵥ stackRows u v = 0 ↔ ∃ r, r ᵥ* N = u ∧ r ᵥ* (A N) = v`,

   from which `encodesD_iff_encodes` gives the equivalence of the whole system
   in `D`-form with `encodes`.

3. **The `ω = 0` branch.**  When `rank H = 0` the paper's system degenerates:
   all blocks are `0`, the `S`-block is vacuous (`Fin (2*0-2+1) = Fin 1` and
   its matrices are empty).  `encodes_of_rank_zero` states this for the block
   pair `(H, H_A)`, and `encodes_of_rank_zero_compressed` for `H = L N`,
   `H_A = L A N` with `L = [L₀; R]` — the paper's "`L₀N = 0`" branch.
   `exists_compressed_zero_of_encodes_zero` is the converse reading: a solution
   with `ω = 0` produces an `R` with `L N = 0` and `L A N = 0`.

No `sorry`, no `admit`, no new axioms.
-/


namespace Q1Paper

open Matrix Polynomial

namespace Thm5

/-! ## 1.  Complexification does not change the rank, for any finite index type

`PaperI.rank_map_ofReal` is stated for `Fin`-indexed matrices.  The rows of the
observer have index type `Fin r₀ ⊕ Fin r`, so we need the general form; it is
obtained by reindexing with `Fintype.equivFin` and `Matrix.rank_reindex`. -/

/-- Complexification does not change the rank (arbitrary finite index types). -/
theorem rank_map_ofReal_arb {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) :
    (M.map (algebraMap ℝ ℂ)).rank = M.rank := by
  classical
  let em : m ≃ Fin (Fintype.card m) := Fintype.equivFin m
  let en : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  have hre : ((M.map (algebraMap ℝ ℂ)).reindex em en)
      = (M.reindex em en).map (algebraMap ℝ ℂ) := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.map_apply]
  calc (M.map (algebraMap ℝ ℂ)).rank
      = ((M.map (algebraMap ℝ ℂ)).reindex em en).rank :=
        (Matrix.rank_reindex em en _).symm
    _ = ((M.reindex em en).map (algebraMap ℝ ℂ)).rank := by rw [hre]
    _ = (M.reindex em en).rank := PaperI.rank_map_ofReal _
    _ = M.rank := Matrix.rank_reindex em en M

/-- Complexification commutes with `fromRows`. -/
theorem fromRows_map_ofReal {m₁ m₂ n : Type*}
    (A : Matrix m₁ n ℝ) (B : Matrix m₂ n ℝ) :
    Matrix.fromRows (A.map (algebraMap ℝ ℂ)) (B.map (algebraMap ℝ ℂ))
      = (Matrix.fromRows A B).map (algebraMap ℝ ℂ) := by
  ext i j
  cases i with
  | inl i => simp [Matrix.map_apply]
  | inr i => simp [Matrix.map_apply]

/-- **(5a) is invariant under complexification**: the compressed algebraic
condition over `ℂ` for `(H_ℂ, H_Aℂ)` is the same as over `ℝ` for `(H, H_A)`. -/
theorem compressedAlgebraic_map_ofReal_iff {q k : Type*} [Fintype q] [Fintype k]
    (H HA : Matrix q k ℝ) :
    PaperI.compressedAlgebraic (H.map (algebraMap ℝ ℂ)) (HA.map (algebraMap ℝ ℂ)) ↔
      PaperI.compressedAlgebraic H HA := by
  unfold PaperI.compressedAlgebraic
  simp only [fromRows_map_ofReal, rank_map_ofReal_arb]

/-! ## 2.  The complex kernel basis

If `N` is a real basis matrix of `ker [CA; C]` (its columns are independent and
its range is the kernel), then `N_ℂ` is a complex basis matrix of
`ker [C_ℂ A_ℂ; C_ℂ]`.  The inclusion `range N_ℂ ≤ ker P_ℂ` is immediate
(`P N = 0`); the two spaces are then compared by dimension. -/

/-- **The complexification of a real kernel basis is a complex kernel basis.** -/
theorem range_map_ofReal_of_ker {m : Type*} [Fintype m] {n k : ℕ}
    (P : Matrix m (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (hN : N.mulVecLin.range = P.mulVecLin.ker) (hNk : N.rank = k) :
    (N.map (algebraMap ℝ ℂ)).mulVecLin.range
      = (P.map (algebraMap ℝ ℂ)).mulVecLin.ker := by
  classical
  -- `P * N = 0`, from `range N ⊆ ker P` column by column
  have hPN : P * N = 0 := by
    ext i j
    have hmem : N.col j ∈ N.mulVecLin.range := by
      refine ⟨Pi.single j 1, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_single]
      simp
    rw [hN] at hmem
    have hzero : P.mulVec (N.col j) = 0 := by simpa using hmem
    have hcol : (P * N).col j = 0 := by
      have h1 : P.mulVec (N.col j) = (P * N).col j := by
        ext x
        simp [Matrix.mulVec, Matrix.col, dotProduct, Matrix.mul_apply]
      rw [← h1]
      exact hzero
    have h2 := congrFun hcol i
    simpa [Matrix.col] using h2
  -- `range N_ℂ ≤ ker P_ℂ`
  have hle : (N.map (algebraMap ℝ ℂ)).mulVecLin.range
      ≤ (P.map (algebraMap ℝ ℂ)).mulVecLin.ker := by
    rintro w ⟨v, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPN]
    simp
  -- dimension of `range N_ℂ`
  have hdimN : Module.finrank ℂ ↥((N.map (algebraMap ℝ ℂ)).mulVecLin.range) = k := by
    change (N.map (algebraMap ℝ ℂ)).rank = k
    rw [rank_map_ofReal_arb, hNk]
  -- `rank P + k = n`, over `ℝ`
  have hPn : P.rank + k = n := by
    have h := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    have h1 : Module.finrank ℝ ↥(P.mulVecLin.range) = P.rank := rfl
    have h2 : Module.finrank ℝ ↥(P.mulVecLin.ker) = k := by
      rw [← hN]
      change N.rank = k
      exact hNk
    rw [h1, h2] at h
    have h3 : Module.finrank ℝ (Fin n → ℝ) = n := by simp
    omega
  -- dimension of `ker P_ℂ`
  have hdimKer : Module.finrank ℂ ↥((P.map (algebraMap ℝ ℂ)).mulVecLin.ker) = k := by
    have h := LinearMap.finrank_range_add_finrank_ker (P.map (algebraMap ℝ ℂ)).mulVecLin
    have h1 : Module.finrank ℂ ↥((P.map (algebraMap ℝ ℂ)).mulVecLin.range) = P.rank := by
      change (P.map (algebraMap ℝ ℂ)).rank = P.rank
      rw [rank_map_ofReal_arb]
    rw [h1] at h
    have h3 : Module.finrank ℂ (Fin n → ℂ) = n := by simp
    rw [h3] at h
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hdimN, hdimKer])

/-! ## 3.  The complex form of Theorem 5

`PaperI.DECℂ` is the paper's `DEC(q)`: the design `R` is real, the ranks are
over `ℂ`, and `(5b)` quantifies over `λ : ℂ`.  `PaperI.DEC_complex_iff_compressed`
turns it into the compressed conditions; `rank_map_ofReal_arb` /
`compressedAlgebraic_map_ofReal_iff` identify them with the real compressed pair
`(L N, L A N)` that `exists_encodes_iff` speaks about. -/

/-- **`DECℂ` in compressed form.**  The paper's decision problem (real design,
complex ranks, `λ : ℂ`) holds exactly when some real `R` makes the compressed pair
`(L N, L A N)`, `L = [L₀; R]`, satisfy (5a) over `ℝ` and (5b) at every complex
parameter.  The hypothesis says that the real `N` is a basis matrix of
`ker [CA; C]`: its range is the kernel and its columns are independent. -/
theorem DECℂ_iff_exists_compressed {p r0 r n k : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (hN : N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker)
    (hNk : N.rank = k) :
    PaperI.DECℂ C A L0 r ↔
      ∃ R : Matrix (Fin r) (Fin n) ℝ,
        PaperI.compressedAlgebraic (Matrix.fromRows L0 R * N)
            (Matrix.fromRows L0 R * A * N) ∧
          PaperI.compressedSpectral
            ((Matrix.fromRows L0 R * N).map (algebraMap ℝ ℂ))
            ((Matrix.fromRows L0 R * A * N).map (algebraMap ℝ ℂ)) := by
  classical
  have hNc : (N.map (algebraMap ℝ ℂ)).mulVecLin.range =
      (Matrix.fromRows ((C.map (algebraMap ℝ ℂ)) * (A.map (algebraMap ℝ ℂ)))
        (C.map (algebraMap ℝ ℂ))).mulVecLin.ker := by
    have h := range_map_ofReal_of_ker (P := Matrix.fromRows (C * A) C) (N := N) hN hNk
    rw [← Matrix.map_mul, fromRows_map_ofReal]
    exact h
  rw [PaperI.DEC_complex_iff_compressed C A L0 r (N.map (algebraMap ℝ ℂ)) hNc]
  constructor
  · rintro ⟨R, h1, h2⟩
    have e1 : (Matrix.fromRows L0 R).map (algebraMap ℝ ℂ)
          * N.map (algebraMap ℝ ℂ)
        = (Matrix.fromRows L0 R * N).map (algebraMap ℝ ℂ) :=
      (Matrix.map_mul).symm
    have e2 : ((Matrix.fromRows L0 R).map (algebraMap ℝ ℂ)
            * A.map (algebraMap ℝ ℂ)) * N.map (algebraMap ℝ ℂ)
        = (Matrix.fromRows L0 R * A * N).map (algebraMap ℝ ℂ) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
    refine ⟨R, ?_, ?_⟩
    · rw [e1, e2] at h1
      exact (compressedAlgebraic_map_ofReal_iff _ _).mp h1
    · rw [e1, e2] at h2
      exact h2
  · rintro ⟨R, h1, h2⟩
    have e1 : (Matrix.fromRows L0 R).map (algebraMap ℝ ℂ)
          * N.map (algebraMap ℝ ℂ)
        = (Matrix.fromRows L0 R * N).map (algebraMap ℝ ℂ) :=
      (Matrix.map_mul).symm
    have e2 : ((Matrix.fromRows L0 R).map (algebraMap ℝ ℂ)
            * A.map (algebraMap ℝ ℂ)) * N.map (algebraMap ℝ ℂ)
        = (Matrix.fromRows L0 R * A * N).map (algebraMap ℝ ℂ) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
    refine ⟨R, ?_, ?_⟩
    · rw [e1, e2]
      exact (compressedAlgebraic_map_ofReal_iff _ _).mpr h1
    · rw [e1, e2]
      exact h2

/-- **Theorem 5 of Paper I, complex form.**  The paper's `DEC(q)` (real design,
ranks and the spectral parameter over `ℂ`) holds exactly when the polynomial system
`Φ_ω` of the paper's proof has a real solution, for some `ω`, with `N` a real basis
matrix of `ker [CA; C]`.  Obtained by composing `DECℂ_iff_exists_compressed` with
`exists_encodes_iff`. -/
theorem DECℂ_iff_exists_encodes {p r0 r n k : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (hN : N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker)
    (hNk : N.rank = k) :
    PaperI.DECℂ C A L0 r ↔
      ∃ (ω : ℕ) (X G : Matrix (Fin r0 ⊕ Fin r) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
        (XL : Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin ω) ℝ)
        (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ),
        encodes C A L0 N X G B XL BR S :=
  (DECℂ_iff_exists_compressed C A L0 N hN hNk).trans (exists_encodes_iff C A L0 N)

/-! ## 4.  The `D`-form of condition (B2)

The paper states (B2) as `D [(X_i B)ᵀ; (G_i B)ᵀ] = 0`, where `D` is any matrix
with `ker D = row [N  AN]`.  `encodes` uses the "exhibited preimage" form.
Both are the same condition; this section makes the translation explicit. -/

/-- `[N  AN]` as a single `n × (k ⊕ k)` matrix: column `inl a` is `N`'s column
`a`, column `inr a` is `(A N)`'s column `a`.  The paper's `row [N  AN]` is
`Q1Subspace.rowSpace (rowPairMatrix A N)`. -/
def rowPairMatrix {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ) : Matrix (Fin n) (Fin k ⊕ Fin k) ℝ :=
  fun i c => Sum.elim (fun a => N i a) (fun a => (A * N) i a) c

/-- Stack the two `k`-rows `u` and `v` into one vector on `Fin k ⊕ Fin k`. -/
def stackRows {k : ℕ} (u v : Fin k → ℝ) : Fin k ⊕ Fin k → ℝ :=
  Sum.elim u v

/-- A row of `[N  AN]`, read through a coefficient vector `r`. -/
theorem vecMul_rowPairMatrix {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ) (r : Fin n → ℝ) :
    Matrix.vecMul r (rowPairMatrix A N)
      = stackRows (Matrix.vecMul r N) (Matrix.vecMul r (A * N)) := by
  ext c
  cases c with
  | inl a => rfl
  | inr a => rfl

/-- `stackRows` is injective. -/
theorem stackRows_inj {k : ℕ} {u v u' v' : Fin k → ℝ} :
    stackRows u v = stackRows u' v' ↔ u = u' ∧ v = v' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext a
      exact congrFun h (Sum.inl a)
    · funext a
      exact congrFun h (Sum.inr a)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **The `D`-form and the preimage form of (B2) agree**, for any `D` whose
kernel is `row [N  AN]`. -/
theorem mem_ker_rowPair_iff {s n k : ℕ}
    (D : Matrix (Fin s) (Fin k ⊕ Fin k) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ)
    (hD : D.mulVecLin.ker = Q1Subspace.rowSpace (rowPairMatrix A N))
    (u v : Fin k → ℝ) :
    D.mulVec (stackRows u v) = 0 ↔
      ∃ ri : Fin n → ℝ, Matrix.vecMul ri N = u ∧ Matrix.vecMul ri (A * N) = v := by
  have hmem : (stackRows u v ∈ Q1Subspace.rowSpace (rowPairMatrix A N)) ↔
      ∃ ri : Fin n → ℝ, Matrix.vecMul ri (rowPairMatrix A N) = stackRows u v :=
    Q1Subspace.mem_rowSpan_iff_exists_vecMul (rowPairMatrix A N) (stackRows u v)
  have h1 : (stackRows u v ∈ D.mulVecLin.ker) ↔ D.mulVec (stackRows u v) = 0 := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [← h1, hD, hmem]
  constructor
  · rintro ⟨ri, hri⟩
    rw [vecMul_rowPairMatrix, stackRows_inj] at hri
    exact ⟨ri, hri⟩
  · rintro ⟨ri, h1', h2'⟩
    exact ⟨ri, by rw [vecMul_rowPairMatrix, h1', h2']⟩

/-- The paper's system with (B2) in `D`-form.  It differs from `encodes` only in
the last conjunct. -/
def encodesD {p r0 r n k ω s : ℕ}
    (_C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (D : Matrix (Fin s) (Fin k ⊕ Fin k) ℝ)
    (X G : Matrix (Fin r0 ⊕ Fin r) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
    (XL : Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin ω) ℝ)
    (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) : Prop :=
  XL * X = 1 ∧
  B * BR = 1 ∧
  S 0 * G = -1 ∧
  (∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0) ∧
  S (Fin.last (2 * ω - 2)) * X = 0 ∧
  (∀ i : Fin r0, (X * B) (Sum.inl i) = (L0 * N) i ∧
                 (G * B) (Sum.inl i) = (L0 * A * N) i) ∧
  (∀ i : Fin r, D.mulVec (stackRows ((X * B) (Sum.inr i)) ((G * B) (Sum.inr i))) = 0)

/-- **`D`-form of (B2) is the `∃`-preimage form**: the whole system `Φ_ω` is
unchanged when (B2) is written as `D [(X_iB)ᵀ; (G_iB)ᵀ] = 0` with
`ker D = row [N  AN]`. -/
theorem encodesD_iff_encodes {p r0 r n k ω s : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (D : Matrix (Fin s) (Fin k ⊕ Fin k) ℝ)
    (hD : D.mulVecLin.ker = Q1Subspace.rowSpace (rowPairMatrix A N))
    (X G : Matrix (Fin r0 ⊕ Fin r) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
    (XL : Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin ω) ℝ)
    (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) :
    encodesD C A L0 N D X G B XL BR S ↔ encodes C A L0 N X G B XL BR S := by
  unfold encodesD encodes
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h5, h6,
      fun i => (mem_ker_rowPair_iff D A N hD _ _).mp (h7 i)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h5, h6,
      fun i => (mem_ker_rowPair_iff D A N hD _ _).mpr (h7 i)⟩

/-! ## 5.  The `ω = 0` branch

`rank H = 0` forces `H = 0` and, together with `(5a)`, `H_A = 0`.  Then all
blocks can be taken zero: `X, G` have zero columns, `B` has zero rows, and the
`S`-block is vacuous because `2*0 - 2 + 1 = 1` and the matrices are `0 × _`. -/

/-- **The degenerate branch**: if the compressed block has rank zero, the
paper's system is satisfiable with `ω = 0` and all blocks zero. -/
theorem encodes_of_rank_zero {p r0 r n k : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (H HA : Matrix (Fin r0 ⊕ Fin r) (Fin k) ℝ)
    (hAlg : PaperI.compressedAlgebraic H HA) (hH : H.rank = 0)
    (hB1 : ∀ i : Fin r0, H (Sum.inl i) = (L0 * N) i ∧
      HA (Sum.inl i) = (L0 * A * N) i)
    (hB2 : ∀ i : Fin r, ∃ ri : Fin n → ℝ, Matrix.vecMul ri N = H (Sum.inr i) ∧
      Matrix.vecMul ri (A * N) = HA (Sum.inr i)) :
    ∃ (X G : Matrix (Fin r0 ⊕ Fin r) (Fin 0) ℝ) (B : Matrix (Fin 0) (Fin k) ℝ)
      (XL : Matrix (Fin 0) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin 0) ℝ)
      (S : Fin (2 * 0 - 2 + 1) → Matrix (Fin 0) (Fin r0 ⊕ Fin r) ℝ),
      encodes C A L0 N X G B XL BR S := by
  classical
  have hH0 : H = 0 := eq_zero_of_rank_eq_zero H hH
  have hHA0 : HA = 0 := by
    have h1 : (Matrix.fromRows HA H).rank = 0 := hAlg.trans hH
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
  refine ⟨0, 0, 0, 0, 0, fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro i
    have hLN : ∀ (i : Fin r0) (j : Fin k), (L0 * N) i j = 0 := by
      intro i j
      have h := congrFun (hB1 i).1 j
      rw [← h, hH0]
      exact Matrix.zero_apply _ _
    have hLAN : ∀ (i : Fin r0) (j : Fin k), (L0 * A * N) i j = 0 := by
      intro i j
      have h := congrFun (hB1 i).2 j
      rw [← h, hHA0]
      exact Matrix.zero_apply _ _
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

/-- The `ω = 0` branch for `H = L N`, `H_A = L A N` with `L = [L₀; R]`: if the
compressed block is zero then the paper's `L₀N = 0` branch satisfies `encodes`. -/
theorem encodes_of_rank_zero_compressed {p r0 r n k : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (R : Matrix (Fin r) (Fin n) ℝ)
    (hH : (Matrix.fromRows L0 R * N).rank = 0)
    (hHA : Matrix.fromRows L0 R * A * N = 0) :
    ∃ (X G : Matrix (Fin r0 ⊕ Fin r) (Fin 0) ℝ) (B : Matrix (Fin 0) (Fin k) ℝ)
      (XL : Matrix (Fin 0) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin 0) ℝ)
      (S : Fin (2 * 0 - 2 + 1) → Matrix (Fin 0) (Fin r0 ⊕ Fin r) ℝ),
      encodes C A L0 N X G B XL BR S := by
  classical
  have hH0 : Matrix.fromRows L0 R * N = 0 := eq_zero_of_rank_eq_zero _ hH
  refine encodes_of_rank_zero C A L0 N (Matrix.fromRows L0 R * N)
    (Matrix.fromRows L0 R * A * N) ?_ hH ?_ ?_
  · unfold PaperI.compressedAlgebraic
    have hz : Matrix.fromRows (0 : Matrix (Fin r0 ⊕ Fin r) (Fin k) ℝ)
        (0 : Matrix (Fin r0 ⊕ Fin r) (Fin k) ℝ) = 0 := by
      ext i j
      cases i <;> rfl
    rw [hHA, hH0, hz]
    simp
  · intro i
    refine ⟨?_, ?_⟩
    · exact fromRows_mul_row_inl L0 R N i
    · rw [fromRows_mul L0 R A, fromRows_mul_row_inl]
  · intro i
    refine ⟨R i, ?_, ?_⟩
    · show Matrix.vecMul (R i) N = (Matrix.fromRows L0 R * N) (Sum.inr i)
      rw [fromRows_mul_row_inr]
      funext j
      simp [Matrix.vecMul, dotProduct, Matrix.mul_apply]
    · show Matrix.vecMul (R i) (A * N) = (Matrix.fromRows L0 R * A * N) (Sum.inr i)
      rw [fromRows_mul L0 R A, fromRows_mul_row_inr, Matrix.mul_assoc]
      funext j
      simp [Matrix.vecMul, dotProduct, Matrix.mul_apply]

/-- **The converse reading of the degenerate branch**: a solution with `ω = 0`
produces a real `R` whose compressed block `(L N, L A N)` vanishes, i.e. the
`ω = 0` disjunct is exactly the `L₀N = 0` branch of the paper. -/
theorem exists_compressed_zero_of_encodes_zero {p r0 r n k : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (X G : Matrix (Fin r0 ⊕ Fin r) (Fin 0) ℝ) (B : Matrix (Fin 0) (Fin k) ℝ)
    (XL : Matrix (Fin 0) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin 0) ℝ)
    (S : Fin (2 * 0 - 2 + 1) → Matrix (Fin 0) (Fin r0 ⊕ Fin r) ℝ)
    (henc : encodes C A L0 N X G B XL BR S) :
    ∃ R : Matrix (Fin r) (Fin n) ℝ,
      Matrix.fromRows L0 R * N = 0 ∧ Matrix.fromRows L0 R * A * N = 0 := by
  obtain ⟨hXL, hBR, hS0, hSj, hSd, hB1, hB2⟩ := henc
  choose R hR using hB2
  let Rm : Matrix (Fin r) (Fin n) ℝ := R
  have hXB : X * B = 0 := by
    ext i j
    simp [Matrix.mul_apply]
  have hGB : G * B = 0 := by
    ext i j
    simp [Matrix.mul_apply]
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
      fromRows_mul L0 Rm A
    ext i kk
    cases i with
    | inl i =>
        rw [hLA, fromRows_mul_row_inl]
        exact (congrFun (hB1 i).2 kk).symm
    | inr i =>
        rw [hLA, fromRows_mul_row_inr, Matrix.mul_assoc]
        have h := congrFun (hR i).2 kk
        simpa [Matrix.vecMul, dotProduct, Matrix.mul_apply] using h
  refine ⟨Rm, ?_, ?_⟩
  · rw [hLN, hXB]
  · rw [hLAN, hGB]

end Thm5

end Q1Paper
