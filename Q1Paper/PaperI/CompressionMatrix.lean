/-
Q1Paper/PaperI/CompressionMatrix.lean

Matrix-level Claim 2 of Paper I: for `N` a basis matrix of `ker [CA; C]`, the
raw conditions (5a), (5b) on the row stack `[LA; L; CA; C]` are equivalent to
the compressed conditions on `H = L N` and `H_A = L A N`.

The proof uses only

* the rank identity `rank [P; M] = rank P + rank (M N_P)` (`G4RankIdentity`),
* its commutativity in the order of the two blocks,
* the kernel identity `ker [L; P] = N (ker (L N))`,

so no duality (and hence no choice of an inner product) is needed.  The field
is arbitrary; the transfer `Q -> R -> C` of the paper's input is a separate
step and is not part of this file.
-/

import Q1Paper.G4RankIdentity
import Q1Paper.Q1RowSpace
import Q1Paper.PaperI.Interface

namespace Q1Paper.PaperI

open Matrix

variable {K : Type*} [Field K]

/-! ### The rank of a row stack does not depend on the order of the blocks -/

theorem rank_fromRows_comm {m m' n : Type*} [Fintype m] [Fintype m'] [Fintype n]
    (A : Matrix m n K) (B : Matrix m' n K) :
    (Matrix.fromRows A B).rank = (Matrix.fromRows B A).rank := by
  rw [Q1Subspace.rank_eq_finrank_rowSpace, Q1Subspace.rank_eq_finrank_rowSpace,
    Q1Subspace.rowSpace_fromRows, Q1Subspace.rowSpace_fromRows, sup_comm]

/-! ### The rank identity at arbitrary finite index types

`G4RankIdentity.rank_vstack_add_rank_mul` is stated for `Fin` indices; the
paper's stacks use sum types, so the same proof is repeated here for arbitrary
finite index types. -/

theorem rank_fromRows_add_map {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (P : Matrix m n K) (M : Matrix p n K) :
    (Matrix.fromRows P M).rank =
      P.rank + Module.finrank K ↥(Submodule.map M.mulVecLin P.mulVecLin.ker) := by
  classical
  let e := Q1Paper.sumArrowEquivProd (K := K) m p
  have hpair :
      e.toLinearMap.comp (Matrix.fromRows P M).mulVecLin =
        P.mulVecLin.prod M.mulVecLin := by
    refine LinearMap.ext ?_
    intro v
    apply Prod.ext <;> funext i <;>
      simp [e, Q1Paper.sumArrowEquivProd, Matrix.mulVecLin_apply, Matrix.fromRows_apply_inl,
        Matrix.fromRows_apply_inr, Matrix.mulVec]
  have hrange :
      (P.mulVecLin.prod M.mulVecLin).range =
        Submodule.map e.toLinearMap (Matrix.fromRows P M).mulVecLin.range := by
    rw [← hpair, LinearMap.range_comp]
  calc (Matrix.fromRows P M).rank
      = Module.finrank K ↥(Matrix.fromRows P M).mulVecLin.range := rfl
    _ = Module.finrank K ↥(P.mulVecLin.prod M.mulVecLin).range := by
        rw [hrange, LinearEquiv.finrank_map_eq]
    _ = P.rank + Module.finrank K ↥(Submodule.map M.mulVecLin P.mulVecLin.ker) := by
        simpa [Matrix.rank] using Q1Paper.finrank_range_prod P.mulVecLin M.mulVecLin

/-- `rank P + rank (M N)` for `N` a basis matrix of `ker P`, general indices. -/
theorem rank_vstack_add_rank_mul' {m n p k : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype k]
    (P : Matrix m n K) (M : Matrix p n K) (N : Matrix n k K)
    (hN : ∀ v : n → K, P.mulVec v = 0 ↔ ∃ w : k → K, N.mulVec w = v) :
    (Matrix.fromRows P M).rank = P.rank + (M * N).rank := by
  rw [rank_fromRows_add_map]
  congr 1
  have hker : N.mulVecLin.range = P.mulVecLin.ker := by
    ext v
    simp only [LinearMap.mem_range, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact (hN v).symm
  have hrange : (M * N).mulVecLin.range = Submodule.map M.mulVecLin P.mulVecLin.ker := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp, hker]
  have hrank : (M * N).rank = Module.finrank K ↥((M * N).mulVecLin.range) := rfl
  rw [hrank, hrange]

/-- `rank (fromRows X P) = rank P + rank (X N)`, the split used for (5b). -/
theorem rank_fromRows_eq_rank_add_mul {m n p k : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype k]
    (P : Matrix p n K) (X : Matrix m n K) (N : Matrix n k K)
    (hN : ∀ v : n → K, P.mulVec v = 0 ↔ ∃ w : k → K, N.mulVec w = v) :
    (Matrix.fromRows X P).rank = P.rank + (X * N).rank := by
  rw [rank_fromRows_comm (A := X) (B := P)]
  exact rank_vstack_add_rank_mul' P X N hN

/-! ### The kernel of the stacked matrix, compressed by `N` -/

theorem ker_fromRows_eq_map {m p n k : Type*}
    [Fintype m] [Fintype p] [Fintype n] [Fintype k]
    (L : Matrix m n K) (P : Matrix p n K) (N : Matrix n k K)
    (hN : N.mulVecLin.range = P.mulVecLin.ker) :
    (Matrix.fromRows L P).mulVecLin.ker =
      Submodule.map N.mulVecLin ((L * N).mulVecLin.ker) := by
  ext v
  constructor
  · intro hv
    have hv' : (Matrix.fromRows L P).mulVec v = 0 := hv
    have hL : L.mulVec v = 0 := by
      funext i
      have := congrFun hv' (Sum.inl i)
      simpa [Matrix.fromRows_mulVec] using this
    have hP : P.mulVec v = 0 := by
      funext i
      have := congrFun hv' (Sum.inr i)
      simpa [Matrix.fromRows_mulVec] using this
    have hPker : v ∈ P.mulVecLin.ker := hP
    have hrange : v ∈ N.mulVecLin.range := by
      rw [hN]
      exact hPker
    obtain ⟨w, hw⟩ := hrange
    have hw' : N.mulVec w = v := hw
    refine Submodule.mem_map.mpr ⟨w, ?_, ?_⟩
    · show (L * N).mulVec w = 0
      have hmul : (L * N).mulVec w = L.mulVec (N.mulVec w) := by
        have h := congrArg (fun g : (k → K) →ₗ[K] (m → K) => g w)
          (Matrix.mulVecLin_mul (M := L) (N := N))
        simpa [Matrix.mulVecLin_apply] using h
      rw [hmul, hw', hL]
    · show N.mulVecLin w = v
      simpa [Matrix.mulVecLin_apply] using hw'
  · intro hv
    obtain ⟨w, hwker, hwv⟩ := Submodule.mem_map.mp hv
    have hwv' : N.mulVec w = v := by
      simpa [Matrix.mulVecLin_apply] using hwv
    have hLN : (L * N).mulVec w = 0 := hwker
    have hmul : (L * N).mulVec w = L.mulVec (N.mulVec w) := by
      have h := congrArg (fun g : (k → K) →ₗ[K] (m → K) => g w)
        (Matrix.mulVecLin_mul (M := L) (N := N))
      simpa [Matrix.mulVecLin_apply] using h
    have hL : L.mulVec v = 0 := by
      rw [← hwv', ← hmul]
      exact hLN
    have hP : P.mulVec v = 0 := by
      have hmem : N.mulVec w ∈ P.mulVecLin.ker := by
        rw [← hN]
        exact ⟨w, rfl⟩
      rw [← hwv']
      exact hmem
    show (Matrix.fromRows L P).mulVec v = 0
    rw [Matrix.fromRows_mulVec]
    funext i
    cases i with
    | inl i => simpa using congrFun hL i
    | inr i => simpa using congrFun hP i

/-- Composing `Submodule.map` for the two compressed factors. -/
theorem map_ker_eq {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (LA : Matrix m n K) (N : Matrix n k K) (S : Submodule K (k → K)) :
    Submodule.map LA.mulVecLin (Submodule.map N.mulVecLin S) =
      Submodule.map (LA * N).mulVecLin S := by
  rw [← Submodule.map_comp (f := N.mulVecLin) (g := LA.mulVecLin)]
  rw [Matrix.mulVecLin_mul]

/-! ### The interface theorems -/

/-- **(5a), matrix level.** -/
theorem rawAlgebraic_iff_compressed {p q n k : Type*}
    [Fintype p] [Fintype q] [Fintype n] [Fintype k]
    (C CA : Matrix p n K) (L LA : Matrix q n K) (N : Matrix n k K)
    (hN : N.mulVecLin.range = (Matrix.fromRows CA C).mulVecLin.ker) :
    rawAlgebraic C CA L LA ↔ compressedAlgebraic (L * N) (LA * N) := by
  have hP : (Matrix.fromRows L (Matrix.fromRows CA C)).mulVecLin.ker =
      Submodule.map N.mulVecLin ((L * N).mulVecLin.ker) :=
    ker_fromRows_eq_map L (Matrix.fromRows CA C) N hN
  have hmap :
      Submodule.map LA.mulVecLin
          (Submodule.map N.mulVecLin ((L * N).mulVecLin.ker)) =
        Submodule.map (LA * N).mulVecLin ((L * N).mulVecLin.ker) :=
    map_ker_eq LA N _
  have hraw : rawAlgebraic C CA L LA ↔
      Module.finrank K ↥(Submodule.map LA.mulVecLin
        (Matrix.fromRows L (Matrix.fromRows CA C)).mulVecLin.ker) = 0 := by
    have hrank : (Matrix.fromRows LA (Matrix.fromRows L (Matrix.fromRows CA C))).rank =
        (Matrix.fromRows L (Matrix.fromRows CA C)).rank +
          Module.finrank K ↥(Submodule.map LA.mulVecLin
            (Matrix.fromRows L (Matrix.fromRows CA C)).mulVecLin.ker) := by
      rw [rank_fromRows_comm (A := LA) (B := Matrix.fromRows L (Matrix.fromRows CA C))]
      exact rank_fromRows_add_map (Matrix.fromRows L (Matrix.fromRows CA C)) LA
    unfold rawAlgebraic
    rw [hrank]
    constructor
    · intro h; omega
    · intro h; rw [h]; omega
  have hcomp : compressedAlgebraic (L * N) (LA * N) ↔
      Module.finrank K ↥(Submodule.map (LA * N).mulVecLin
        ((L * N).mulVecLin.ker)) = 0 := by
    have hrank : (Matrix.fromRows (LA * N) (L * N)).rank =
        (L * N).rank +
          Module.finrank K ↥(Submodule.map (LA * N).mulVecLin ((L * N).mulVecLin.ker)) := by
      rw [rank_fromRows_comm (A := LA * N) (B := L * N)]
      exact rank_fromRows_add_map (L * N) (LA * N)
    unfold compressedAlgebraic
    rw [hrank]
    constructor
    · intro h; omega
    · intro h; rw [h]; omega
  rw [hraw, hcomp, hP, hmap]

/-- **(5b), matrix level.** -/
theorem rawSpectral_iff_compressed {p q n k : Type*}
    [Fintype p] [Fintype q] [Fintype n] [Fintype k]
    (C CA : Matrix p n K) (L LA : Matrix q n K) (N : Matrix n k K)
    (hN : N.mulVecLin.range = (Matrix.fromRows CA C).mulVecLin.ker) :
    rawSpectral C CA L LA ↔ compressedSpectral (L * N) (LA * N) := by
  have hN' : ∀ v : n → K,
      (Matrix.fromRows CA C).mulVec v = 0 ↔ ∃ w : k → K, N.mulVec w = v := by
    intro v
    constructor
    · intro hv
      have hmem : v ∈ (Matrix.fromRows CA C).mulVecLin.ker := hv
      rw [← hN] at hmem
      exact hmem
    · rintro ⟨w, rfl⟩
      have hmem : N.mulVec w ∈ (Matrix.fromRows CA C).mulVecLin.ker := by
        rw [← hN]
        exact ⟨w, rfl⟩
      exact hmem
  have hsub : ∀ lam : K, (lam • L - LA) * N = lam • (L * N) - LA * N := by
    intro lam
    simp [Matrix.sub_mul, Matrix.smul_mul]
  constructor
  · intro h lam
    have h1 := h lam
    rw [rank_fromRows_eq_rank_add_mul (P := Matrix.fromRows CA C) (X := lam • L - LA) N hN'] at h1
    rw [rank_fromRows_eq_rank_add_mul (P := Matrix.fromRows CA C) (X := L) N hN'] at h1
    rw [hsub lam] at h1
    show (lam • (L * N) - LA * N).rank = (L * N).rank
    omega
  · intro h lam
    rw [rank_fromRows_eq_rank_add_mul (P := Matrix.fromRows CA C) (X := lam • L - LA) N hN']
    rw [rank_fromRows_eq_rank_add_mul (P := Matrix.fromRows CA C) (X := L) N hN']
    rw [hsub lam]
    rw [h lam]

/-- **(5a) written as a row-space inclusion of the compressed blocks.** -/
theorem rawAlgebraic_iff_rowSpace {p q n k : Type*}
    [Fintype p] [Fintype q] [Fintype n] [Fintype k]
    (C CA : Matrix p n K) (L LA : Matrix q n K) (N : Matrix n k K)
    (hN : N.mulVecLin.range = (Matrix.fromRows CA C).mulVecLin.ker) :
    rawAlgebraic C CA L LA ↔
      Q1Subspace.rowSpace (LA * N) ≤ Q1Subspace.rowSpace (L * N) := by
  rw [rawAlgebraic_iff_compressed C CA L LA N hN]
  exact Q1Subspace.rank_fromRows_eq_rank_iff (LA * N) (L * N)

/-- **The decision problem in compressed form**: `DEC` holds exactly when some
free block `R` makes the compressed pair satisfy the two compressed conditions. -/
theorem DEC_iff_compressed {p r0 n k : ℕ}
    (C : Matrix (Fin p) (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (L0 : Matrix (Fin r0) (Fin n) K) (r : ℕ) (N : Matrix (Fin n) (Fin k) K)
    (hN : N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker) :
    DEC C A L0 r ↔ ∃ R : Matrix (Fin r) (Fin n) K,
      let L := Matrix.fromRows L0 R
      compressedAlgebraic (L * N) (L * A * N) ∧
        compressedSpectral (L * N) (L * A * N) := by
  constructor
  · rintro ⟨R, h1, h2⟩
    refine ⟨R, ?_, ?_⟩
    · exact (rawAlgebraic_iff_compressed C (C * A) (Matrix.fromRows L0 R)
        (Matrix.fromRows L0 R * A) N hN).mp h1
    · exact (rawSpectral_iff_compressed C (C * A) (Matrix.fromRows L0 R)
        (Matrix.fromRows L0 R * A) N hN).mp h2
  · rintro ⟨R, h1, h2⟩
    refine ⟨R, ?_, ?_⟩
    · exact (rawAlgebraic_iff_compressed C (C * A) (Matrix.fromRows L0 R)
        (Matrix.fromRows L0 R * A) N hN).mpr h1
    · exact (rawSpectral_iff_compressed C (C * A) (Matrix.fromRows L0 R)
        (Matrix.fromRows L0 R * A) N hN).mpr h2

end Q1Paper.PaperI
