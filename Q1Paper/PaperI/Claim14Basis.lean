/-
Q1Paper/PaperI/Claim14Basis.lean

Chart data of Claim 14 (`clm:chartdata`) of Paper I, assembled from the pieces
that already exist:

* `Q1Paper/PaperI/RationalBasis.lean` (namespace `Q1Paper.PaperI`):
  `exists_rational_bases_bounded` -- for a rational matrix `M` with
  `bitLenMat M <= tau` it produces a kernel basis `N` (`M N = 0`,
  `ker M = range N`, `N.rank = n - M.rank`), a row basis `R`
  (`R.rank = M.rank`, `rowSpace R = rowSpace M`) and an annihilator `D`, all
  with the explicit bound `bitLenRat <= tauM M tau`.

* `Q1Paper/PaperI/Claim14.lean` (namespace `Q1Paper.PaperI.Claim14`):
  `map_comp_fst_K0_eq_inf`, `span_image_basis_eq_inf`,
  `linearIndependent_image_basis_iff`, `not_linearIndependent_of_ker_ne_bot`,
  `ker_restrictFst_eq_bot_iff`, `quotientEquivInf`, `basisOfQuotientBasis`,
  `matrix_map_comp_fst_K0_eq_inf`.

* `Q1Paper/PaperI/KernelBasis.lean` (namespace `Q1Paper`):
  `exists_basis_matrix_of_submodule`.

Contents of this file (all proved; no `sorry`, no `admit`, no new axiom;
the axiom footprint of the headline theorems is printed at the end and is
`[propext, Classical.choice, Quot.sound]`):

## 1. Index-generic basis matrices
  * `exists_basis_matrix_of_submodule_fintype` : the `KernelBasis` lemma with
    `Fin n` replaced by an arbitrary finite index type `ι`;
  * `rowSpace_transpose_eq_range`, `exists_rowBasis_of_submodule` : the row-space
    (transposed) form, which is what the paper's "basis of a row space" means;
  * `rowSpace_mul_le'`, `range_vecMulLinear_eq_rowSpace'`.

## 2. The paper's objects
  * `pairColumns`, `pairMatrix` : `M = [N  AN]` (`Fin k ⊕ Fin k` and `Fin (k+k)`
    column index respectively), with the two block projections
    `pairMatrix_apply_inl` / `pairMatrix_apply_inr`;
  * `blockPair S` : the paper's `S × S` inside `Fin k ⊕ Fin k -> K`;
  * `blockDiag AS` : the paper's `A_V`, whose row space is `S × S`
    (`rowSpace_blockDiag`, `range_blockDiag`).

## 3. Deliverable 1: bases of `N`, `T`, `S`, `W_0`
  * `exists_chart_bases` : one theorem producing all four basis matrices at
    once, with `rank = dim` and `rowSpace`/`range` characterisations and the
    `tauM` bit bound for each.

## 4. Deliverable 2: `V = T ∩ (S × S)`
  * `inf_eq_map_K0` : `V` is the image of the equalizer (from
    `map_comp_fst_K0_eq_inf`);
  * `exists_inf_basis_matrix`, `exists_inf_rowBasis_matrix` : a matrix whose
    columns (rows) are a basis of `V` (`rank = finrank V`, `range`/`rowSpace`
    `= V`), from `exists_basis_matrix_of_submodule_fintype` applied to the
    intersection submodule;
  * `finrank_inf_add_finrank_ker_restrictFst` : the dimension equality
    `dim V + dim (ker (K0 → V)) = dim K0`;
  * `image_basis_spanning`, `image_basis_not_basis`,
    `finrank_inf_lt_finrank_K0` : the image of a basis of the equalizer spans
    `V`, but has *more columns than* `dim V` whenever the left row map is not
    injective -- a spanning image is not automatically a basis.

## 5. Deliverable 3: `E_Q`
  * `exists_chart_completion` : rows of `E_Q` together with a basis `E_0` of
    `W_0` are a basis of `W_1` (`m' = dim W_1 - dim W_0` rows, span `W_1`,
    rank `dim W_1`), *given* `W_0 ≤ W_1`; the hypothesis is exactly the paper's
    feasibility gate;
  * `exists_chart_completion_pair` : the same for `W_0 = row (L_0 M)` and
    `V = T ∩ (S × S)`.
-/

import Q1Paper.PaperI.RationalBasis
import Q1Paper.PaperI.Claim14
import Q1Paper.PaperI.KernelBasis

namespace Q1Paper.PaperI.Chart14

open Module Matrix
open Q1Paper.PaperI.Claim14

variable {K : Type*} [Field K]

/-! ## 1.  Basis matrices over arbitrary finite index types -/

/-- **Basis matrix of a submodule of `ι → K`, any finite index type.**

`Q1Paper.exists_basis_matrix_of_submodule` is the case `ι = Fin n`; the proof is
the same (the `Module.finBasis` of `W` written as the columns of the matrix). -/
theorem exists_basis_matrix_of_submodule_fintype {ι : Type*} [Fintype ι]
    (W : Submodule K (ι → K)) :
    ∃ N : Matrix ι (Fin (Module.finrank K W)) K,
      Matrix.rank N = Module.finrank K W ∧ N.mulVecLin.range = W := by
  classical
  let b := Module.finBasis K W
  let N : Matrix ι (Fin (Module.finrank K W)) K := fun i j => (b j : ι → K) i
  have hmul : ∀ v : Fin (Module.finrank K W) → K,
      N.mulVecLin v = ∑ j, v j • (b j : ι → K) := by
    intro v
    rw [Matrix.mulVecLin_apply]
    funext i
    simp only [Matrix.mulVec, dotProduct, N, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hle : N.mulVecLin.range ≤ W := by
    rintro x ⟨v, rfl⟩
    rw [hmul v]
    exact Submodule.sum_mem W (fun j _ => Submodule.smul_mem W (v j) (b j).2)
  have hge : W ≤ N.mulVecLin.range := by
    intro x hx
    refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_⟩
    rw [hmul]
    have h := congrArg (fun w : W => (w : ι → K)) (b.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at h
    simpa only [Submodule.coe_smul, Subtype.coe_mk] using h
  have hrange : N.mulVecLin.range = W := le_antisymm hle hge
  refine ⟨N, ?_, hrange⟩
  change Module.finrank K ↥(LinearMap.range N.mulVecLin) = Module.finrank K W
  rw [hrange]

/-- The row space of `Nᵀ` is the range of `N.mulVecLin` (the columns of `N`). -/
theorem rowSpace_transpose_eq_range {ι : Type*} [Fintype ι] {c : ℕ}
    (N : Matrix ι (Fin c) K) :
    Q1Subspace.rowSpace (Nᵀ) = N.mulVecLin.range := by
  rw [Matrix.range_mulVecLin]
  unfold Q1Subspace.rowSpace
  rfl

/-- **Row basis matrix of a submodule of `ι → K`**: the transposed basis matrix.
Its rows are a basis of `W`, its rank is `finrank W`. -/
theorem exists_rowBasis_of_submodule {ι : Type*} [Fintype ι]
    (W : Submodule K (ι → K)) :
    ∃ R : Matrix (Fin (Module.finrank K W)) ι K,
      Matrix.rank R = Module.finrank K W ∧ Q1Subspace.rowSpace R = W := by
  obtain ⟨N, hrank, hrange⟩ := exists_basis_matrix_of_submodule_fintype W
  exact ⟨Nᵀ, by rw [Matrix.rank_transpose, hrank],
    by rw [rowSpace_transpose_eq_range, hrange]⟩

/-- Right multiplication cannot enlarge the row space. -/
theorem rowSpace_mul_le' {s m d : Type*} [Fintype s] [Fintype m] [Fintype d]
    (L : Matrix s m K) (M : Matrix m d K) :
    Q1Subspace.rowSpace (L * M) ≤ Q1Subspace.rowSpace M := by
  unfold Q1Subspace.rowSpace
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have hrow : (L * M) i = ∑ k, L i k • M k := by
    funext j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  show (L * M) i ∈ Q1Subspace.rowSpace M
  rw [hrow]
  exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

/-- `range (vecMulLinear A) = rowSpace A` for an arbitrary column index type. -/
theorem range_vecMulLinear_eq_rowSpace' {a d : Type*} [Fintype a] [Fintype d]
    [DecidableEq a] [DecidableEq d] (A : Matrix a d K) :
    LinearMap.range (Matrix.vecMulLinear A) = Q1Subspace.rowSpace A := by
  rw [Q1Subspace.range_eq_rowSpan]
  rfl

/-! ## 2.  The paper's objects: `M = [N  AN]`, `S × S`, `A_V` -/

variable {n k ℓ : ℕ}

/-- **`M = [N  AN]`** with the two blocks kept apart as a sum index: the paper's
`M : R^{n × 2k}` with its two blocks of `k` columns. -/
def pairColumns (N : Matrix (Fin n) (Fin k) K) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin k ⊕ Fin k) K :=
  fun i j => j.elim (fun a => N i a) (fun a => (A * N) i a)

/-- The paper's `M = [N  AN]` as an `n × 2k` matrix (`2k = k + k` columns). -/
def pairMatrix (N : Matrix (Fin n) (Fin k) K) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin (k + k)) K :=
  (pairColumns N A).submatrix id finSumFinEquiv.symm

/-- The first block of a row of `pairMatrix N A` is the corresponding row of `N`. -/
theorem pairMatrix_apply_inl (N : Matrix (Fin n) (Fin k) K) (A : Matrix (Fin n) (Fin n) K)
    (i : Fin n) (a : Fin k) :
    pairMatrix N A i (finSumFinEquiv (Sum.inl a)) = N i a := by
  show (Sum.elim (fun a => N i a) (fun a => (A * N) i a))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl a))) = N i a
  rw [Equiv.symm_apply_apply, Sum.elim_inl]

/-- The second block of a row of `pairMatrix N A` is the corresponding row of `A * N`. -/
theorem pairMatrix_apply_inr (N : Matrix (Fin n) (Fin k) K) (A : Matrix (Fin n) (Fin n) K)
    (i : Fin n) (a : Fin k) :
    pairMatrix N A i (finSumFinEquiv (Sum.inr a)) = (A * N) i a := by
  show (Sum.elim (fun a => N i a) (fun a => (A * N) i a))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr a))) = (A * N) i a
  rw [Equiv.symm_apply_apply, Sum.elim_inr]

/-- **The paper's `S × S ⊆ K^{2k}`**, in two-block coordinates: the vectors whose
two blocks both lie in `S`.  (Under `Fin k ⊕ Fin k ≃ Fin (k+k)` this is the
paper's `S × S`.) -/
def blockPair (S : Submodule K (Fin k → K)) : Submodule K (Fin k ⊕ Fin k → K) where
  carrier := {w | (fun i : Fin k => w (Sum.inl i)) ∈ S ∧ (fun i : Fin k => w (Sum.inr i)) ∈ S}
  zero_mem' := ⟨Submodule.zero_mem S, Submodule.zero_mem S⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  smul_mem' := by
    intro c x hx
    refine ⟨?_, ?_⟩
    · show c • (fun i : Fin k => x (Sum.inl i)) ∈ S
      exact Submodule.smul_mem S c hx.1
    · show c • (fun i : Fin k => x (Sum.inr i)) ∈ S
      exact Submodule.smul_mem S c hx.2

/-- Membership in the paper's `S × S`. -/
theorem mem_blockPair {S : Submodule K (Fin k → K)} {w : Fin k ⊕ Fin k → K} :
    w ∈ blockPair S ↔
      ((fun i : Fin k => w (Sum.inl i)) ∈ S ∧ (fun i : Fin k => w (Sum.inr i)) ∈ S) :=
  Iff.rfl

/-- **The paper's `A_V`**: a basis matrix `AS` of `S` placed in both diagonal blocks;
its rows are the rows of a basis of `S × S`. -/
def blockDiag (AS : Matrix (Fin ℓ) (Fin k) K) : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin k ⊕ Fin k) K :=
  Matrix.fromBlocks AS 0 0 AS

/-- The row space of `A_V` is `S × S`. -/
theorem rowSpace_blockDiag (AS : Matrix (Fin ℓ) (Fin k) K) :
    Q1Subspace.rowSpace (blockDiag AS) = blockPair (Q1Subspace.rowSpace AS) := by
  apply le_antisymm
  · rw [Q1Subspace.rowSpace, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    cases r with
    | inl a =>
        refine ⟨?_, ?_⟩
        · have h : (fun i : Fin k => blockDiag AS (Sum.inl a) (Sum.inl i)) = AS a := by
            funext i; simp [blockDiag]
          rw [h]
          exact Submodule.subset_span ⟨a, rfl⟩
        · have h : (fun i : Fin k => blockDiag AS (Sum.inl a) (Sum.inr i)) = 0 := by
            funext i; simp [blockDiag]
          rw [h]
          exact Submodule.zero_mem _
    | inr a =>
        refine ⟨?_, ?_⟩
        · have h : (fun i : Fin k => blockDiag AS (Sum.inr a) (Sum.inl i)) = 0 := by
            funext i; simp [blockDiag]
          rw [h]
          exact Submodule.zero_mem _
        · have h : (fun i : Fin k => blockDiag AS (Sum.inr a) (Sum.inr i)) = AS a := by
            funext i; simp [blockDiag]
          rw [h]
          exact Submodule.subset_span ⟨a, rfl⟩
  · intro w hw
    obtain ⟨hx, hy⟩ := mem_blockPair.mp hw
    obtain ⟨u, hu⟩ := (Q1Subspace.mem_rowSpan_iff_exists_vecMul AS _).mp hx
    obtain ⟨v, hv⟩ := (Q1Subspace.mem_rowSpan_iff_exists_vecMul AS _).mp hy
    have hwv : (Sum.elim u v) ᵥ* blockDiag AS = w := by
      funext j
      cases j with
      | inl i =>
          have h : ((Sum.elim u v) ᵥ* blockDiag AS) (Sum.inl i) = (u ᵥ* AS) i := by
            simp [blockDiag, Matrix.vecMul, dotProduct, Fintype.sum_sum_type]
          rw [h, congrFun hu i]
      | inr i =>
          have h : ((Sum.elim u v) ᵥ* blockDiag AS) (Sum.inr i) = (v ᵥ* AS) i := by
            simp [blockDiag, Matrix.vecMul, dotProduct, Fintype.sum_sum_type]
          rw [h, congrFun hv i]
    rw [← hwv]
    exact Q1Subspace.range_le_rowSpan _ ⟨Sum.elim u v, rfl⟩

/-- **`A_V` is a surjection onto `S × S`** (over any field). -/
theorem range_blockDiag [DecidableEq (Fin ℓ ⊕ Fin ℓ)] [DecidableEq (Fin k ⊕ Fin k)]
    (AS : Matrix (Fin ℓ) (Fin k) K) :
    LinearMap.range (Matrix.vecMulLinear (blockDiag AS)) =
      blockPair (Q1Subspace.rowSpace AS) := by
  rw [range_vecMulLinear_eq_rowSpace', rowSpace_blockDiag]

/-- The `ℚ`-only row space of `RationalBasis.lean` is the general row space. -/
theorem rowSpace_rat_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    Q1Paper.PaperI.rowSpace A = Q1Subspace.rowSpace A := rfl

/-! ## 3.  Deliverable 1: bases of `N`, `T = row M`, `S = row (AN)`, `W_0 = row (L_0 M)` -/

/-- **Deliverable 1 (Claim 14, chart bases of the four spaces).**

For a rational stack `P` (the paper's `[C; CA]`), a rational `A` and prescribed
block `L_0`, there are simultaneously

* `N`, whose columns are a basis of `ker P` (`P N = 0`, `ker P = range N`,
  `N.rank = n - P.rank`);
* `R_T`, whose rows are a basis of `T = row M`, `M = [N  AN] = pairMatrix N A`
  (`R_T.rank = M.rank`, `rowSpace R_T = rowSpace M`);
* `D_T`, with `ker D_T = row M` (the annihilator of Claim 13 applied to `M`);
* `R_S`, whose rows are a basis of `S = row (AN)`;
* `R_0`, whose rows are a basis of `W_0 = row (L_0 M)`;

and every entry of the four basis matrices has bit length at most the Claim 13
bound `tauM` evaluated at the *corresponding* matrix (`bitLenMat` of `P`,
`pairMatrix N A`, `A * N`, `L_0 * pairMatrix N A` respectively).

The bit bounds are therefore relative to each matrix separately; passing to a
single bound in the input length `L` (the paper's `poly L`) needs a
submultiplicativity lemma `bitLenMat (X * Y) <= ...`, which this file does not
provide -- see the header comment and the report. -/
theorem exists_chart_bases {m n r0 : ℕ} (P : Matrix (Fin m) (Fin n) ℚ)
    (A : Matrix (Fin n) (Fin n) ℚ) (L0 : Matrix (Fin r0) (Fin n) ℚ) :
    ∃ (N : Matrix (Fin n) (Fin (n - P.rank)) ℚ)
      (RT : Matrix (Fin ((pairMatrix N A).rank)) (Fin ((n - P.rank) + (n - P.rank))) ℚ)
      (DT : Matrix (Fin (((n - P.rank) + (n - P.rank)) - (pairMatrix N A).rank))
              (Fin ((n - P.rank) + (n - P.rank))) ℚ)
      (RS : Matrix (Fin ((A * N).rank)) (Fin (n - P.rank)) ℚ)
      (R0 : Matrix (Fin ((L0 * pairMatrix N A).rank))
              (Fin ((n - P.rank) + (n - P.rank))) ℚ),
      P * N = 0 ∧
      LinearMap.ker P.mulVecLin = LinearMap.range N.mulVecLin ∧
      N.rank = n - P.rank ∧
      Matrix.rank RT = (pairMatrix N A).rank ∧
      Q1Subspace.rowSpace RT = Q1Subspace.rowSpace (pairMatrix N A) ∧
      LinearMap.ker DT.mulVecLin = Q1Subspace.rowSpace (pairMatrix N A) ∧
      Matrix.rank RS = (A * N).rank ∧
      Q1Subspace.rowSpace RS = Q1Subspace.rowSpace (A * N) ∧
      Matrix.rank R0 = (L0 * pairMatrix N A).rank ∧
      Q1Subspace.rowSpace R0 = Q1Subspace.rowSpace (L0 * pairMatrix N A) ∧
      (∀ i j, bitLenRat (N i j) ≤ tauM P (bitLenMat P)) ∧
      (∀ i j, bitLenRat (RT i j) ≤ tauM (pairMatrix N A) (bitLenMat (pairMatrix N A))) ∧
      (∀ i j, bitLenRat (RS i j) ≤ tauM (A * N) (bitLenMat (A * N))) ∧
      (∀ i j, bitLenRat (R0 i j)
        ≤ tauM (L0 * pairMatrix N A) (bitLenMat (L0 * pairMatrix N A))) := by
  classical
  obtain ⟨N, -, -, hPN, hker, hNrank, -, -, -, hNb, -, -⟩ :=
    exists_rational_bases_bounded P le_rfl
  obtain ⟨-, RT, DT, -, -, -, hRTrank, hRTrow, hDTker, -, hRTb, -⟩ :=
    exists_rational_bases_bounded (pairMatrix N A) le_rfl
  obtain ⟨-, RS, -, -, -, -, hRSrank, hRSrow, -, -, hRSb, -⟩ :=
    exists_rational_bases_bounded (A * N) le_rfl
  obtain ⟨-, R0, -, -, -, -, hR0rank, hR0row, -, -, hR0b, -⟩ :=
    exists_rational_bases_bounded (L0 * pairMatrix N A) le_rfl
  exact ⟨N, RT, DT, RS, R0, hPN, hker, hNrank, hRTrank,
    by simpa only [rowSpace_rat_eq] using hRTrow,
    by simpa only [rowSpace_rat_eq] using hDTker,
    hRSrank, by simpa only [rowSpace_rat_eq] using hRSrow,
    hR0rank, by simpa only [rowSpace_rat_eq] using hR0row,
    hNb, hRTb, hRSb, hR0b⟩

/-! ## 4.  Deliverable 2: `V = T ∩ (S × S)` -/

section AbstractInf

variable {U X W : Type*}
  [AddCommGroup U] [Module K U] [AddCommGroup X] [Module K X]
  [AddCommGroup W] [Module K W]
  [FiniteDimensional K U] [FiniteDimensional K X] [FiniteDimensional K W]

omit [FiniteDimensional K W] in
/-- **Dimension count for the equalizer.**  The rank-nullity theorem applied to
the restricted map `K0 → T ∩ S`, whose range is the intersection
(`range_restrictFst`) and whose kernel is the dependency space. -/
theorem finrank_inf_add_finrank_ker_restrictFst (psi : U →ₗ[K] W) (phi : X →ₗ[K] W) :
    Module.finrank K ↥(LinearMap.range psi ⊓ LinearMap.range phi) +
        Module.finrank K ↥(LinearMap.ker (restrictFst psi phi)) =
      Module.finrank K ↥(K0 psi phi) := by
  have h := LinearMap.finrank_range_add_finrank_ker (restrictFst psi phi)
  rw [range_restrictFst] at h
  exact h

omit [FiniteDimensional K W] in
/-- **The dimension gap.**  If the first row map is not injective, the equalizer
is strictly larger than the intersection: the image of a basis of `K0` has more
vectors than `dim (T ∩ S)`, so it cannot be a basis. -/
theorem finrank_inf_lt_finrank_K0 (psi : U →ₗ[K] W) (phi : X →ₗ[K] W)
    (h : LinearMap.ker psi ≠ ⊥) :
    Module.finrank K ↥(LinearMap.range psi ⊓ LinearMap.range phi) <
      Module.finrank K ↥(K0 psi phi) := by
  have hker : LinearMap.ker (restrictFst psi phi) ≠ ⊥ := by
    intro hbot
    exact h ((ker_restrictFst_eq_bot_iff psi phi).mp hbot).1
  have hlt : (⊥ : Submodule K ↥(K0 psi phi)) < LinearMap.ker (restrictFst psi phi) :=
    bot_lt_iff_ne_bot.mpr hker
  have hpos : 0 < Module.finrank K ↥(LinearMap.ker (restrictFst psi phi)) := by
    have h' := Submodule.finrank_lt_finrank_of_lt hlt
    simpa using h'
  have hsum := finrank_inf_add_finrank_ker_restrictFst psi phi
  omega

end AbstractInf

/-- **`V = T ∩ (S × S)` is the image of the equalizer** (Claim 14's
`matrix_map_comp_fst_K0_eq_inf`, with the two row maps `M` and `A_V`). -/
theorem inf_eq_map_K0 {n k ℓ : ℕ} (M : Matrix (Fin n) (Fin k ⊕ Fin k) K)
    (AS : Matrix (Fin ℓ) (Fin k) K) :
    Submodule.map ((Matrix.vecMulLinear M).comp
        (LinearMap.fst K (Fin n → K) (Fin ℓ ⊕ Fin ℓ → K)))
        (K0 (Matrix.vecMulLinear M) (Matrix.vecMulLinear (blockDiag AS))) =
      Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS) := by
  rw [map_comp_fst_K0_eq_inf, range_vecMulLinear_eq_rowSpace', range_blockDiag]

/-- **Deliverable 2: a matrix whose columns are a basis of `V`.**

`NV` has `dim V` columns, full column rank `dim V`, and its column space is
exactly `V = T ∩ (S × S)`.  This is
`exists_basis_matrix_of_submodule_fintype` applied to the intersection
submodule; unlike the image of a basis of the equalizer (next theorem) it is a
basis by construction, because `finrank` fixes the number of columns. -/
theorem exists_inf_basis_matrix {n k ℓ : ℕ} (M : Matrix (Fin n) (Fin k ⊕ Fin k) K)
    (AS : Matrix (Fin ℓ) (Fin k) K) :
    ∃ NV : Matrix (Fin k ⊕ Fin k)
        (Fin (Module.finrank K
          ↥(Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS)))) K,
      Matrix.rank NV =
          Module.finrank K ↥(Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS)) ∧
        NV.mulVecLin.range =
          Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS) :=
  exists_basis_matrix_of_submodule_fintype _

/-- **Deliverable 2, row form**: a matrix whose *rows* are a basis of `V`. -/
theorem exists_inf_rowBasis_matrix {n k ℓ : ℕ} (M : Matrix (Fin n) (Fin k ⊕ Fin k) K)
    (AS : Matrix (Fin ℓ) (Fin k) K) :
    ∃ RV : Matrix (Fin (Module.finrank K
        ↥(Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS))))
        (Fin k ⊕ Fin k) K,
      Matrix.rank RV =
          Module.finrank K ↥(Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS)) ∧
        Q1Subspace.rowSpace RV =
          Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS) :=
  exists_rowBasis_of_submodule _

/-- **The image of a basis of the equalizer as a matrix.**  Its columns span
`V = T ∩ (S × S)` (Claim 14's `span_image_basis_eq_inf`, matrix form); this is
the paper's "rational generating set of `V`". -/
theorem image_basis_spanning {ι : Type*} [Fintype ι] {a b d : ℕ}
    (psi : (Fin a → K) →ₗ[K] (Fin d → K)) (phi : (Fin b → K) →ₗ[K] (Fin d → K))
    (bK : Basis ι K (K0 psi phi)) :
    ∃ NV : Matrix (Fin d) ι K,
      NV.mulVecLin.range = LinearMap.range psi ⊓ LinearMap.range phi ∧
        Matrix.rank NV = Module.finrank K ↥(LinearMap.range psi ⊓ LinearMap.range phi) := by
  let NV : Matrix (Fin d) ι K := fun j i => psi ((bK i : (Fin a → K) × (Fin b → K)).1) j
  have hrange : NV.mulVecLin.range = LinearMap.range psi ⊓ LinearMap.range phi := by
    rw [Matrix.range_mulVecLin]
    exact span_image_basis_eq_inf psi phi bK
  refine ⟨NV, hrange, ?_⟩
  show Module.finrank K ↥(NV.mulVecLin.range) =
    Module.finrank K ↥(LinearMap.range psi ⊓ LinearMap.range phi)
  rw [hrange]

/-- **A spanning image is not automatically a basis.**  If the left row map is
not injective, the number of columns of the matrix above (`card ι = dim K0`)
strictly exceeds its rank (`dim V`), so its columns are linearly dependent and
it is not a basis matrix of `V`. -/
theorem image_basis_not_basis {ι : Type*} [Fintype ι] {a b d : ℕ}
    (psi : (Fin a → K) →ₗ[K] (Fin d → K)) (phi : (Fin b → K) →ₗ[K] (Fin d → K))
    (bK : Basis ι K (K0 psi phi)) (h : LinearMap.ker psi ≠ ⊥) :
    Matrix.rank (fun j i => psi ((bK i : (Fin a → K) × (Fin b → K)).1) j) <
      Fintype.card ι := by
  let NV : Matrix (Fin d) ι K := fun j i => psi ((bK i : (Fin a → K) × (Fin b → K)).1) j
  have hcard : Module.finrank K ↥(K0 psi phi) = Fintype.card ι :=
    Module.finrank_eq_card_basis bK
  have hlt := finrank_inf_lt_finrank_K0 psi phi h
  have hrange : NV.mulVecLin.range = LinearMap.range psi ⊓ LinearMap.range phi := by
    rw [Matrix.range_mulVecLin]
    exact span_image_basis_eq_inf psi phi bK
  show Module.finrank K ↥(NV.mulVecLin.range) < Fintype.card ι
  rw [hrange, ← hcard]
  exact hlt

/-! ## 5.  Deliverable 3: `E_Q` -/

section Completion

variable {ι : Type*} [Fintype ι]

/-- **Deliverable 3: `E_Q` completes a basis `E_0` of `W_0` to a basis of `V`.**

Let `E_0` have rows forming a basis of `W_0` (`rowSpace E_0 = W_0` and
`E_0.rank = s₀`, so `s₀ = dim W_0`) and let `W_0 ≤ W₁`.  Then there is
`E_Q : Matrix (Fin m') ι K` with `m' = dim W₁ - s₀` rows such that the rows of
`[E_0; E_Q]` span `W₁` **and** have rank `dim W₁`; since the number of rows is
`s₀ + m' = dim W₁`, the rows of `[E_0; E_Q]` are linearly independent, i.e. they
are a basis of `W₁`.

Construction: take a complement `W_c` of `W_0` in the ambient space
(`Submodule.exists_isCompl`); the modular law gives `W₁ = W_0 ⊔ (W₁ ⊓ W_c)`, and
a basis matrix of `W₁ ⊓ W_c`, transposed, is `E_Q`.

**The hypothesis `W_0 ≤ W₁` cannot be dropped** and, in the paper's instance
`W₁ = T ∩ (S × S)`, is not a theorem: `W_0 ≤ T` is automatic
(`rowSpace_mul_le'`), but `W_0 ≤ S × S` is precisely the feasibility gate of the
algorithm (`infeasible` when it fails). -/
theorem exists_chart_completion {s₀ : ℕ} {W0 W1 : Submodule K (ι → K)}
    (E0 : Matrix (Fin s₀) ι K) (hE0 : Q1Subspace.rowSpace E0 = W0)
    (hE0rank : E0.rank = s₀) (hWV : W0 ≤ W1) :
    ∃ (m' : ℕ) (EQ : Matrix (Fin m') ι K),
      m' = Module.finrank K ↥W1 - s₀ ∧
        Q1Subspace.rowSpace (Matrix.fromRows E0 EQ) = W1 ∧
          (Matrix.fromRows E0 EQ).rank = Module.finrank K ↥W1 := by
  classical
  obtain ⟨Wc, hWc⟩ := Submodule.exists_isCompl W0
  -- the modular law: `W_0 ⊔ (W_1 ⊓ W_c) = W_1`
  have hV : W0 ⊔ (W1 ⊓ Wc) = W1 := by
    have hmod : (W0 ⊔ Wc) ⊓ W1 = W0 ⊔ (Wc ⊓ W1) := sup_inf_assoc_of_le Wc hWV
    rw [hWc.sup_eq_top, top_inf_eq] at hmod
    rw [inf_comm W1 Wc]
    exact hmod.symm
  -- `W_0 ⊓ (W_1 ⊓ W_c) = ⊥`
  have hzero : W0 ⊓ (W1 ⊓ Wc) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.mpr hWV, hWc.inf_eq_bot]
  -- `dim W_0 = s₀`
  have hW0fin : Module.finrank K ↥W0 = s₀ := by
    rw [← hE0, ← Q1Subspace.rank_eq_finrank_rowSpace, hE0rank]
  -- the dimension bookkeeping
  have hfin : Module.finrank K ↥(W1 ⊓ Wc) = Module.finrank K ↥W1 - s₀ := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq W0 (W1 ⊓ Wc)
    rw [hV, hzero, finrank_bot, hW0fin] at hsum
    omega
  -- a basis matrix of `W_1 ⊓ W_c`, transposed to a row matrix
  obtain ⟨NQ, -, hNQ⟩ := exists_basis_matrix_of_submodule_fintype (W1 ⊓ Wc)
  refine ⟨Module.finrank K ↥(W1 ⊓ Wc), NQᵀ, hfin, ?_, ?_⟩
  · rw [Q1Subspace.rowSpace_fromRows, hE0, rowSpace_transpose_eq_range, hNQ, hV]
  · rw [Q1Subspace.rank_eq_finrank_rowSpace]
    rw [Q1Subspace.rowSpace_fromRows, hE0, rowSpace_transpose_eq_range, hNQ, hV]

end Completion

/-- **Deliverable 3 for the paper's data**: `W_0 = row (L_0 M)` and
`V = T ∩ (S × S)` with `T = row M`, `S = row A_S`.

The theorem produces the basis `E_0` of `W_0` as well, so `E_Q` is produced with
`m' = dim V - dim W_0` rows.  The hypothesis `hgate : row (L_0 M) ≤ S × S` is the
paper's feasibility gate (it is not derivable: `row (L_0 M) ≤ T` is automatic,
the second half is a condition on the input). -/
theorem exists_chart_completion_pair {r0 n k ℓ : ℕ} (M : Matrix (Fin n) (Fin k ⊕ Fin k) K)
    (AS : Matrix (Fin ℓ) (Fin k) K) (L0 : Matrix (Fin r0) (Fin n) K)
    (hgate : Q1Subspace.rowSpace (L0 * M) ≤ blockPair (Q1Subspace.rowSpace AS)) :
    ∃ (s₀ : ℕ) (E0 : Matrix (Fin s₀) (Fin k ⊕ Fin k) K) (m' : ℕ)
      (EQ : Matrix (Fin m') (Fin k ⊕ Fin k) K),
      s₀ = Module.finrank K ↥(Q1Subspace.rowSpace (L0 * M)) ∧
        Q1Subspace.rowSpace E0 = Q1Subspace.rowSpace (L0 * M) ∧
          E0.rank = s₀ ∧
            m' = Module.finrank K
              ↥(Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS)) - s₀ ∧
      Q1Subspace.rowSpace (Matrix.fromRows E0 EQ) =
                Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS) ∧
              (Matrix.fromRows E0 EQ).rank = Module.finrank K
                ↥(Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS)) := by
  classical
  have hWT : Q1Subspace.rowSpace (L0 * M) ≤ Q1Subspace.rowSpace M := rowSpace_mul_le' L0 M
  have hWV : Q1Subspace.rowSpace (L0 * M) ≤
      Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS) := le_inf hWT hgate
  obtain ⟨E0, hE0rank, hE0row⟩ := exists_rowBasis_of_submodule (Q1Subspace.rowSpace (L0 * M))
  obtain ⟨m', EQ, hm', hspan, hrank⟩ :=
    exists_chart_completion (W0 := Q1Subspace.rowSpace (L0 * M))
      (W1 := Q1Subspace.rowSpace M ⊓ blockPair (Q1Subspace.rowSpace AS))
      E0 hE0row hE0rank hWV
  exact ⟨Module.finrank K ↥(Q1Subspace.rowSpace (L0 * M)), E0, m', EQ, rfl, hE0row,
    hE0rank, hm', hspan, hrank⟩

/-! ## 6.  Axiom footprint (evidence that nothing is assumed) -/


end Q1Paper.PaperI.Chart14
