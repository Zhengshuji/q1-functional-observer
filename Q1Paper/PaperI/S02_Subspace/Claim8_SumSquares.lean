
import Q1Paper.PaperI.S03_Certificate.MinorFamilyBridge
import Q1Paper.PaperI.S03_Certificate.MinorRank
import Q1Paper.PaperI.S03_Certificate.BasisExtraction

/-!
Q1Paper/PaperI/S02_Subspace/Claim8_SumSquares.lean

**The algebraic core of Claim 8's disjunction, with no spectral theorem.**

For `M : Matrix (Fin m) (Fin n) ℝ` let `Γ := M * Mᵀ` be the Gram matrix of the rows of `M`,
and let `elemSymm M j` be the `j`-th elementary symmetric function of `Γ`, i.e. the sum of its
principal `j × j` minors:

  `elemSymm M j = ∑_{|S| = j} det (Γ_{S,S})`,   `Γ_{S,S} = M_S * M_Sᵀ`.

Main theorem (`elemSymm_pos_iff_rank_ge`):  `0 < elemSymm M j ↔ j ≤ M.rank`.

Route (Cauchy–Binet only — no eigenvalues, no spectral theorem):

1. Cauchy–Binet in the project's spelling
   (`Matrix.det_mul_transpose_eq_sum_det_submatrix`, `PaperI/CauchyBinet.lean`) gives

     `det (M_S M_Sᵀ) = ∑_{|T| = j} (det M_{S,T})²`     (`gramBlock_eq_sum_sq`),

   a sum of squares over `ℝ`.  Hence `0 ≤ det (M_S M_Sᵀ)` (`gramBlock_nonneg`) and
   `det (M_S M_Sᵀ) ≠ 0 ↔ ∃ T, det M_{S,T} ≠ 0` (`gramBlock_ne_zero_iff`).
2. Since each principal minor is `≥ 0`, `elemSymm M j > 0` iff one of them is nonzero
   (`elemSymm_pos_iff`, via `sum_pos_iff_exists_pos`).
3. `det M_{S,T} ≠ 0 → j ≤ M.rank` is `rank_le_of_det_maximalMinor_ne_zero`
   (`PaperI/MinorRank.lean`); this gives `→`.
4. For `←` extract `j` independent rows of `M` (`exists_injective_linearIndependent`,
   `PaperI/BasisExtraction.lean`), then `j` independent columns of the resulting
   full-row-rank `j × n` block (`exists_invertible_cols`); the injective-indexed minor so
   obtained is moved to the increasing-enumeration-indexed one via the sign bridge
   (`det_submatrix_injective_eq_signed`, the real-valued analogue of
   `maximalMinor_injective_eq_signed_subset` in `PaperI/MinorFamilyBridge.lean`).

Index convention.  A `j`-element set of rows is an element of `Set.powersetCard (Fin m) j`
(Mathlib's subtype `{S : Finset (Fin m) // S.card = j}` — the only form in which the
cardinality proof travels with the set, so that `S.orderEmbOfFin ⋯` can be written).  The
project's `rowEmb`/`colEmb` are exactly `S.orderEmbOfFin ⋯`.

No `sorry`, no `admit`, no new axioms.  Check with
  lake env lean Q1Paper/PaperI/Claim8_SumSquares.lean
-/


open Matrix
open Q1Paper.PaperI

namespace Q1Paper.PaperI.Claim8_SumSquares

variable {m n : ℕ}

/-! ## 1.  Principal Gram blocks of a set of rows -/

/-- The rows of `M` selected by the `j`-element set `S`, as a `j × n` matrix
(this is `M_S` for `S` the row set). -/
noncomputable def rowBlock (M : Matrix (Fin m) (Fin n) ℝ) {j : ℕ}
    (S : Set.powersetCard (Fin m) j) : Matrix (Fin j) (Fin n) ℝ :=
  M.submatrix (rowEmb S) id

/-- The principal `j × j` minor `Γ_{S,S} = det (M_S M_Sᵀ)` of the Gram matrix `Γ = M * Mᵀ`. -/
noncomputable def gramBlock (M : Matrix (Fin m) (Fin n) ℝ) {j : ℕ}
    (S : Set.powersetCard (Fin m) j) : ℝ :=
  (rowBlock M S * (rowBlock M S)ᵀ).det

/-- The `j`-th elementary symmetric function of `Γ = M * Mᵀ`: the sum of its principal
`j × j` minors, i.e. the sum of `det Γ_{S,S}` over the `j`-element sets `S` of rows. -/
noncomputable def elemSymm (M : Matrix (Fin m) (Fin n) ℝ) (j : ℕ) : ℝ :=
  ∑ S : Set.powersetCard (Fin m) j, gramBlock M S

/-! ## 2.  Cauchy–Binet: a principal Gram minor is a sum of squares of minors -/

/-- **Cauchy–Binet, squared form.**  For any `j × n` matrix `A`, `det (A Aᵀ)` is the sum over
the `j`-element column sets `T` of `(det A_{·,T})²`. -/
theorem det_mul_transpose_self_eq_sum_sq {j : ℕ} (A : Matrix (Fin j) (Fin n) ℝ) :
    (A * Aᵀ).det = ∑ T : Set.powersetCard (Fin n) j, (A.submatrix id (colEmb T)).det ^ 2 := by
  rw [Matrix.det_mul_transpose_eq_sum_det_submatrix A A]
  exact Finset.sum_congr rfl (fun T _ => by simp only [colEmb, pow_two])

/-- **`det Γ_{S,S} = ∑_{|T| = j} (det M_{S,T})²`.**  This is the Cauchy–Binet identity
restricted to the rows of `S` and read through the Gram matrix. -/
theorem gramBlock_eq_sum_sq {j : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (S : Set.powersetCard (Fin m) j) :
    gramBlock M S = ∑ T : Set.powersetCard (Fin n) j, (M.submatrix (rowEmb S) (colEmb T)).det ^ 2 := by
  rw [gramBlock, det_mul_transpose_self_eq_sum_sq]
  exact Finset.sum_congr rfl (fun T _ => by
    rw [show (rowBlock M S).submatrix id (colEmb T) = M.submatrix (rowEmb S) (colEmb T) by
      rw [rowBlock, Matrix.submatrix_submatrix]
      rfl])

/-- Every principal Gram minor is nonnegative (it is a sum of squares). -/
theorem gramBlock_nonneg {j : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (S : Set.powersetCard (Fin m) j) : 0 ≤ gramBlock M S := by
  rw [gramBlock_eq_sum_sq]
  exact Finset.sum_nonneg (fun T _ => sq_nonneg _)

/-- **A single nonzero minor makes the principal Gram minor nonzero.** -/
theorem gramBlock_ne_zero_of_det_ne_zero {j : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (S : Set.powersetCard (Fin m) j) (T : Set.powersetCard (Fin n) j)
    (h : (M.submatrix (rowEmb S) (colEmb T)).det ≠ 0) : gramBlock M S ≠ 0 := by
  intro h0
  have hsum : ∑ T' : Set.powersetCard (Fin n) j,
      (M.submatrix (rowEmb S) (colEmb T')).det ^ 2 = 0 := by
    rw [← gramBlock_eq_sum_sq]
    exact h0
  have hpos : 0 < (M.submatrix (rowEmb S) (colEmb T)).det ^ 2 := pow_two_pos_of_ne_zero h
  have hle : (M.submatrix (rowEmb S) (colEmb T)).det ^ 2 ≤ 0 := by
    rw [← hsum]
    exact Finset.single_le_sum
      (f := fun T' : Set.powersetCard (Fin n) j =>
        (M.submatrix (rowEmb S) (colEmb T')).det ^ 2)
      (fun T' _ => sq_nonneg _) (Finset.mem_univ T)
  linarith

/-- **`det Γ_{S,S} ≠ 0` iff some maximal minor on the rows `S` is nonzero.** -/
theorem exists_det_ne_zero_of_gramBlock_ne_zero {j : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (S : Set.powersetCard (Fin m) j) (h : gramBlock M S ≠ 0) :
    ∃ T : Set.powersetCard (Fin n) j, (M.submatrix (rowEmb S) (colEmb T)).det ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (by
    rw [gramBlock_eq_sum_sq]
    exact Finset.sum_eq_zero (fun T _ => by rw [hc T]; simp))

/-- **`det Γ_{S,S} ≠ 0` iff some maximal minor on the rows `S` is nonzero** (both directions). -/
theorem gramBlock_ne_zero_iff {j : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (S : Set.powersetCard (Fin m) j) :
    gramBlock M S ≠ 0 ↔
      ∃ T : Set.powersetCard (Fin n) j, (M.submatrix (rowEmb S) (colEmb T)).det ≠ 0 :=
  ⟨exists_det_ne_zero_of_gramBlock_ne_zero M S,
   fun ⟨T, hT⟩ => gramBlock_ne_zero_of_det_ne_zero M S T hT⟩

/-- A nonzero principal Gram minor forces `j ≤ M.rank` (the easy direction of the main
theorem, via `rank_le_of_det_maximalMinor_ne_zero`). -/
theorem le_rank_of_gramBlock_ne_zero {j : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (S : Set.powersetCard (Fin m) j) (h : gramBlock M S ≠ 0) : j ≤ M.rank := by
  obtain ⟨T, hT⟩ := exists_det_ne_zero_of_gramBlock_ne_zero M S h
  exact rank_le_of_det_maximalMinor_ne_zero M (rowEmb S) (colEmb T) hT

/-! ## 3.  Positivity of a sum of nonnegative terms -/

/-- A sum of nonnegative reals is positive iff one summand is. -/
theorem sum_pos_iff_exists_pos {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    0 < ∑ i, f i ↔ ∃ i, 0 < f i := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hzero : ∑ i, f i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (hc i) (hf i))
    rw [hzero] at h
    exact lt_irrefl 0 h
  · rintro ⟨i, hi⟩
    exact Finset.sum_pos' (s := Finset.univ) (fun j _ => hf j) ⟨i, Finset.mem_univ i, hi⟩

/-- `elemSymm` is nonnegative (sum of nonnegative principal Gram minors). -/
theorem elemSymm_nonneg (M : Matrix (Fin m) (Fin n) ℝ) (j : ℕ) : 0 ≤ elemSymm M j := by
  rw [elemSymm]
  exact Finset.sum_nonneg (fun S _ => gramBlock_nonneg M S)

/-- **Step 2 of the route.**  `elemSymm M j > 0` iff one principal Gram minor is nonzero. -/
theorem elemSymm_pos_iff (M : Matrix (Fin m) (Fin n) ℝ) (j : ℕ) :
    0 < elemSymm M j ↔ ∃ S : Set.powersetCard (Fin m) j, gramBlock M S ≠ 0 := by
  rw [elemSymm]
  constructor
  · intro h
    obtain ⟨S, hS⟩ :=
      (sum_pos_iff_exists_pos (fun S : Set.powersetCard (Fin m) j => gramBlock M S)
        (fun S => gramBlock_nonneg M S)).mp h
    exact ⟨S, ne_of_gt hS⟩
  · rintro ⟨S, hS⟩
    exact (sum_pos_iff_exists_pos (fun S : Set.powersetCard (Fin m) j => gramBlock M S)
      (fun S => gramBlock_nonneg M S)).mpr
      ⟨S, lt_of_le_of_ne (gramBlock_nonneg M S) (Ne.symm hS)⟩

/-- `elemSymm M j > 0` iff some maximal minor of `M` on `j` rows is nonzero. -/
theorem elemSymm_pos_iff_exists_det (M : Matrix (Fin m) (Fin n) ℝ) (j : ℕ) :
    0 < elemSymm M j ↔ ∃ (S : Set.powersetCard (Fin m) j) (T : Set.powersetCard (Fin n) j),
      (M.submatrix (rowEmb S) (colEmb T)).det ≠ 0 := by
  rw [elemSymm_pos_iff]
  exact ⟨fun ⟨S, hS⟩ => by
            obtain ⟨T, hT⟩ := exists_det_ne_zero_of_gramBlock_ne_zero M S hS
            exact ⟨S, T, hT⟩,
         fun ⟨S, T, hT⟩ => ⟨S, gramBlock_ne_zero_of_det_ne_zero M S T hT⟩⟩

/-! ## 4.  Sign bridge: injective-indexed minor → increasing-indexed minor -/

/-- **Real-valued analogue of `maximalMinor_injective_eq_signed_subset`.**  The minor indexed
by two injections equals the product of the two reordering signs times the minor indexed by
the increasing enumerations of their images (which are `Set.powersetCard` elements). -/
theorem det_submatrix_injective_eq_signed {q ℓ j : ℕ} (M : Matrix (Fin q) (Fin ℓ) ℝ)
    (ρ : Fin j → Fin q) (hρ : Function.Injective ρ)
    (κ : Fin j → Fin ℓ) (hκ : Function.Injective κ) :
    (M.submatrix ρ κ).det =
      (Equiv.Perm.sign (permOfImage ρ hρ) : ℝ) * (Equiv.Perm.sign (permOfImage κ hκ) : ℝ) *
        (M.submatrix (rowEmb (imageFin ρ hρ)) (colEmb (imageFin κ hκ))).det := by
  have hcomp : M.submatrix ρ κ =
      (M.submatrix (rowEmb (imageFin ρ hρ)) (colEmb (imageFin κ hκ))).submatrix
        (permOfImage ρ hρ) (permOfImage κ hκ) := by
    ext i k
    simp only [Matrix.submatrix_apply]
    rw [rowEmb_imageFin, colEmb_imageFin, embOfFinset_permOfImage, embOfFinset_permOfImage]
  rw [hcomp, det_submatrix_perm]

/-! ## 5.  The hard direction: `j ≤ rank M` gives a nonzero principal Gram minor -/

/-- **`j ≤ rank M` produces a `j`-element row set with nonzero principal Gram minor.**

Extraction: `j` independent rows → a full-row-rank `j × n` block → a nonzero `j × j` minor of
it (with injectively indexed rows/columns) → the sign bridge turns it into one indexed by the
increasing enumerations of the two images → Cauchy–Binet upgrades it to `det Γ_{S,S} ≠ 0`. -/
theorem exists_gramBlock_ne_zero_of_le_rank {j : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hj : j ≤ M.rank) : ∃ S : Set.powersetCard (Fin m) j, gramBlock M S ≠ 0 := by
  classical
  -- `rank M` is the dimension of the row span
  have hrow : Module.finrank ℝ (Submodule.span ℝ (Set.range M.row)) = M.rank := by
    rw [← Matrix.rank_eq_finrank_span_row]
  -- `rank M` linearly independent rows
  obtain ⟨ρ₀, hρ₀inj, hρ₀LI⟩ := exists_injective_linearIndependent (v := M.row) hrow
  -- keep the first `j` of them
  let ρ : Fin j → Fin m := ρ₀ ∘ Fin.castLE hj
  have hρinj : Function.Injective ρ := hρ₀inj.comp (Fin.castLE_injective hj)
  have hρLI : LinearIndependent ℝ (M.row ∘ ρ) := by
    have h := hρ₀LI.comp (Fin.castLE hj) (Fin.castLE_injective hj)
    simpa [ρ, Function.comp_assoc] using h
  -- the selected block has full row rank
  let W : Matrix (Fin j) (Fin n) ℝ := M.submatrix ρ id
  have hWrow : W.row = M.row ∘ ρ := by
    funext i
    rfl
  have hWrank : W.rank = j := by
    rw [Matrix.rank_eq_finrank_span_row, hWrow, finrank_span_eq_card hρLI, Fintype.card_fin]
  -- hence it has an invertible column submatrix
  obtain ⟨κ, hκinj, hκdet⟩ := exists_invertible_cols W hWrank
  have hMdet : (M.submatrix ρ κ).det ≠ 0 := by
    have hEq : W.submatrix id κ = M.submatrix ρ κ := by
      ext i k
      rfl
    rwa [hEq] at hκdet
  -- move to the increasing enumeration of the images
  refine ⟨imageFin ρ hρinj,
    gramBlock_ne_zero_of_det_ne_zero M (imageFin ρ hρinj) (imageFin κ hκinj) ?_⟩
  intro h0
  apply hMdet
  rw [det_submatrix_injective_eq_signed M ρ hρinj κ hκinj, h0, mul_zero]

/-! ## 6.  Main theorem -/

/-- **Claim 8's algebraic fact.**  For `M : Matrix (Fin m) (Fin n) ℝ` and any `j`, the `j`-th
elementary symmetric function of the Gram matrix `M * Mᵀ` is positive iff `j ≤ rank M`.

No spectral theorem is used: the proof is Cauchy–Binet plus `rank = size of the largest
nonzero minor`. -/
theorem elemSymm_pos_iff_rank_ge (M : Matrix (Fin m) (Fin n) ℝ) (j : ℕ) :
    0 < elemSymm M j ↔ j ≤ M.rank := by
  rw [elemSymm_pos_iff]
  exact ⟨fun ⟨S, hS⟩ => le_rank_of_gramBlock_ne_zero M S hS,
         fun h => exists_gramBlock_ne_zero_of_le_rank M h⟩

/-- Corollary: `elemSymm M j = 0` iff `rank M < j`. -/
theorem elemSymm_eq_zero_iff_rank_lt (M : Matrix (Fin m) (Fin n) ℝ) (j : ℕ) :
    elemSymm M j = 0 ↔ M.rank < j := by
  constructor
  · intro h0
    by_contra hlt
    push_neg at hlt
    have hpos : 0 < elemSymm M j := (elemSymm_pos_iff_rank_ge M j).mpr hlt
    rw [h0] at hpos
    exact lt_irrefl 0 hpos
  · intro hlt
    have hle : elemSymm M j ≤ 0 := by
      by_contra hc
      push_neg at hc
      exact absurd ((elemSymm_pos_iff_rank_ge M j).mp hc) (by omega)
    exact le_antisymm hle (elemSymm_nonneg M j)

/-! ## 7.  Bridge to the `Finset.powersetCard` spelling

`Set.powersetCard (Fin m) j` and `Finset.powersetCard j Finset.univ` have the same elements,
but only the subtype form carries the cardinality proof inside the term, so that the summand
`S.orderEmbOfFin ⋯` can be written at all.  The two sums below are the same sum. -/

/-- The principal Gram block of a plain finset `S` of rows when `S.card = j`, and `0`
otherwise (used only under `S ∈ Finset.powersetCard j univ`, where the first case applies). -/
noncomputable def gramBlockOf (M : Matrix (Fin m) (Fin n) ℝ) (j : ℕ) (S : Finset (Fin m)) : ℝ :=
  if h : S.card = j then gramBlock M (Set.powersetCard.ofCard h) else 0

/-- On a set of cardinality `j`, `gramBlockOf` is the principal Gram block. -/
theorem gramBlockOf_of_card {j : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) {S : Finset (Fin m)}
    (h : S.card = j) : gramBlockOf M j S = gramBlock M (Set.powersetCard.ofCard h) := by
  simp [gramBlockOf, h]

/-- The reindexing `↥(Finset.powersetCard j univ) ≃ Set.powersetCard (Fin m) j`. -/
noncomputable def powersetCardEquiv (m j : ℕ) :
    ↥((Finset.univ : Finset (Fin m)).powersetCard j) ≃ Set.powersetCard (Fin m) j where
  toFun S := ⟨S.1, (Finset.mem_powersetCard.mp S.2).2⟩
  invFun S := ⟨S.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S.1, S.2⟩⟩
  left_inv S := by
    apply Subtype.ext
    rfl
  right_inv S := by
    apply Subtype.ext
    rfl

/-- **`elemSymm` as a sum over `Finset.univ.powersetCard j`** (the `Finset.powersetCard`
spelling of the same sum of principal minors). -/
theorem elemSymm_eq_sum_powersetCard (M : Matrix (Fin m) (Fin n) ℝ) (j : ℕ) :
    elemSymm M j = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard j, gramBlockOf M j S := by
  have h1 : elemSymm M j =
      ∑ S : Set.powersetCard (Fin m) j, gramBlockOf M j (S : Finset (Fin m)) := by
    rw [elemSymm]
    exact Finset.sum_congr rfl (fun S _ => by simp [gramBlockOf])
  have h2 : (∑ S : ↥((Finset.univ : Finset (Fin m)).powersetCard j), gramBlockOf M j ↑S) =
      ∑ S : Set.powersetCard (Fin m) j, gramBlockOf M j (S : Finset (Fin m)) :=
    Fintype.sum_equiv (powersetCardEquiv m j)
      (fun S : ↥((Finset.univ : Finset (Fin m)).powersetCard j) => gramBlockOf M j ↑S)
      (fun S : Set.powersetCard (Fin m) j => gramBlockOf M j (S : Finset (Fin m)))
      (fun S => by
        show gramBlockOf M j S.1 = gramBlockOf M j S.1
        rfl)
  rw [h1, ← h2, ← Finset.sum_coe_sort (s := (Finset.univ : Finset (Fin m)).powersetCard j)
    (f := gramBlockOf M j)]

/-- **The main theorem in the `Finset.powersetCard` spelling.** -/
theorem elemSymm_pos_iff_rank_ge_finset (M : Matrix (Fin m) (Fin n) ℝ) (j : ℕ) :
    0 < (∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard j, gramBlockOf M j S) ↔
      j ≤ M.rank := by
  rw [← elemSymm_eq_sum_powersetCard]
  exact elemSymm_pos_iff_rank_ge M j

end Q1Paper.PaperI.Claim8_SumSquares

