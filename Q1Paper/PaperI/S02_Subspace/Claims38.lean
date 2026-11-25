
import Q1Paper.Q1Subspace
import Q1Paper.Q1Projection
import Q1Paper.Q1RowSpace
import Q1Paper.Monotone
import Q1Paper.MonotoneBlocks
import Q1Paper.BoundLower
import Q1Paper.FreeRows
import Q1Paper.G5GramRank
import Q1Paper.PaperI.S00_Interface.Interface

/-!
Q1Paper/PaperI/S02_Subspace/Claims38.lean

Bridge file from the existing Lean library to **Claims 3--8 of Paper I**
(`paper_I_dec.tex`, labels `lem:attainable`, `lem:sandwich`, `lem:W-conditions`,
`lem:struct`, `lem:monotone`, `lem:rankcons`).

One theorem per claim, no `sorry`.  Every theorem is proved by reusing the
project's existing lemmas; the docstring of each theorem records (a) which
paper statement it captures, (b) which existing declarations it reuses, and
(c) what part of the paper statement is *not* covered by the current API
(also listed in the report accompanying this file).

Summary of coverage:

* Claim 3 (`lem:attainable`): `κ_obs = r d₀`, `k ≤ d₀ ≤ r d₀`, and the
  definitional description of attainable pairs (the range of the pair map).
* Claim 4 (`lem:sandwich`): `W₀ ⊆ W ⊆ 𝒯`, `dim W ≤ dim W₀ + r`, and the
  onto/preimage half of the converse (`w ∈ 𝒯` is some free row's image).
* Claim 5 (`lem:W-conditions`): (5a) ⟺ `π₂(W) ≤ π₁(W)` and
  (5b) ⟺ `dim π_λ(W) = dim π₁(W)` for every `λ`, for `W = row[H  H_A]`.
* Claim 6 (`lem:struct`): `ω + 1 ≤ dim W ≤ 2ω` for a feasible `W` over an
  algebraically closed field.
* Claim 7 (`lem:monotone`): `DEC(q) ⇒ DEC(q+1)`; the proof goes through the
  invariance of the two design conditions under adjoining zero rows.
* Claim 8 (`lem:rankcons`): `∃b, Mb = c` ⟺ `rank(MMᵀ) = rank(MMᵀ + ccᵀ)`
  (together with the equivalent augmented-matrix rank test).

Notation follows the paper where the API allows it: `rowSpace M` is the span
of the rows of `M`, `pi1`/`pi2`/`piLam` are the projections `(h,g) ↦ h`,
`(h,g) ↦ g`, `(h,g) ↦ λh - g`.
-/


set_option linter.unusedSectionVars false

open Module LinearMap
open Matrix

namespace Q1Paper

variable {K : Type*} [Field K]

/-! ## Bridge lemmas

`Q1Subspace.rowSpace` (used by `Q1RowSpace`, the rank–row-space bridge) and
`Q1Subspace.rowSpan` (used by `Monotone`/`Q1Subspace`) have the same body.
The copies below restate the `rowSpan` lemmas for `rowSpace` so that the later
proofs match syntactically; they are `rfl`-level repackagings, no new
mathematics. -/

theorem rowSpace_eq_rowSpan {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n K) :
    Q1Subspace.rowSpace M = Q1Subspace.rowSpan M := rfl

theorem mem_rowSpace_iff_exists_vecMul {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n K) (w : n → K) :
    w ∈ Q1Subspace.rowSpace M ↔ ∃ u : m → K, Matrix.vecMul u M = w :=
  Q1Subspace.mem_rowSpan_iff_exists_vecMul M w

theorem rowSpace_fromRows_left {n0 m r : Type*} [Fintype n0] [Fintype m] [Fintype r]
    [DecidableEq n0]
    (L0 : Matrix n0 m K) (R : Matrix r m K) :
    Q1Subspace.rowSpace L0 ≤ Q1Subspace.rowSpace (Matrix.fromRows L0 R) :=
  Q1Subspace.rowSpan_fromRows_left L0 R

theorem rank_eq_finrank_rowSpan {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n K) :
    Matrix.rank M = finrank K ↥(Q1Subspace.rowSpan M) :=
  Q1Subspace.rank_eq_finrank_rowSpace M

/-! ## Claim 3 (`lem:attainable`)

Paper: every free row pair lies in `𝒯 = row[N  AN]`; writing the `r` free rows
in a basis of `𝒯` uses `κ_obs = r d₀` coordinates; and for `r ≥ 1`,
`k ≤ d₀ ≤ r d₀`.

Lean form (`d₀` is `finrank K (freePairSpace N (A ∘ N))`, the abstract
dimension of the range of the pair map, i.e. `rank[N  AN]`): the first
conjunct is `κ_obs = r d₀`, the second says membership in the free-pair space
is exactly being the image of a free row, the third is `k ≤ d₀` (it needs
`N` injective, i.e. `N` has full column rank), and the fourth is `d₀ ≤ r d₀`
for `r ≥ 1`.

Reuses: `kappaObs_eq_mul_freePairSpace`, `mem_freePairSpace_iff`,
`finrank_domain_le_freePairSpace` (`FreeRows.lean`, `KappaObs.lean`,
`Basic.lean`).

Gap: the identification of `freePairSpace f g` with the row space of the
concrete matrix `[N  AN]` (and hence of `d₀` with `rank[N  AN]`) is not
formalized; the paper's `k` is `finrank K E` here, which is `k` only after
that identification. -/
section Claim3

variable {E F : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- **Claim 3 (`lem:attainable`).**  For the pair map of `(f, g)` (the abstract
`(N, A ∘ N)`) with `f` injective: `κ_obs = r d₀`, feasible pairs are exactly
the pair-map images, `k ≤ d₀`, and `d₀ ≤ r d₀` for `r ≥ 1`. -/
theorem claim3_attainable (r : ℕ) (f g : E →ₗ[K] F) (hf : Function.Injective f) :
    KappaObs.kappaObs r f g = r * finrank K (freePairSpace f g) ∧
    (∀ y : F × F, y ∈ freePairSpace f g ↔ ∃ x : E, (f x, g x) = y) ∧
    finrank K E ≤ finrank K (freePairSpace f g) ∧
    (1 ≤ r → finrank K (freePairSpace f g) ≤ KappaObs.kappaObs r f g) := by
  refine ⟨kappaObs_eq_mul_freePairSpace r f g, ?_,
    finrank_domain_le_freePairSpace f g hf, ?_⟩
  · intro y
    exact mem_freePairSpace_iff f g y
  · intro hr
    rw [kappaObs_eq_mul_freePairSpace]
    exact Nat.le_mul_of_pos_left _ hr

end Claim3

/-! ## Claim 4 (`lem:sandwich`)

Paper: for `L = [L₀; R]` one has `W₀ ⊆ W ⊆ 𝒯` and `dim(W/W₀) ≤ r`;
conversely every subspace `W` with these properties is realized by a free block
with `t = dim(W/W₀)` nonzero rows and the rest zero.

Lean form (with `W₀ = row(L₀M)`, `W = row([L₀;R] M)`, `𝒯 = row M`): the four
conjuncts are the two inclusions, the dimension bound
`dim W ≤ dim W₀ + card r` (equivalent to `dim(W/W₀) ≤ r` since `W₀ ≤ W`), and
the onto statement that every `w ∈ 𝒯` is `u M` for some free row `u`.  The
auxiliary `exists_rows_mul_eq` upgrades the onto statement to a whole family
of rows: any `t` vectors of `𝒯` are simultaneously the rows of `R * M`.

Reuses: `rowSpan_fromRows_left` (`Q1Subspace.lean`, the "sandwich" lemma),
`mem_rowSpan_iff_exists_vecMul` (`Q1Subspace.lean`, realizability),
`rowSpace_fromRows` (`Q1RowSpace.lean`), `rank_eq_finrank_rowSpace`
(`Q1RowSpace.lean`), `Matrix.fromRows_mul`, `Matrix.rank_le_card_height`.

Gap: the full converse — choosing a basis of `W/W₀`, lifting it to `W`,
taking preimages in `𝒯` and padding with zero rows to exactly `r` rows — is
not formalized.  `exists_rows_mul_eq` supplies the "preimages" step for a
given family of vectors; what is missing is the quotient-basis bookkeeping
(`dim(W/W₀)` = `finrank W - finrank W₀`) and the padding of `R` to `r` rows. -/
section Claim4

/-- Right multiplication cannot enlarge the row space: every row of `X * M` is
a combination of rows of `M`. -/
theorem rowSpace_mul_le {p m n : Type*} [Fintype p] [Fintype m] [Fintype n] [DecidableEq m]
    (X : Matrix p m K) (M : Matrix m n K) :
    Q1Subspace.rowSpace (X * M) ≤ Q1Subspace.rowSpace M := by
  have h : ∀ i : p, Matrix.vecMulLinear M (X i) = (X * M) i := by
    intro i
    ext j
    rw [Matrix.vecMulLinear_apply, Matrix.vecMul_apply_eq_sum, Matrix.mul_apply]
  rw [Q1Subspace.rowSpace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  show (X * M) i ∈ Q1Subspace.rowSpace M
  rw [← h i]
  exact Q1Subspace.range_le_rowSpan M ⟨X i, rfl⟩

/-- **Preimages of a finite family of attainable row pairs.**  If every `w i`
lies in `𝒯 = row M`, then one matrix `R` has all of them as its compressed
rows: `(R * M) i = w i`.  This is the "choose preimages" half of the converse
of Claim 4. -/
theorem exists_rows_mul_eq {t m n : Type*} [Fintype t] [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n K) (w : t → (n → K)) (hw : ∀ i, w i ∈ Q1Subspace.rowSpace M) :
    ∃ R : Matrix t m K, ∀ i, (R * M) i = w i := by
  classical
  choose u hu using fun i => (mem_rowSpace_iff_exists_vecMul M (w i)).mp (hw i)
  refine ⟨Matrix.of u, fun i => ?_⟩
  have h1 : (Matrix.of u * M) i = Matrix.vecMul (u i) M := by
    ext j
    rw [Matrix.vecMul_apply_eq_sum, Matrix.mul_apply]
    rfl
  rw [h1]
  exact hu i

/-- **Claim 4 (`lem:sandwich`), sandwich and dimension bound.**  For
`L = [L₀; R]`: `W₀ ⊆ W ⊆ 𝒯`, `dim W ≤ dim W₀ + r`, and every element of `𝒯`
is a free row's image. -/
theorem claim4_sandwich {n0 r m n : Type*} [Fintype n0] [Fintype r] [Fintype m] [Fintype n]
    [DecidableEq m]
    (L0 : Matrix n0 m K) (R : Matrix r m K) (M : Matrix m n K) :
    Q1Subspace.rowSpace (L0 * M) ≤ Q1Subspace.rowSpace (Matrix.fromRows L0 R * M) ∧
    Q1Subspace.rowSpace (Matrix.fromRows L0 R * M) ≤ Q1Subspace.rowSpace M ∧
    finrank K ↥(Q1Subspace.rowSpace (Matrix.fromRows L0 R * M))
      ≤ finrank K ↥(Q1Subspace.rowSpace (L0 * M)) + Fintype.card r ∧
    (∀ w : n → K, w ∈ Q1Subspace.rowSpace M → ∃ u : m → K, Matrix.vecMul u M = w) := by
  have hW : Q1Subspace.rowSpace (Matrix.fromRows L0 R * M)
      = Q1Subspace.rowSpace (L0 * M) ⊔ Q1Subspace.rowSpace (R * M) := by
    rw [Matrix.fromRows_mul, Q1Subspace.rowSpace_fromRows]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hW]
    exact le_sup_left
  · rw [hW]
    exact sup_le (rowSpace_mul_le L0 M) (rowSpace_mul_le R M)
  · rw [hW]
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (Q1Subspace.rowSpace (L0 * M)) (Q1Subspace.rowSpace (R * M))
    have hR : finrank K ↥(Q1Subspace.rowSpace (R * M)) ≤ Fintype.card r := by
      rw [← Q1Subspace.rank_eq_finrank_rowSpace]
      exact Matrix.rank_le_card_height (R * M)
    omega
  · intro w hw
    exact (mem_rowSpace_iff_exists_vecMul M w).mp hw

end Claim4

/-! ## Claim 5 (`lem:W-conditions`)

Paper: (5a) holds iff `π₂(W) ⊆ π₁(W)`, and (5b) holds iff
`dim π_λ(W) = dim π₁(W)` for every `λ ∈ ℂ`; here `W = row[H  H_A]`.

Lean form: `pairRowSpace H HA = span{(H i, HA i)}` is the row space of the
row pairs.  The theorem first identifies the projections of this subspace
(`π₁ = row H`, `π₂ = row H_A`, `π_λ = row(λH - H_A)`) and then transports the
two rank criteria of `Q1RowSpace`/`Q1Pencil` across that identification.

Reuses: `pi1`, `pi2` (`Q1Projection.lean`), `piLam` (`BoundLower.lean`),
`rank_fromRows_eq_rank_iff` (`Q1RowSpace.lean`),
`rank_eq_finrank_rowSpace` (`Q1RowSpace.lean`).

Gap: the paper applies `π_λ` to the complexification `W_ℂ`; this file works
over a single field `K` and does not formalize the scalar extension.  The
equivalence itself is field-independent, so this is a cosmetic gap. -/
section Claim5

variable {q k : Type*} [Fintype q] [Fintype k]

/-- The row space of the row pairs `(H i, HA i)`: this is the paper's
`W = row[H  H_A] ⊆ K^k × K^k`. -/
def pairRowSpace (H HA : Matrix q k K) : Submodule K ((k → K) × (k → K)) :=
  Submodule.span K (Set.range (fun i : q => (H i, HA i)))

theorem pi1_pairRowSpace (H HA : Matrix q k K) :
    Q1Subspace.pi1 (pairRowSpace H HA) = Q1Subspace.rowSpace H := by
  have hset : LinearMap.fst K (k → K) (k → K) ''
      Set.range (fun i : q => (H i, HA i)) = Set.range (fun i : q => H i) := by
    ext x
    constructor
    · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(H i, HA i), ⟨i, rfl⟩, rfl⟩
  rw [pairRowSpace, Q1Subspace.pi1, Submodule.map_span, hset, Q1Subspace.rowSpace]

theorem pi2_pairRowSpace (H HA : Matrix q k K) :
    Q1Subspace.pi2 (pairRowSpace H HA) = Q1Subspace.rowSpace HA := by
  have hset : LinearMap.snd K (k → K) (k → K) ''
      Set.range (fun i : q => (H i, HA i)) = Set.range (fun i : q => HA i) := by
    ext x
    constructor
    · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(H i, HA i), ⟨i, rfl⟩, rfl⟩
  rw [pairRowSpace, Q1Subspace.pi2, Submodule.map_span, hset, Q1Subspace.rowSpace]

theorem piLam_pairRowSpace (H HA : Matrix q k K) (lam : K) :
    Q1Subspace.piLam lam (pairRowSpace H HA) = Q1Subspace.rowSpace (lam • H - HA) := by
  have hset : (lam • LinearMap.fst K (k → K) (k → K)
        - LinearMap.snd K (k → K) (k → K)) ''
      Set.range (fun i : q => (H i, HA i)) = Set.range (fun i : q => (lam • H - HA) i) := by
    ext x
    constructor
    · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by ext j; simp [Matrix.sub_apply, Matrix.smul_apply]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(H i, HA i), ⟨i, rfl⟩, by ext j; simp [Matrix.sub_apply, Matrix.smul_apply]⟩
  rw [pairRowSpace, Q1Subspace.piLam, Submodule.map_span, hset, Q1Subspace.rowSpace]

/-- **Claim 5 (`lem:W-conditions`).**  For `W = row[H  H_A]`:
(5a) (`rank[H_A; H] = rank H`) holds iff `π₂(W) ≤ π₁(W)`, and
(5b) (`rank(λH − H_A) = rank H` for all `λ`) holds iff
`dim π_λ(W) = dim π₁(W)` for all `λ`. -/
theorem claim5_conditions_depend_on_W (H HA : Matrix q k K) :
    ((Matrix.fromRows HA H).rank = H.rank ↔
      Q1Subspace.pi2 (pairRowSpace H HA) ≤ Q1Subspace.pi1 (pairRowSpace H HA)) ∧
    ((∀ lam : K, (lam • H - HA).rank = H.rank) ↔
      ∀ lam : K, finrank K ↥(Q1Subspace.piLam lam (pairRowSpace H HA))
        = finrank K ↥(Q1Subspace.pi1 (pairRowSpace H HA))) := by
  constructor
  · rw [Q1Subspace.rank_fromRows_eq_rank_iff, pi2_pairRowSpace, pi1_pairRowSpace]
  · constructor
    · intro h lam
      rw [piLam_pairRowSpace, pi1_pairRowSpace,
        ← Q1Subspace.rank_eq_finrank_rowSpace (lam • H - HA),
        ← Q1Subspace.rank_eq_finrank_rowSpace H]
      exact h lam
    · intro h lam
      have hlam := h lam
      rw [piLam_pairRowSpace, pi1_pairRowSpace,
        ← Q1Subspace.rank_eq_finrank_rowSpace (lam • H - HA),
        ← Q1Subspace.rank_eq_finrank_rowSpace H] at hlam
      exact hlam

end Claim5

/-! ## Claim 6 (`lem:struct`)

Paper: for a feasible `W` with `ω = dim π₁(W) > 0`,
`ω + 1 ≤ dim W ≤ 2ω`.

Lean form: `ω = finrank K (pi1 W)`; feasibility is the algebraic condition
`π₂(W) ≤ π₁(W)` plus the spectral condition
`finrank (piLam λ W) = ω` for all `λ`.  The paper works over `ℂ`, hence the
`[IsAlgClosed K]` assumption (used only for the eigenvalue in the lower half).

Reuses: `finrank_add_one_le_of_spectral` (`BoundLower.lean`, the lower half),
`pi1_eq_pi2_of_spectral` (`BoundLower.lean`, `λ = 0` step),
`finrank_le_two_mul_of_pi1_eq_pi2` (`Q1Projection.lean`, the upper half).

Gap: nothing beyond the standing `ω > 0` hypothesis; the paper notes the bound
fails at `ω = 0` (`H = H_A = 0`, `dim W = 0`). -/
section Claim6

variable {F : Type*} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- **Claim 6 (`lem:struct`).**  A feasible `W` with `ω = dim π₁(W) > 0`
satisfies `ω + 1 ≤ dim W ≤ 2ω`. -/
theorem claim6_struct [IsAlgClosed K] {W : Submodule K (F × F)}
    (hle : Q1Subspace.pi2 W ≤ Q1Subspace.pi1 W)
    (hω : 0 < finrank K ↥(Q1Subspace.pi1 W))
    (hspec : ∀ lam : K, finrank K ↥(Q1Subspace.piLam lam W)
      = finrank K ↥(Q1Subspace.pi1 W)) :
    finrank K ↥(Q1Subspace.pi1 W) + 1 ≤ finrank K ↥W ∧
    finrank K ↥W ≤ 2 * finrank K ↥(Q1Subspace.pi1 W) := by
  refine ⟨Q1Subspace.finrank_add_one_le_of_spectral hle hω hspec, ?_⟩
  have h0 : finrank K ↥(Q1Subspace.piLam 0 W) = finrank K ↥(Q1Subspace.pi1 W) := hspec 0
  exact Q1Subspace.finrank_le_two_mul_of_pi1_eq_pi2 W
    (Q1Subspace.pi1_eq_pi2_of_spectral hle h0)

end Claim6

/-! ## Claim 7 (`lem:monotone`)

Paper: `DEC(q) ⇒ DEC(q+1)` for `q < n`.

Lean form: the mathematical content of the paper's one-line proof — adjoining
a zero row to the observer `L` leaves the two design conditions (5a)/(5b)
unchanged, for an arbitrary fixed trailing block `D` (the paper's
`D = [CA; C]`), and likewise for the compressed spectral condition.  This is
stated uniformly in the number of adjoined zero rows.

Reuses: `conditions_fromRows_zero` (`MonotoneBlocks.lean`, both conditions at
once), `spectralCondition_append_zero_rows` and
`hasConstantRank_append_zero_rows` (`MonotoneBlocks.lean`, compressed blocks),
which in turn use `rank_fromRows_zero`, `rowSpan_fromRows_zero`
(`Monotone.lean`), `algebraicCondition_fromRows_zero`,
`spectralCondition_fromRows_zero` (`MonotoneBlocks.lean`).

The passage to the predicate `Q1Paper.PaperI.DEC` is carried out below, in
`claim7_DEC_succ`: besides the raw invariance, the file proves that (5a) and
(5b) depend only on the row spaces `rowSpace L`, `rowSpace (L * A)` and
`rowSpace (z • L - L * A)` (`rawConditions_congr`), and that padding the free
block by one zero row leaves each of them unchanged.  What remains outside the
formal statement is only the paper's side condition `q < n`, which is not part
of the Lean predicate `DEC`. -/
section Claim7

/-- **Claim 7 (`lem:monotone`), raw form.**  Adjoining zero rows to the
observer leaves both design conditions (5a) and (5b) unchanged, for an
arbitrary trailing block `D`. -/
theorem claim7_conditions_zero_rows {q c n d : Type*}
    [Fintype q] [Fintype c] [Fintype n] [Fintype d]
    (L : Matrix q n K) (A : Matrix n n K) (D : Matrix d n K) :
    ((Matrix.rank (Matrix.fromRows ((Matrix.fromRows L (0 : Matrix c n K)) * A)
          (Matrix.fromRows (Matrix.fromRows L (0 : Matrix c n K)) D))
        = Matrix.rank (Matrix.fromRows (Matrix.fromRows L (0 : Matrix c n K)) D))
      ∧ (∀ z : K, Matrix.rank (Matrix.fromRows (z • Matrix.fromRows L (0 : Matrix c n K)
            - Matrix.fromRows L (0 : Matrix c n K) * A) D)
          = Matrix.rank (Matrix.fromRows (Matrix.fromRows L (0 : Matrix c n K)) D)))
    ↔ ((Matrix.rank (Matrix.fromRows (L * A) (Matrix.fromRows L D))
          = Matrix.rank (Matrix.fromRows L D))
      ∧ (∀ z : K, Matrix.rank (Matrix.fromRows (z • L - L * A) D)
          = Matrix.rank (Matrix.fromRows L D))) :=
  conditions_fromRows_zero L A D

/-- **Claim 7 (`lem:monotone`), compressed form.**  On the compressed blocks
`(H, H_A)` = `(LN, LAN)`, adjoining zero rows preserves the spectral condition
and constant rank. -/
theorem claim7_compressed_zero_rows {m c n : Type*} [Fintype m] [Fintype c] [Fintype n]
    (H H_A : Matrix m n K) :
    (Q1Subspace.SpectralCondition (Matrix.fromRows H (0 : Matrix c n K))
        (Matrix.fromRows H_A (0 : Matrix c n K)) ↔ Q1Subspace.SpectralCondition H H_A) ∧
    (Q1Subspace.HasConstantRank (Matrix.fromRows H (0 : Matrix c n K))
        (Matrix.fromRows H_A (0 : Matrix c n K)) ↔ Q1Subspace.HasConstantRank H H_A) :=
  ⟨spectralCondition_append_zero_rows H H_A, hasConstantRank_append_zero_rows H H_A⟩

end Claim7

/-! ## Claim 8 (`lem:rankcons`)

Paper: for real `M, c`, `∃b, Mb = c` iff
`rank(MMᵀ) = rank(MMᵀ + ccᵀ)`; equivalently the disjunction over `t` of
`e_t(MMᵀ) > 0 ∧ e_{t+1}(MMᵀ) = 0 ∧ e_{t+1}(MMᵀ + ccᵀ) = 0`.

Lean form: the rank criterion, together with the equivalent augmented-matrix
rank test `rank[M  c] = rank M`.

Reuses: `exists_mulVec_eq_iff_rank_gram` and `rank_augment_eq_iff`
(`G5GramRank.lean`), `exists_solution_iff_mem_range` (`RankConsistency.lean`),
`Matrix.rank_self_mul_transpose`.

Gap: the elementary-symmetric-function form
`∨_t [e_t(Γ) > 0 ∧ e_{t+1}(Γ) = 0 ∧ e_{t+1}(Γ') = 0]` is **not** formalized.
Making it precise needs `e_j` as the `j`-th elementary symmetric function of
the eigenvalues of a positive semidefinite real matrix, together with
`e_j(Γ) > 0 ↔ rank Γ ≥ j`; Mathlib's spectral theory for Hermitian matrices
and the PSD/rank correspondence would have to be assembled for that.  The two
rank criteria above are exactly the statement the paper's proof uses to
replace the disjunction, so the mathematical content is present, but the
`e_j` formulation itself is not. -/
section Claim8

/-- **Claim 8 (`lem:rankcons`).**  `M b = c` is solvable iff the Gram rank
identity holds; equivalently iff adjoining the column `c` does not raise the
rank. -/
theorem claim8_rank_consistency {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    (∃ b : Fin n → ℝ, M.mulVec b = c) ↔
      ((M * Mᵀ).rank = (M * Mᵀ + Matrix.vecMulVec c c).rank ∧
        (augment M c).rank = M.rank) := by
  have hgram := exists_mulVec_eq_iff_rank_gram M c
  constructor
  · intro h
    refine ⟨hgram.mp h, ?_⟩
    have h' : ∃ b : Fin n → ℝ, M.mulVecLin b = c := by
      obtain ⟨b, hb⟩ := h
      exact ⟨b, by rwa [Matrix.mulVecLin_apply]⟩
    exact (rank_augment_eq_iff M c).mpr ((exists_solution_iff_mem_range M.mulVecLin c).mp h')
  · rintro ⟨h1, _⟩
    exact hgram.mpr h1

end Claim8

/-! ### Claim 7 at the level of `DEC`

The index bookkeeping deferred above, carried out explicitly: the padded free
block is `R' : Matrix (Fin (r+1))`, obtained from `R` by appending one zero
row.  The row-space characterisations of the two conditions show that they
only depend on `rowSpace L`, `rowSpace (L * A)` and `rowSpace (z • L - L * A)`,
and each of these is unchanged by the padding.  This yields the paper's
literal `DEC(q) ⇒ DEC(q+1)`. -/
section Claim7DEC

/-- Row `i` of a matrix product is `vecMul` of row `i`; the entrywise form. -/
theorem row_mul_eq_vecMul {p m n : Type*} [Fintype p] [Fintype m] [Fintype n]
    (X : Matrix p m K) (A : Matrix m n K) (i : p) :
    (X * A) i = Matrix.vecMul (X i) A := by
  ext j
  rw [Matrix.vecMul_apply_eq_sum, Matrix.mul_apply]

/-- The row space of `X * A` is the image of the row space of `X` under
`u ↦ vecMul u A`. -/
theorem rowSpace_mul_eq_map {p m n : Type*} [Fintype p] [Fintype m] [Fintype n]
    (X : Matrix p m K) (A : Matrix m n K) :
    Q1Subspace.rowSpace (X * A)
      = (Q1Subspace.rowSpace X).map (Matrix.vecMulLinear A) := by
  change Submodule.span K (Set.range (fun i : p => (X * A) i))
    = (Submodule.span K (Set.range (fun i : p => X i))).map (Matrix.vecMulLinear A)
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨X i, ⟨i, rfl⟩, by
      rw [Matrix.vecMulLinear_apply]
      exact (row_mul_eq_vecMul X A i).symm⟩
  · rintro ⟨y, ⟨i, rfl⟩, hy⟩
    refine ⟨i, ?_⟩
    show (X * A) i = x
    rw [row_mul_eq_vecMul, ← Matrix.vecMulLinear_apply]
    exact hy

/-- The pencil row space of `z • X - X * A` is the image of the row space of
`X` under `u ↦ z • u - vecMul u A`. -/
theorem rowSpace_pencil_eq_map {p n : Type*} [Fintype p] [Fintype n]
    (X : Matrix p n K) (A : Matrix n n K) (z : K) :
    Q1Subspace.rowSpace (z • X - X * A)
      = (Q1Subspace.rowSpace X).map
          (z • (LinearMap.id : (n → K) →ₗ[K] (n → K)) - Matrix.vecMulLinear A) := by
  change Submodule.span K (Set.range (fun i : p => (z • X - X * A) i))
    = (Submodule.span K (Set.range (fun i : p => X i))).map
        (z • LinearMap.id - Matrix.vecMulLinear A)
  rw [Submodule.map_span]
  congr 1
  have hrow : ∀ i : p, (z • X - X * A) i
      = (z • (LinearMap.id : (n → K) →ₗ[K] (n → K)) - Matrix.vecMulLinear A) (X i) := by
    intro i
    rw [show (z • X - X * A) i = z • X i - (X * A) i from rfl, row_mul_eq_vecMul]
    simp [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨X i, ⟨i, rfl⟩, (hrow i).symm⟩
  · rintro ⟨y, ⟨i, rfl⟩, hy⟩
    exact ⟨i, by rw [← hy]; exact hrow i⟩

theorem rowSpace_mul_congr {p p' m n : Type*} [Fintype p] [Fintype p']
    [Fintype m] [Fintype n] {X : Matrix p m K} {Y : Matrix p' m K}
    (h : Q1Subspace.rowSpace X = Q1Subspace.rowSpace Y) (A : Matrix m n K) :
    Q1Subspace.rowSpace (X * A) = Q1Subspace.rowSpace (Y * A) := by
  rw [rowSpace_mul_eq_map X A, rowSpace_mul_eq_map Y A, h]

theorem rowSpace_pencil_congr {p p' n : Type*} [Fintype p] [Fintype p'] [Fintype n]
    {X : Matrix p n K} {Y : Matrix p' n K}
    (h : Q1Subspace.rowSpace X = Q1Subspace.rowSpace Y) (A : Matrix n n K) (z : K) :
    Q1Subspace.rowSpace (z • X - X * A) = Q1Subspace.rowSpace (z • Y - Y * A) := by
  rw [rowSpace_pencil_eq_map X A z, rowSpace_pencil_eq_map Y A z, h]

/-- (5a) as a row-space inequality, with an arbitrary trailing block `D`. -/
theorem rawAlgebraic_iff_rowSpace {q d n : Type*} [Fintype q] [Fintype d] [Fintype n]
    (L : Matrix q n K) (A : Matrix n n K) (D : Matrix d n K) :
    (Matrix.rank (Matrix.fromRows (L * A) (Matrix.fromRows L D))
        = Matrix.rank (Matrix.fromRows L D))
      ↔ Q1Subspace.rowSpace (L * A) ≤ Q1Subspace.rowSpace L ⊔ Q1Subspace.rowSpace D := by
  rw [Q1Subspace.rank_fromRows_eq_rank_iff, Q1Subspace.rowSpace_fromRows]

/-- (5b) as an equality of dimensions of augmented row spaces, with an
arbitrary trailing block `D`.  (Both sides of (5b) contain `D`, so the
`rank = rank` form is *not* the `rank_fromRows_eq_rank_iff` form; this is the
correct row-space transcription.) -/
theorem rawSpectral_iff_finrank {q d n : Type*} [Fintype q] [Fintype d] [Fintype n]
    (L : Matrix q n K) (A : Matrix n n K) (D : Matrix d n K) :
    (∀ z : K, Matrix.rank (Matrix.fromRows (z • L - L * A) D)
        = Matrix.rank (Matrix.fromRows L D))
      ↔ ∀ z : K, finrank K ↥(Q1Subspace.rowSpace (z • L - L * A)
            ⊔ Q1Subspace.rowSpace D)
          = finrank K ↥(Q1Subspace.rowSpace L ⊔ Q1Subspace.rowSpace D) := by
  constructor
  · intro h z
    rw [← Q1Subspace.rowSpace_fromRows (z • L - L * A) D,
      ← Q1Subspace.rowSpace_fromRows L D,
      ← Q1Subspace.rank_eq_finrank_rowSpace (Matrix.fromRows (z • L - L * A) D),
      ← Q1Subspace.rank_eq_finrank_rowSpace (Matrix.fromRows L D)]
    exact h z
  · intro h z
    have hz := h z
    rw [← Q1Subspace.rowSpace_fromRows (z • L - L * A) D,
      ← Q1Subspace.rowSpace_fromRows L D,
      ← Q1Subspace.rank_eq_finrank_rowSpace (Matrix.fromRows (z • L - L * A) D),
      ← Q1Subspace.rank_eq_finrank_rowSpace (Matrix.fromRows L D)] at hz
    exact hz

/-- **The two design conditions depend only on the row spaces** of `L`, of
`L * A`, and of the pencils `z • L - L * A`. -/
theorem rawConditions_congr {q q' d n : Type*} [Fintype q] [Fintype q']
    [Fintype d] [Fintype n]
    (L : Matrix q n K) (L' : Matrix q' n K) (A : Matrix n n K) (D : Matrix d n K)
    (hL : Q1Subspace.rowSpace L = Q1Subspace.rowSpace L')
    (hLA : Q1Subspace.rowSpace (L * A) = Q1Subspace.rowSpace (L' * A))
    (hpen : ∀ z : K, Q1Subspace.rowSpace (z • L - L * A)
      = Q1Subspace.rowSpace (z • L' - L' * A)) :
    ((Matrix.rank (Matrix.fromRows (L * A) (Matrix.fromRows L D))
        = Matrix.rank (Matrix.fromRows L D))
      ∧ (∀ z : K, Matrix.rank (Matrix.fromRows (z • L - L * A) D)
          = Matrix.rank (Matrix.fromRows L D)))
    ↔ ((Matrix.rank (Matrix.fromRows (L' * A) (Matrix.fromRows L' D))
        = Matrix.rank (Matrix.fromRows L' D))
      ∧ (∀ z : K, Matrix.rank (Matrix.fromRows (z • L' - L' * A) D)
          = Matrix.rank (Matrix.fromRows L' D))) := by
  rw [rawAlgebraic_iff_rowSpace L A D, rawAlgebraic_iff_rowSpace L' A D,
    rawSpectral_iff_finrank L A D, rawSpectral_iff_finrank L' A D]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← hLA, ← hL]
      exact h1
    · intro z
      rw [← hpen z, ← hL]
      exact h2 z
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [hLA, hL]
      exact h1
    · intro z
      rw [hpen z, hL]
      exact h2 z

/-- **Claim 7 (`lem:monotone`), `DEC` form.**  `DEC(q) ⇒ DEC(q+1)`: the padded
free block `R'` (one extra zero row) satisfies the same two conditions. -/
theorem claim7_DEC_succ {p r0 n : ℕ} (C : Matrix (Fin p) (Fin n) K)
    (A : Matrix (Fin n) (Fin n) K) (L0 : Matrix (Fin r0) (Fin n) K) (r : ℕ) :
    Q1Paper.PaperI.DEC C A L0 r → Q1Paper.PaperI.DEC C A L0 (r + 1) := by
  classical
  rintro ⟨R, hcond⟩
  let R' : Matrix (Fin (r + 1)) (Fin n) K :=
    Matrix.of (fun (i : Fin (r + 1)) (j : Fin n) =>
      if h : (i : ℕ) < r then R ⟨i, h⟩ j else 0)
  have hgen : ∀ (i : Fin (r + 1)) (h : (i : ℕ) < r), R' i = R ⟨i, h⟩ := by
    intro i h
    ext k
    simp only [R', Matrix.of_apply]
    rw [dif_pos h]
  have hgen0 : ∀ (i : Fin (r + 1)), ¬ ((i : ℕ) < r) → R' i = 0 := by
    intro i h
    ext k
    simp only [R', Matrix.of_apply]
    rw [dif_neg h]
    simp
  have hR' : Q1Subspace.rowSpace R' = Q1Subspace.rowSpace R := by
    apply le_antisymm
    · rw [Q1Subspace.rowSpace, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show R' i ∈ Q1Subspace.rowSpace R
      by_cases h : (i : ℕ) < r
      · rw [hgen i h]
        exact Submodule.subset_span ⟨⟨i, h⟩, rfl⟩
      · rw [hgen0 i h]
        exact Submodule.zero_mem _
    · rw [Q1Subspace.rowSpace, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show R j ∈ Q1Subspace.rowSpace R'
      have hlt : (j : ℕ) < r + 1 := Nat.lt_succ_of_lt j.isLt
      have key : R' ⟨j, hlt⟩ = R j := by
        have h1 := hgen ⟨j, hlt⟩ j.isLt
        simpa using h1
      rw [← key]
      exact Submodule.subset_span ⟨⟨j, hlt⟩, rfl⟩
  let L : Matrix (Fin r0 ⊕ Fin r) (Fin n) K := Matrix.fromRows L0 R
  let L' : Matrix (Fin r0 ⊕ Fin (r + 1)) (Fin n) K := Matrix.fromRows L0 R'
  let D : Matrix (Fin p ⊕ Fin p) (Fin n) K := Matrix.fromRows (C * A) C
  have hLR : Q1Subspace.rowSpace L = Q1Subspace.rowSpace L' := by
    dsimp only [L, L']
    rw [Q1Subspace.rowSpace_fromRows, Q1Subspace.rowSpace_fromRows, hR']
  have hLAmul : Q1Subspace.rowSpace (L * A) = Q1Subspace.rowSpace (L' * A) := by
    dsimp only [L, L']
    rw [Matrix.fromRows_mul, Matrix.fromRows_mul, Q1Subspace.rowSpace_fromRows,
      Q1Subspace.rowSpace_fromRows, rowSpace_mul_congr hR' A]
  have hpen : ∀ z : K, Q1Subspace.rowSpace (z • L - L * A)
      = Q1Subspace.rowSpace (z • L' - L' * A) := by
    intro z
    have hbL : z • L - L * A = Matrix.fromRows (z • L0 - L0 * A) (z • R - R * A) := by
      dsimp only [L]
      rw [Matrix.fromRows_mul, Q1Paper.fromRows_smul, Q1Paper.fromRows_sub]
    have hbL' : z • L' - L' * A
        = Matrix.fromRows (z • L0 - L0 * A) (z • R' - R' * A) := by
      dsimp only [L']
      rw [Matrix.fromRows_mul, Q1Paper.fromRows_smul, Q1Paper.fromRows_sub]
    rw [hbL, hbL', Q1Subspace.rowSpace_fromRows, Q1Subspace.rowSpace_fromRows,
      rowSpace_pencil_congr hR' A z]
  refine ⟨R', ?_⟩
  exact (rawConditions_congr L L' A D hLR hLAmul hpen).mp hcond

end Claim7DEC

end Q1Paper
