/-
Q1Paper/PaperI/Prop4.lean

Proposition 4 of Paper I, case `r = 0` (no free rows): the decision problem reduces to the
**finite rational linear system** (R0) in the unknown blocks `S_0, …, S_{2ω-2}`, and deciding
(R0) decides feasibility.

(R0) is **not** restated here.  It is exactly the existential of part (v) of Claim 16, already
present in `PaperI/Claim16.lean` (`iv_implies_v`, `v_implies_iv`, `claim16_iv_iff_v`):

  `∃ T : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) K,
      T 0 * G = -1 ∧
      (∀ j : Fin (2 * ω - 2), T (Fin.castSucc j) * X - T (Fin.succ j) * G = 0) ∧
      T (Fin.last (2 * ω - 2)) * X = 0`

Every statement below reuses that shape verbatim (no new structure, no new predicate).

Contents:

* `prop4_r0_iff_spectral` : **(R0) solvable ⟺ `rank (λ • X − G) = ω` for every `λ : ℂ`.**
  - ⟹ : a solution of (R0) reassembles into a polynomial left inverse of the pencil
        (`spoly_mul_pencil_eq_one`, used inside `v_implies_i`) and hence forces full column
        rank at every complex parameter (`v_implies_i`).
  - ⟸ : spectral ⟹ the maximal minors of the pencil have no common complex root
        (`rank_eq_iff_no_common_complex_root`, `PaperI/C16Gcd.lean`)
        ⟹ their gcd in `ℚ[λ]` is a nonzero constant
        (`gcd_isConst_of_no_common_complex_root`)
        ⟹ a degree-bounded rational left inverse of the pencil exists
        (`claim16_iii_implies_iv_of_gcd_isConst`, `PaperI/BezoutBounded.lean`)
        ⟹ coefficient comparison gives (R0) (`iv_implies_v`).
    So the *rational* solvability of (R0) is exactly the spectral condition — no algebraic
    closure, no sampling over `λ`, and no search over the `S_j`.
* `decR0`, `decR0_correct` : the `r = 0` decision function and its correctness.
  `decR0` is a **specification-level** decision function (`Bool`-valued, noncomputable): it is
  the classical decision of the predicate (R0).  It is *not* an algorithm; see the note on
  `decR0` below and the closing remarks of this file.
* `rank_map_ratComplex` : the rank is unchanged by `ℚ → ℂ` (both directions via the
  rank/minors criterion of `PaperI/MinorRank.lean`).
* `prop4_compressed`, `decR0_iff_compressedSpectral` : (R0) ⟺ the compressed spectral
  condition on `(H, H_A)` with `ω = rank H` — the `r = 0` form of the paper's `DEC` after
  `DEC_iff_compressed` / `DEC_complex_iff_compressed`.

No `sorry`, no `admit`, no new axioms.
-/

import Q1Paper.PaperI.BezoutBounded
import Q1Paper.PaperI.Interface

open Matrix Polynomial
open scoped BigOperators

namespace Q1Paper

noncomputable section

/-! ## 1. (R0) ⟺ the spectral condition -/

/-- **Proposition 4, `r = 0` case.**  The rational linear system (R0) of Claim 16 (v) —
unknown blocks `S_0, …, S_{2ω-2} : Matrix (Fin ω) (Fin q) ℚ` satisfying
`S_0 G = -1`, `S_{j-1} X - S_j G = 0`, `S_{2ω-2} X = 0` — is solvable over `ℚ` exactly when
the pencil `λX − G` has rank `ω` at every complex parameter. -/
theorem prop4_r0_iff_spectral {q ω : ℕ} (hω : 1 ≤ ω) (X G : Matrix (Fin q) (Fin ω) ℚ) :
    (∃ S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) ℚ,
        S 0 * G = -1 ∧
        (∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0) ∧
        S (Fin.last (2 * ω - 2)) * X = 0) ↔
    (∀ lam : ℂ, (lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).rank = ω) := by
  constructor
  · -- (R0) ⟹ spectral: reassemble the blocks into a left inverse, then evaluate.
    rintro ⟨S, h0, hj, hd⟩
    exact v_implies_i X G S h0 hj hd
  · -- spectral ⟹ (R0): no common complex root, constant gcd, bounded Bézout, coefficients.
    intro hspec
    have hroot : NoCommonComplexRoot (pencilMinors X G) :=
      (rank_eq_iff_no_common_complex_root X G).mp hspec
    have hgcd : FamilyGcdIsConst (pencilMinors X G) :=
      gcd_isConst_of_no_common_complex_root hroot
    obtain ⟨S, hS, hdeg⟩ := claim16_iii_implies_iv_of_gcd_isConst hω X G hgcd
    exact iv_implies_v X G S hS hdeg

/-! ## 2. The `r = 0` decision function and its correctness -/

/-- **The `r = 0` decision**: solve (R0), return `true` iff it is solvable.

This is the `Bool`-valued decision of the predicate (R0) itself: the classical (propositional)
decision of the existential statement of Claim 16 (v).  It is `noncomputable` and is therefore a
*correctness specification at the level of the predicate*, not an executable solver: Mathlib
(`leanprover/lean4:v4.35.0`, Mathlib rev `f0b4c81`) does not provide a computable rank or a
Gaussian-elimination/linear-system solver over `ℚ`, so no executable `decR0` is constructed
here (`decR0_correct` is what a future executable implementation must meet).  The project's
Bareiss development (`PaperI/BareissTableau.lean`, `PaperI/BareissAssemble.lean`) supplies a
computable fraction-free elimination for *square* matrices with nonzero leading principal
minors (`tab_pivot`), together with its pivot/determinant theorems; an executable `decR0` would
still need (i) symmetry pivoting or a minor-selection rank test, (ii) the assembly of the block
system in the unknowns `S_0, …, S_{2ω-2}`, and (iii) the proof that this elimination decides
solvability of that system.  None of the three is formalised in the tree. -/
noncomputable def decR0 (q ω : ℕ) (X G : Matrix (Fin q) (Fin ω) ℚ) : Bool := by
  classical
  exact decide (∃ S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) ℚ,
        S 0 * G = -1 ∧
        (∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0) ∧
        S (Fin.last (2 * ω - 2)) * X = 0)

/-- **Correctness of `decR0`**: it returns `true` exactly on the pairs `(X, G)` whose pencil has
full column rank `ω` at every complex parameter.  Combined with `prop4_r0_iff_spectral` this is
the statement that deciding (R0) decides the `r = 0` feasibility question. -/
theorem decR0_correct {q ω : ℕ} (hω : 1 ≤ ω) (X G : Matrix (Fin q) (Fin ω) ℚ) :
    decR0 q ω X G = true ↔
      (∀ lam : ℂ, (lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).rank = ω) := by
  classical
  rw [decR0, decide_eq_true_iff]
  exact prop4_r0_iff_spectral hω X G

/-! ## 3. Rank is unchanged by `ℚ → ℂ` -/

/-- Complexifying commutes with the determinant (over `ℚ`). -/
theorem det_map_ratComplex {ω : ℕ} (A : Matrix (Fin ω) (Fin ω) ℚ) :
    (A.map (algebraMap ℚ ℂ)).det = algebraMap ℚ ℂ A.det := by
  have h := RingHom.map_det (algebraMap ℚ ℂ) A
  rw [show (algebraMap ℚ ℂ).mapMatrix A = A.map (algebraMap ℚ ℂ) from rfl] at h
  exact h.symm

/-- `rank M_ℂ ≤ rank M`: a nonzero minor of `M_ℂ` is the complexification of a nonzero minor
of `M`. -/
theorem rank_map_ratComplex_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) :
    (M.map (algebraMap ℚ ℂ)).rank ≤ M.rank := by
  obtain ⟨ρ, κ, _, _, hdet⟩ :=
    PaperI.exists_det_submatrix_ne_zero_of_rank (M.map (algebraMap ℚ ℂ)) rfl
  have h1 : (M.submatrix ρ κ).det ≠ 0 := by
    intro h0
    apply hdet
    rw [show (M.map (algebraMap ℚ ℂ)).submatrix ρ κ
        = (M.submatrix ρ κ).map (algebraMap ℚ ℂ) from by ext i j; rfl,
      det_map_ratComplex, h0, map_zero]
  exact PaperI.rank_le_of_det_maximalMinor_ne_zero M ρ κ h1

/-- `rank M ≤ rank M_ℂ`: complexifying a nonzero minor keeps it nonzero. -/
theorem rank_le_map_ratComplex {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) :
    M.rank ≤ (M.map (algebraMap ℚ ℂ)).rank := by
  obtain ⟨ρ, κ, _, _, hdet⟩ := PaperI.exists_det_submatrix_ne_zero_of_rank M rfl
  have h1 : ((M.map (algebraMap ℚ ℂ)).submatrix ρ κ).det ≠ 0 := by
    rw [show (M.map (algebraMap ℚ ℂ)).submatrix ρ κ
        = (M.submatrix ρ κ).map (algebraMap ℚ ℂ) from by ext i j; rfl,
      det_map_ratComplex]
    intro h0
    exact hdet ((algebraMap ℚ ℂ).injective (by rw [h0, map_zero]))
  exact PaperI.rank_le_of_det_maximalMinor_ne_zero (M.map (algebraMap ℚ ℂ)) ρ κ h1

/-- **Rank is unchanged by `ℚ → ℂ`.**  Consequently a rational matrix — in particular the
compressed block `H` of the paper — has the same rank whether the ranks are computed over `ℚ`
(as the data are) or over `ℂ` (as `DECℂ` prescribes). -/
theorem rank_map_ratComplex {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) :
    (M.map (algebraMap ℚ ℂ)).rank = M.rank :=
  le_antisymm (rank_map_ratComplex_le M) (rank_le_map_ratComplex M)

/-! ## 4. The `r = 0` connection to the paper's `DEC`

`PaperI.DEC` (`PaperI/Interface.lean`) says: for some free block `R`, the row-stacked `L`
satisfies (5a) and (5b).  After compression (`PaperI.DEC_iff_compressed`, resp.
`PaperI.DEC_complex_iff_compressed` for `DECℂ`) this becomes
`compressedAlgebraic H H_A ∧ compressedSpectral H H_A` for the compressed blocks
`H = L * N`, `H_A = L * A * N`, where `compressedSpectral H H_A` unfolds to
`∀ λ, rank (λ • H − H_A) = H.rank`.

The next theorem is exactly the `r = 0` reduction: when the compressed block has `ω = rank H`
columns (i.e. we are in the full-column-rank, "no free rows" coordinates of Proposition 4), the
*compressed spectral condition* is a finite rational linear system, namely (R0), and nothing
else.  The hypothesis `H.rank = ω` is precisely the paper's `ω = rank H`. -/
theorem prop4_compressed {q ω : ℕ} (hω : 1 ≤ ω) (H HA : Matrix (Fin q) (Fin ω) ℚ)
    (hH : H.rank = ω) :
    PaperI.compressedSpectral (H.map (algebraMap ℚ ℂ)) (HA.map (algebraMap ℚ ℂ)) ↔
      (∃ S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) ℚ,
        S 0 * HA = -1 ∧
        (∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * H - S (Fin.succ j) * HA = 0) ∧
        S (Fin.last (2 * ω - 2)) * H = 0) := by
  unfold PaperI.compressedSpectral
  rw [rank_map_ratComplex H, hH]
  exact (prop4_r0_iff_spectral hω H HA).symm

/-- **`decR0` decides the `r = 0` compressed spectral condition.** -/
theorem decR0_iff_compressedSpectral {q ω : ℕ} (hω : 1 ≤ ω) (H HA : Matrix (Fin q) (Fin ω) ℚ)
    (hH : H.rank = ω) :
    decR0 q ω H HA = true ↔
      PaperI.compressedSpectral (H.map (algebraMap ℚ ℂ)) (HA.map (algebraMap ℚ ℂ)) :=
  (decR0_correct hω H HA).trans
    ((prop4_compressed hω H HA hH).trans (prop4_r0_iff_spectral hω H HA)).symm

/-! ## 5. Non-vacuity

Two checks that the equivalence of §1 is not vacuous: an explicit solution of (R0) (`X = 0`,
`G = -1`, where the pencil is the constant invertible matrix), and a pair with no solution
(`X = 1`, `G = -1`, where the pencil vanishes at `λ = -1`). -/

/-- A `True` point of (R0): for `ω = q = 1`, `X = 0`, `G = -1` the block `S_0 = 1` satisfies
`S_0 G = -1` and `S_0 X = 0`. -/
example : ∃ S : Fin (2 * 1 - 2 + 1) → Matrix (Fin 1) (Fin 1) ℚ,
    S 0 * (-1) = -1 ∧
    (∀ j : Fin (2 * 1 - 2),
      S (Fin.castSucc j) * 0 - S (Fin.succ j) * (-1) = 0) ∧
    S (Fin.last (2 * 1 - 2)) * 0 = 0 := by
  refine ⟨fun _ => 1, by norm_num, ?_, by norm_num⟩
  intro j
  exact Fin.elim0 j

/-- The `True` point goes through `decR0_correct`: the pencil `λ • 0 − (−1) = 1` has rank
`ω = 1` at every complex parameter. -/
example : decR0 1 1 0 (-1) = true := by
  rw [decR0_correct (le_refl 1)]
  intro lam
  have hM : (lam • (0 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℂ)
      - (-1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℂ)) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hM, Matrix.rank_one, Fintype.card_fin]

/-- A `False` point: for `X = G = 1` the pencil `λ • 1 − 1` vanishes at `λ = 1`, so its rank is
not `ω = 1` there; consequently `decR0` does not return `true`. -/
example : decR0 1 1 1 1 ≠ true := by
  intro h
  have hspec := (decR0_correct (le_refl 1) (1 : Matrix (Fin 1) (Fin 1) ℚ) 1).mp h
  have h1 := hspec 1
  have hzero : ((1 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℂ)
      - (1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℂ)) = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hzero, Matrix.rank_zero] at h1
  omega

end

end Q1Paper

/-! ## Axiom audit -/

