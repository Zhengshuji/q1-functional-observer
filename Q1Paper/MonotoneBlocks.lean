
import Mathlib
import Q1Paper.Monotone
import Q1Paper.RowSpaceAlgebraic
import Q1Paper.ConstantRankPencil
/-!
Q1Paper/MonotoneBlocks.lean

Monotonicity of the feasible order (Paper I, Claim 7 / `lem:monotone`):
the bookkeeping that carries the two design conditions through `Matrix.fromRows`.

The paper's proof of monotonicity is one sentence: *adjoining a zero row to `R`
leaves `H`, `H_A`, and the ranks in (5a) and (5b) unchanged*.  This file makes
that sentence exact, uniformly in the observer matrix, and in the trailing block
of rows that the paper carries along.

Setting.  `L : Matrix q n K` is the observer matrix and

  `L' := Matrix.fromRows L (0 : Matrix c n K)`

is `L` with `c` extra rows of zeros (`c = 1` is the paper's step from order `q`
to order `q+1`).  `A : Matrix n n K` is the system matrix of the paper (square),
`N : Matrix n k K` a basis matrix of `K_0 = ker[C; CA]`, and `D : Matrix d n K` a
*fixed* trailing block that does not change when `L` grows.  For the paper

  `D = Matrix.fromRows (C * A) C`,

and the paper's four-block matrices are then `[L A; L; C A; C] =
Matrix.fromRows (L * A) (Matrix.fromRows L D)` and `[L; C A; C] =
Matrix.fromRows L D`.

Contents.
* `fromRows_mul_eq` — the `fromRows`-multiplication lemma.  **This already exists
  in Mathlib as `Matrix.fromRows_mul` (it is `@[simp]`)**; it is restated under a
  project name only so that the rest of the file reads uniformly, and it is
  proved by `exact Matrix.fromRows_mul ..`.  No new mathematics.
* `rank_fromRows_zero_mul`, `rank_fromRows_zero_mul_mul` — target 2: the two
  compressed blocks `H = L * N` and `H_A = L * A * N` keep their ranks when zero
  rows are adjoined to `L`.
* `algebraicCondition_fromRows_zero` — condition (5a) is the same for `L'` and `L`:
  `rank [L'A; L'; D] = rank [L'; D]` iff `rank [L A; L; D] = rank [L; D]`.
* `spectralCondition_fromRows_zero` — condition (5b) is the same for `L'` and `L`:
  `∀ z, rank [z•L' - L'A; D] = rank [L'; D]` iff the same with `L`.
* `conditions_fromRows_zero` — the two together: the pair of conditions defining
  `DEC` is invariant under adjoining zero rows.
* `spectralCondition_append_zero_rows`, `hasConstantRank_append_zero_rows` — the
  same statement in the *compressed* coordinates, on the library's own predicates
  `Q1Subspace.SpectralCondition` and `Q1Subspace.HasConstantRank` from
  `Q1Paper/ConstantRankPencil.lean`.

What is **not** here.  There is no `DEC` predicate in this library.  `ConstantRankPencil.lean`
offers `SpectralCondition`/`HasConstantRank` on compressed blocks `(H, H_A)`, but no
module defines the compression `H = L * N`, `H_A = L * A * N`, the prescribed block
`L_0`, or the family `L = [L_0; R]` indexed by the order `q`.  Hence the q-level
statement `DEC q → DEC (q+1)` is not stated here: it would need that interface, and
inventing one is out of scope.  What is proved is the mathematical content of its
proof — the invariance of the two conditions — uniformly in `L` and in `D`.
-/


open Matrix

namespace Q1Paper

variable {K : Type*} [Field K]

/-! ### 1. `fromRows` and multiplication -/

/-- Right multiplication distributes over a row partition:
`fromRows A₁ A₂ * X = fromRows (A₁ * X) (A₂ * X)`.

This is **exactly Mathlib's `Matrix.fromRows_mul`** (which is `@[simp]`); it is
restated here under a project name for uniform reading of this file and is proved
by that lemma.  No new mathematics, and nothing below depends on the restatement
rather than on the Mathlib lemma. -/
theorem fromRows_mul_eq {m₁ m₂ n p : Type*} [Fintype n]
    (A₁ : Matrix m₁ n K) (A₂ : Matrix m₂ n K) (X : Matrix n p K) :
    Matrix.fromRows A₁ A₂ * X = Matrix.fromRows (A₁ * X) (A₂ * X) :=
  Matrix.fromRows_mul A₁ A₂ X

/-- Scalar multiplication acts blockwise on a row partition. -/
theorem fromRows_smul {m₁ m₂ n : Type*} (c : K)
    (A₁ : Matrix m₁ n K) (A₂ : Matrix m₂ n K) :
    c • Matrix.fromRows A₁ A₂ = Matrix.fromRows (c • A₁) (c • A₂) := by
  ext (i | i) j <;> simp

/-- Subtraction acts blockwise on a row partition. -/
theorem fromRows_sub {m₁ m₂ n : Type*}
    (A₁ B₁ : Matrix m₁ n K) (A₂ B₂ : Matrix m₂ n K) :
    Matrix.fromRows A₁ A₂ - Matrix.fromRows B₁ B₂ = Matrix.fromRows (A₁ - B₁) (A₂ - B₂) := by
  ext (i | i) j <;> simp

/-- Multiplying a matrix with `c` zero rows adjoined, on the right: the zero block
stays zero.  This is the `fromRows`-level form of target 2. -/
theorem fromRows_zero_mul {q c n p : Type*} [Fintype n]
    (L : Matrix q n K) (A : Matrix n p K) :
    (Matrix.fromRows L (0 : Matrix c n K)) * A
      = Matrix.fromRows (L * A) (0 : Matrix c p K) := by
  rw [fromRows_mul_eq, Matrix.zero_mul]

/-! ### 2. The two compressed blocks keep their ranks (target 2) -/

/-- **Target 2, first block**: adjoining zero rows to `L` does not change the rank
of `H = L * N`. -/
theorem rank_fromRows_zero_mul {q c n k : Type*}
    [Fintype q] [Fintype c] [Fintype n] [Fintype k]
    (L : Matrix q n K) (N : Matrix n k K) :
    ((Matrix.fromRows L (0 : Matrix c n K)) * N).rank = (L * N).rank := by
  rw [fromRows_zero_mul, rank_fromRows_zero]

/-- **Target 2, second block**: adjoining zero rows to `L` does not change the rank
of `H_A = L * A * N`. -/
theorem rank_fromRows_zero_mul_mul {q c n p k : Type*}
    [Fintype q] [Fintype c] [Fintype n] [Fintype p] [Fintype k]
    (L : Matrix q n K) (A : Matrix n p K) (N : Matrix p k K) :
    (((Matrix.fromRows L (0 : Matrix c n K)) * A) * N).rank = ((L * A) * N).rank := by
  rw [fromRows_zero_mul, fromRows_zero_mul, rank_fromRows_zero]

/-! ### 3. The row space of a `fromRows` block -/

/-- `Q1Subspace.rowSpace` is `Q1Subspace.rowSpan` under another name; this records
the zero-row invariance already proved for `rowSpan` in `Q1Paper/Monotone.lean`. -/
theorem rowSpace_fromRows_zero {p c n : Type*} [Fintype p] [Fintype c] [Fintype n]
    (M : Matrix p n K) :
    Q1Subspace.rowSpace (Matrix.fromRows M (0 : Matrix c n K)) = Q1Subspace.rowSpace M :=
  rowSpan_fromRows_zero M

/-- Right multiplication keeps the row space: the row space of `(fromRows L 0) * A`
is that of `L * A`. -/
theorem rowSpace_zero_mul {q c n p : Type*} [Fintype q] [Fintype c] [Fintype n]
    [Fintype p] (L : Matrix q n K) (A : Matrix n p K) :
    Q1Subspace.rowSpace ((Matrix.fromRows L (0 : Matrix c n K)) * A)
      = Q1Subspace.rowSpace (L * A) := by
  rw [fromRows_zero_mul, rowSpace_fromRows_zero]

/-- Zero rows adjoined to the *upper* block of a stack do not change its row space. -/
theorem rowSpace_fromRows_zero_rows {p c n d : Type*}
    [Fintype p] [Fintype c] [Fintype n] [Fintype d]
    (M : Matrix p n K) (D : Matrix d n K) :
    Q1Subspace.rowSpace (Matrix.fromRows (Matrix.fromRows M (0 : Matrix c n K)) D)
      = Q1Subspace.rowSpace (Matrix.fromRows M D) := by
  conv_lhs => rw [Q1Subspace.rowSpace_fromRows]
  rw [rowSpace_fromRows_zero, ← Q1Subspace.rowSpace_fromRows]

/-- Zero rows adjoined to the *upper* block of a stack do not change its rank. -/
theorem rank_fromRows_zero_rows {p c n d : Type*}
    [Fintype p] [Fintype c] [Fintype n] [Fintype d]
    (M : Matrix p n K) (D : Matrix d n K) :
    (Matrix.fromRows (Matrix.fromRows M (0 : Matrix c n K)) D).rank
      = (Matrix.fromRows M D).rank := by
  rw [Q1Subspace.rank_eq_finrank_rowSpace, Q1Subspace.rank_eq_finrank_rowSpace,
    rowSpace_fromRows_zero_rows]

/-! ### 4. Condition (5a) -/

/-- **Condition (5a) is invariant under adjoining zero rows.**  With
`L' = fromRows L 0` and an arbitrary fixed trailing block `D` (for the paper,
`D = [C A; C]`), the algebraic rank equality for `L'` holds exactly when it holds
for `L`. -/
theorem algebraicCondition_fromRows_zero {q c n d : Type*}
    [Fintype q] [Fintype c] [Fintype n] [Fintype d]
    (L : Matrix q n K) (A : Matrix n n K) (D : Matrix d n K) :
    (Matrix.rank (Matrix.fromRows ((Matrix.fromRows L (0 : Matrix c n K)) * A)
        (Matrix.fromRows (Matrix.fromRows L (0 : Matrix c n K)) D))
      = Matrix.rank (Matrix.fromRows (Matrix.fromRows L (0 : Matrix c n K)) D))
    ↔ (Matrix.rank (Matrix.fromRows (L * A) (Matrix.fromRows L D))
      = Matrix.rank (Matrix.fromRows L D)) := by
  rw [Q1Subspace.rank_fromRows_eq_rank_iff, Q1Subspace.rank_fromRows_eq_rank_iff,
    rowSpace_zero_mul, rowSpace_fromRows_zero_rows]

/-! ### 5. Condition (5b): the pencil `z • L - L * A` -/

/-- The pencil of `L' = fromRows L 0` is the pencil of `L` with zero rows adjoined:
`z • L' - L' * A = fromRows (z • L - L * A) 0`. -/
theorem fromRows_zero_pencil {q c n : Type*} [Fintype q] [Fintype c] [Fintype n]
    (L : Matrix q n K) (A : Matrix n n K) (z : K) :
    z • Matrix.fromRows L (0 : Matrix c n K)
        - Matrix.fromRows L (0 : Matrix c n K) * A
      = Matrix.fromRows (z • L - L * A) (0 : Matrix c n K) := by
  rw [fromRows_zero_mul, fromRows_smul, fromRows_sub]
  simp

/-- **Condition (5b) is invariant under adjoining zero rows.**  The spectral
condition for `L' = fromRows L 0` — the rank equality for the pencil at every
scalar `z` — holds exactly when it holds for `L`. -/
theorem spectralCondition_fromRows_zero {q c n d : Type*}
    [Fintype q] [Fintype c] [Fintype n] [Fintype d]
    (L : Matrix q n K) (A : Matrix n n K) (D : Matrix d n K) :
    (∀ z : K, Matrix.rank (Matrix.fromRows (z • Matrix.fromRows L (0 : Matrix c n K)
          - Matrix.fromRows L (0 : Matrix c n K) * A) D)
        = Matrix.rank (Matrix.fromRows (Matrix.fromRows L (0 : Matrix c n K)) D))
    ↔ (∀ z : K, Matrix.rank (Matrix.fromRows (z • L - L * A) D)
        = Matrix.rank (Matrix.fromRows L D)) := by
  have hpen : ∀ z : K,
      Matrix.rank (Matrix.fromRows (z • Matrix.fromRows L (0 : Matrix c n K)
          - Matrix.fromRows L (0 : Matrix c n K) * A) D)
        = Matrix.rank (Matrix.fromRows (z • L - L * A) D) := by
    intro z
    rw [fromRows_zero_pencil, rank_fromRows_zero_rows]
  have hbot : Matrix.rank (Matrix.fromRows (Matrix.fromRows L (0 : Matrix c n K)) D)
      = Matrix.rank (Matrix.fromRows L D) := rank_fromRows_zero_rows L D
  constructor
  · intro h z
    rw [← hpen z, ← hbot]
    exact h z
  · intro h z
    rw [hpen z, hbot]
    exact h z

/-- **The two conditions together**: the pair of rank conditions that defines
`DEC` for the order of `L` is invariant under adjoining zero rows.  This is the
matrix content of the paper's "adjoining a zero row to `R` leaves `H`, `H_A`, and
the ranks in (5a) and (5b) unchanged". -/
theorem conditions_fromRows_zero {q c n d : Type*}
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
          = Matrix.rank (Matrix.fromRows L D))) := by
  rw [algebraicCondition_fromRows_zero L A D, spectralCondition_fromRows_zero L A D]

/-! ### 6. The same, on the compressed blocks of `Q1Paper/ConstantRankPencil.lean` -/

/-- **The paper's spectral condition on the compressed blocks** is invariant under
adjoining zero rows to `L`: `SpectralCondition (fromRows H 0) (fromRows H_A 0)` iff
`SpectralCondition H H_A`, where `H = L * N` and `H_A = L * A * N`. -/
theorem spectralCondition_append_zero_rows {m c n : Type*}
    [Fintype m] [Fintype c] [Fintype n]
    (H H_A : Matrix m n K) :
    Q1Subspace.SpectralCondition (Matrix.fromRows H (0 : Matrix c n K))
        (Matrix.fromRows H_A (0 : Matrix c n K))
      ↔ Q1Subspace.SpectralCondition H H_A := by
  have hpencil : ∀ z : K,
      z • Matrix.fromRows H (0 : Matrix c n K)
          - Matrix.fromRows H_A (0 : Matrix c n K)
        = Matrix.fromRows (z • H - H_A) (0 : Matrix c n K) := by
    intro z
    rw [fromRows_smul, fromRows_sub]
    simp
  have hz : ∀ z : K,
      Q1Subspace.matrixRank (z • Matrix.fromRows H (0 : Matrix c n K)
          - Matrix.fromRows H_A (0 : Matrix c n K))
        = Q1Subspace.matrixRank (z • H - H_A) := by
    intro z
    rw [hpencil z]
    exact rank_fromRows_zero (z • H - H_A)
  have hH : Q1Subspace.matrixRank (Matrix.fromRows H (0 : Matrix c n K))
      = Q1Subspace.matrixRank H :=
    rank_fromRows_zero H
  constructor
  · intro h z
    rw [← hz z, ← hH]
    exact h z
  · intro h z
    rw [hz z, hH]
    exact h z

/-- **Constant rank** of the pencil on the compressed blocks is likewise invariant
under adjoining zero rows. -/
theorem hasConstantRank_append_zero_rows {m c n : Type*}
    [Fintype m] [Fintype c] [Fintype n]
    (H H_A : Matrix m n K) :
    Q1Subspace.HasConstantRank (Matrix.fromRows H (0 : Matrix c n K))
        (Matrix.fromRows H_A (0 : Matrix c n K))
      ↔ Q1Subspace.HasConstantRank H H_A := by
  have hpencil : ∀ z : K,
      z • Matrix.fromRows H (0 : Matrix c n K)
          - Matrix.fromRows H_A (0 : Matrix c n K)
        = Matrix.fromRows (z • H - H_A) (0 : Matrix c n K) := by
    intro z
    rw [fromRows_smul, fromRows_sub]
    simp
  have hz : ∀ z : K,
      Q1Subspace.matrixRank (z • Matrix.fromRows H (0 : Matrix c n K)
          - Matrix.fromRows H_A (0 : Matrix c n K))
        = Q1Subspace.matrixRank (z • H - H_A) := by
    intro z
    rw [hpencil z]
    exact rank_fromRows_zero (z • H - H_A)
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, fun z => by rw [← hz z]; exact hr z⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, fun z => by rw [hz z]; exact hr z⟩

end Q1Paper
