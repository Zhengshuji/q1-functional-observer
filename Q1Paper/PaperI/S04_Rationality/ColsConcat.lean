import Q1Paper.PaperI.S04_Rationality.BitLenMatMul
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
Q1Paper/PaperI/S04_Rationality/ColsConcat.lean

**Column concatenation** `[A | B]` and its bit-length bound.

*** CORRECTION TO THE TASK PREMISE. ***  The task said "Mathlib has `Matrix.fromRows` but no
`Matrix.fromColumns`".  The second half is **false for the pinned Mathlib rev** (`f0b4c81`,
toolchain `v4.35.0`): Mathlib has `Matrix.fromCols` in
`Mathlib/Data/Matrix/ColumnRowPartitioned.lean`, with the API
`Matrix.fromCols_apply_inl/inr`, `Matrix.transpose_fromCols`,
`Matrix.fromCols_mulVec`, `Matrix.fromCols_mul_fromRows`.  It is already used in this very
project by `Q1Paper/GramRankAugmented.lean` (`M.fromCols (colMatrix c)`), which typechecks at
`Matrix (Fin m) (Fin n ⊕ Fin 1) ℝ`.  So `[N | A*N]` is `N.fromCols (A * N)` directly, and
nothing needs transposing.  Sections 2 and 3 below therefore state the bound twice: once for
the project-local `fromCols` (as requested, defined via `fromRows` of the transposes) and
once for Mathlib's `Matrix.fromCols` (Section 4, the version the paper should cite).

Column concatenation of `A : Matrix α γ` and `B : Matrix α δ` (blocks sharing the row type
`α`, with column index sets `γ` and `δ`) is the matrix `Matrix α (γ ⊕ δ)` whose `inl` columns
are those of `A` and whose `inr` columns are those of `B`.

NOTE ON THE REQUESTED SIGNATURE.  The task statement asked for
`(A : Matrix α γ) (B : Matrix β γ) : Matrix (α ⊕ β) γ`, i.e. `(fromRows Aᵀ Bᵀ)ᵀ` with the
*rows* of the inputs differing.  That does not typecheck: `fromRows` requires its two
arguments to share the **column** type, and `Aᵀ : Matrix γ α`, `Bᵀ : Matrix γ β` have column
types `α` and `β`.  The type-correct version has the **row** types equal and the column types
different, which is also the shape the paper needs: `N : Matrix (Fin n) (Fin k)` and
`A * N : Matrix (Fin n) (Fin k)` give `[N | A*N] : Matrix (Fin n) (Fin k ⊕ Fin k)`.  So below
`fromCols` takes `A : Matrix α γ`, `B : Matrix α δ` and returns `Matrix α (γ ⊕ δ)`; the
`Fin`-shaped statements are reindexed along `finSumFinEquiv : Fin γ ⊕ Fin δ ≃ Fin (γ + δ)`.

NOTE ON THE PAYOFF HYPOTHESIS.  `bitLenMat N ≤ t` is used rather than the entrywise
`∀ i j, bitLenRat (N i j) ≤ t`.  The entrywise form does *not* imply a bound on `bitLenMat N`:
`Matrix.den` is the **lcm** of the entry denominators, and an lcm can be strictly bigger than
every one of its arguments in bit length — the two entries `1/2`, `1/3` both have
`bitLenRat = 2`, but their common denominator `6` has bit length `3`, so for
`N = ![![1/2, 1/3]]` one has `bitLenMat N = 3 > 2 = max (bitLenRat entry)`.  The same witness
is recorded in `PaperI/BitLenMatMul.lean` right after `bitLenMatAny_fromRows_le`.  An honest
entrywise statement therefore needs an extra hypothesis controlling `N.den`, and the clean
form of that hypothesis is `bitLenMat N ≤ t` itself.

Check with `lake env lean Q1Paper/PaperI/ColsConcat.lean`.
-/


open Matrix

namespace Q1Paper.PaperI

/-! ## 1.  The column concatenation -/

/-- **Column concatenation** of two rational matrices sharing the row index type:
`fromCols A B = [A | B]`, with column index type `γ ⊕ δ`.  Defined as the transpose of the
row stack of the transposes, since the task asked for a `fromRows`-based construction.  (This
is `Matrix.fromCols` up to definitional unfolding; see Section 4.) -/
def fromCols {α γ δ : Type*} [Fintype α] [Fintype γ] [Fintype δ]
    (A : Matrix α γ ℚ) (B : Matrix α δ ℚ) : Matrix α (γ ⊕ δ) ℚ :=
  (Matrix.fromRows Aᵀ Bᵀ)ᵀ

/-- The two blocks really are the columns: the `inl` columns are those of `A`, the `inr`
columns those of `B`.  (Not needed for the bound; recorded so that `fromCols` is not a
vacuous definition.) -/
theorem fromCols_apply_inl {α γ δ : Type*} [Fintype α] [Fintype γ] [Fintype δ]
    (A : Matrix α γ ℚ) (B : Matrix α δ ℚ) (i : α) (j : γ) :
    fromCols A B i (Sum.inl j) = A i j := by
  simp [fromCols, Matrix.fromRows_apply_inl]

theorem fromCols_apply_inr {α γ δ : Type*} [Fintype α] [Fintype γ] [Fintype δ]
    (A : Matrix α γ ℚ) (B : Matrix α δ ℚ) (i : α) (j : δ) :
    fromCols A B i (Sum.inr j) = B i j := by
  simp [fromCols, Matrix.fromRows_apply_inr]

/-! ## 2.  The bit-length bound -/

/-- **Bit length of the column concatenation.**  `bitLenMat [A | B] ≤ bitLenMat A +
bitLenMat B`: transpose (bit length unchanged), `fromRows` (additive), transpose back. -/
theorem bitLenMatAny_fromCols_le {α γ δ : Type*} [Fintype α] [Fintype γ] [Fintype δ]
    (A : Matrix α γ ℚ) (B : Matrix α δ ℚ) :
    bitLenMatAny (fromCols A B) ≤ bitLenMatAny A + bitLenMatAny B := by
  refine (bitLenMatAny_transpose_le (Matrix.fromRows Aᵀ Bᵀ)).trans ?_
  refine (bitLenMatAny_fromRows_le Aᵀ Bᵀ).trans ?_
  exact Nat.add_le_add (bitLenMatAny_transpose_le A) (bitLenMatAny_transpose_le B)

/-- **Bit length of the column concatenation** (`Fin` form).  The column index type of
`fromCols A B` is `Fin k ⊕ Fin n`; reindexing it along
`finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n)` makes it an honest `Fin`-shaped matrix, for
which `bitLenMat` (rather than `bitLenMatAny`) is available.  The reindexing is a submatrix,
so it cannot increase the bit length. -/
theorem bitLenMat_fromCols_le {m k n : ℕ} (A : Matrix (Fin m) (Fin k) ℚ)
    (B : Matrix (Fin m) (Fin n) ℚ) :
    bitLenMat ((fromCols A B).submatrix id finSumFinEquiv.symm) ≤
      bitLenMat A + bitLenMat B := by
  have h := bitLenMatAny_submatrix_le (fromCols A B) (id : Fin m → Fin m) finSumFinEquiv.symm
  have h2 := h.trans (bitLenMatAny_fromCols_le A B)
  rwa [bitLenMatAny_eq_bitLenMat, bitLenMatAny_eq_bitLenMat, bitLenMatAny_eq_bitLenMat] at h2

/-- Transposition preserves `bitLenMatAny` exactly (the `≤` of
`bitLenMatAny_transpose_le` is an equality). -/
theorem bitLenMatAny_transpose_eq {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℚ) : bitLenMatAny Aᵀ = bitLenMatAny A := by
  refine le_antisymm (bitLenMatAny_transpose_le A) ?_
  have h := bitLenMatAny_transpose_le Aᵀ
  rwa [Matrix.transpose_transpose] at h

/-! ## 3.  The same bound for Mathlib's `Matrix.fromCols` -/

/-- **Mathlib's `Matrix.fromCols` does not increase the bit length** beyond the sum:
`bitLenMatAny (Matrix.fromCols A B) ≤ bitLenMatAny A + bitLenMatAny B`.  This is the
statement to cite: `Matrix.fromCols` is the real Mathlib name, and it is definitionally the
transposed row stack used above. -/
theorem bitLenMatAny_matrixFromCols_le {α γ δ : Type*} [Fintype α] [Fintype γ] [Fintype δ]
    (A : Matrix α γ ℚ) (B : Matrix α δ ℚ) :
    bitLenMatAny (Matrix.fromCols A B) ≤ bitLenMatAny A + bitLenMatAny B := by
  have hT : (Matrix.fromCols A B)ᵀ = Matrix.fromRows Aᵀ Bᵀ := Matrix.transpose_fromCols A B
  have h1 : bitLenMatAny (Matrix.fromCols A B) = bitLenMatAny (Matrix.fromRows Aᵀ Bᵀ) := by
    rw [← hT, bitLenMatAny_transpose_eq]
  rw [h1]
  exact (bitLenMatAny_fromRows_le Aᵀ Bᵀ).trans
    (Nat.add_le_add (bitLenMatAny_transpose_le A) (bitLenMatAny_transpose_le B))

/-! ## 4.  The payoff: the pair matrix `[N | A * N]` -/

/-- **The pair matrix `[N | A * N]`** (general finite index types): concatenating a matrix
with its image under `A` costs at most one extra copy of `bitLenMatAny N`, one copy of
`bitLenMatAny A`, and the `log` of the inner dimension `α` (the number of summands in an
entry of `A * N`).

The `log` term is not removable: `bitLenMatAny_mul_le` needs it (`1 × 4` times `4 × 1` of
ones gives `4`). -/
theorem bitLenMatAny_fromCols_mul_le {α γ : Type*} [Fintype α] [Fintype γ]
    (N : Matrix α γ ℚ) (A : Matrix α α ℚ) :
    bitLenMatAny (fromCols N (A * N)) ≤
      2 * bitLenMatAny N + bitLenMatAny A + (Fintype.card α + 1).size := by
  have h1 := bitLenMatAny_fromCols_le N (A * N)
  have h2 := bitLenMatAny_mul_le A N
  omega

/-- **The pair matrix `[N | A * N]`** (`Fin` form), with an explicit budget `t` for `N` and
`L` for `A`:

`bitLenMatAny [N | A*N] ≤ 2 * t + L + (n + 1).size`, where `t` bounds `bitLenMat N`, `L`
bounds `bitLenMat A`, and `n` is the number of rows of `N` (the inner dimension of `A * N`).
So the concatenation roughly doubles the bit length of the kernel basis plus the bit length
of `A`, up to the additive `log` term `(n + 1).size ≤ n + 1`. -/
theorem bitLenMatAny_pairMatrix_le {n k t L : ℕ}
    (N : Matrix (Fin n) (Fin k) ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (hN : bitLenMat N ≤ t) (hA : bitLenMat A ≤ L) :
    bitLenMatAny (fromCols N (A * N)) ≤ 2 * t + L + (n + 1).size := by
  have h := bitLenMatAny_fromCols_mul_le N A
  rw [Fintype.card_fin] at h
  have hN' : bitLenMatAny N ≤ t := by simpa [bitLenMatAny_eq_bitLenMat] using hN
  have hA' : bitLenMatAny A ≤ L := by simpa [bitLenMatAny_eq_bitLenMat] using hA
  omega

/-- **The payoff in the paper's shape**, for Mathlib's `Matrix.fromCols`: the matrix
`N.fromCols (A * N)` has bit length at most `2 * t + L + (n + 1).size`. -/
theorem bitLenMatAny_pairMatrix_le' {n k t L : ℕ}
    (N : Matrix (Fin n) (Fin k) ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (hN : bitLenMat N ≤ t) (hA : bitLenMat A ≤ L) :
    bitLenMatAny (Matrix.fromCols N (A * N)) ≤ 2 * t + L + (n + 1).size := by
  have h1 := bitLenMatAny_matrixFromCols_le N (A * N)
  have h2 := bitLenMatAny_mul_le A N
  rw [Fintype.card_fin] at h2
  have hN' : bitLenMatAny N ≤ t := by simpa [bitLenMatAny_eq_bitLenMat] using hN
  have hA' : bitLenMatAny A ≤ L := by simpa [bitLenMatAny_eq_bitLenMat] using hA
  omega

end Q1Paper.PaperI
