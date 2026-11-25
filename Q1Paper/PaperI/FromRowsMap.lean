import Q1Paper.PaperI.ChartComplete

/-! # `fromRows` commutes with `map`

The blocking lemma of the previous round: `fromRows` produces a matrix indexed by a `Sum`, and
mapping a function over its entries should equal stacking the mapped blocks.  It is a case split on
the `Sum` index — the earlier attempts failed only because they used `Fin.addCases` on a type that is
a `Sum`, not a `Fin`. -/

namespace Q1Paper.PaperI.FromRowsMap

open Q1Paper Q1Subspace

variable {R S : Type*} [Semiring R] [Semiring S]
variable {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂] {n : Type*} [Fintype n]

/-- **`fromRows` commutes with `map`.** -/
theorem fromRows_map (f : R → S) (A : Matrix m₁ n R) (B : Matrix m₂ n R) :
    (Matrix.fromRows A B).map f = Matrix.fromRows (A.map f) (B.map f) := by
  ext i j
  cases i with
  | inl a => rfl
  | inr b => rfl

end Q1Paper.PaperI.FromRowsMap
