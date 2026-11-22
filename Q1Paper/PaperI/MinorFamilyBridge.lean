/-
Q1Paper/PaperI/MinorFamilyBridge.lean

D1 bridge between the two index families of maximal minors:

* `minorFamily` (Claim 11/12): indexed by pairs of *injective maps*
  `Fin ω → Fin q` and `Fin ω → Fin k`;
* `windowMinorFamily` (§III-D): indexed by pairs of *subsets*
  `Set.powersetCard (Fin q) ω × Set.powersetCard (Fin k) ω`.

Each subset pair occurs in the injective family exactly `(ω!)²` times, with the
sign of the reordering; hence the two window matrices have the same row space and
Gram matrices differing by the positive factor `(ω!)²`.

This file starts the bridge with the scalar determinant identity: permuting the
rows and columns of an `ω × ω` matrix multiplies its determinant by the product
of the two signs.
-/

import Q1Paper.PaperI.GramCompression

namespace Q1Paper.PaperI

open Matrix

variable {K : Type*} [Field K]

/-- **Determinant under row/column permutations.** -/
theorem det_submatrix_perm {ω : ℕ} (σ τ : Equiv.Perm (Fin ω))
    (M : Matrix (Fin ω) (Fin ω) K) :
    (M.submatrix σ τ).det =
      (Equiv.Perm.sign σ : K) * (Equiv.Perm.sign τ : K) * M.det := by
  have h : M.submatrix σ τ = (M.submatrix σ id).submatrix id τ := by
    rw [Matrix.submatrix_submatrix]
    rfl
  rw [h, Matrix.det_permute', Matrix.det_permute]
  ring

end Q1Paper.PaperI
