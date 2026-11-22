/-
Port of the square Cauchy-Binet identity.

Source: Ralf Stephan, rwst/Subspace-Theorems, files
ArithmeticHeights/Plucker.lean, ArithmeticHeights/RowSpace.lean and
ArithmeticHeights/CauchyBinet.lean (Apache-2.0, see the LICENSE of that
repository).  Adapted for this project: the module system and the
public/[expose] annotations are removed, and only the declarations needed
for det_mul_eq_sum_det_submatrix are kept.

Main result: for a commutative ring R,
det (A * B) = sum over s : Set.powersetCard iota m of
   det (A.submatrix id (orderEmbOfFin s)) * det (B.submatrix (orderEmbOfFin s) id).
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace exteriorPower

open Matrix Module

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The **Plücker coordinates** of a family `v : Fin k → (ι → R)`: the coordinate tuple of the
wedge `v 0 ∧ ⋯ ∧ v (k-1)` in the basis of `⋀[R]^k (ι → R)` induced by the standard basis of
`ι → R`, indexed by the `k`-element subsets of `ι`. -/
noncomputable def plucker (k : ℕ) (v : Fin k → (ι → R)) : Set.powersetCard ι k → R :=
  ((Pi.basisFun R ι).exteriorPower k).equivFun (ιMulti R k v)

/-- **The Plücker coordinates are the maximal minors.** The coordinate at a `k`-element subset `s`
of `ι` is the determinant of the `k × k` matrix cut out of the rows `v` by the columns `s`, the
columns taken in the order of `ι`. -/
theorem plucker_apply (k : ℕ) (v : Fin k → (ι → R)) (s : Set.powersetCard ι k) :
    plucker k v s = (Matrix.of fun i j ↦ v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det := by
  rw [plucker, Basis.equivFun_apply, basis_repr_apply, ιMultiDual_apply_ιMulti]
  simp

/-!
### The identity in Plücker coordinates
-/

section Dual

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The dual map of the standard basis is the dot product.** Mathlib's `Basis.toDual_apply_left`
evaluates `b.toDual x` on a basis vector; for the standard basis of `ι → R` the value on an
arbitrary vector is the dot product. -/
theorem _root_.Pi.basisFun_toDual_apply (x y : ι → R) :
    (Pi.basisFun R ι).toDual x y = x ⬝ᵥ y := by
  conv_lhs => rw [← (Pi.basisFun R ι).sum_repr y]
  rw [map_sum]
  simp only [map_smul, Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

end Dual

section Basis

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [LinearOrder ι]

/-- The pairing against the image of a basis vector of `⋀^k (ι → R)` reads off a coordinate: this
is `exteriorPower.ιMultiDual` unfolded, since that functional is *defined* as the pairing against
the wedge of the dual basis vectors indexed by `s`. -/
private lemma pairingDual_map_toDual_basis (k : ℕ) (s : Set.powersetCard ι k)
    (y : ⋀[R]^k (ι → R)) :
    pairingDual R (ι → R) k
        (map k (Pi.basisFun R ι).toDual ((Pi.basisFun R ι).exteriorPower k s)) y
      = ((Pi.basisFun R ι).exteriorPower k).repr y s := by
  rw [basis_apply, map_apply_ιMulti_family,
    show (Pi.basisFun R ι).toDual ∘ (Pi.basisFun R ι) = (Pi.basisFun R ι).coord from
      funext fun i ↦ Basis.coe_toDual_self _ i, basis_repr_apply]
  rfl

end Basis

section CauchyBinet

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}

/-- On the basis of `⋀^k (ι → R)` induced by the standard basis, the bilinear form obtained by
pairing along `Basis.toDual` is the diagonal one. -/
private lemma pairingDual_map_toDual (k : ℕ) (x y : ⋀[R]^k (ι → R)) :
    pairingDual R (ι → R) k (map k (Pi.basisFun R ι).toDual x) y
      = ∑ s : Set.powersetCard ι k, ((Pi.basisFun R ι).exteriorPower k).repr x s *
          ((Pi.basisFun R ι).exteriorPower k).repr y s := by
  conv_lhs => rw [← ((Pi.basisFun R ι).exteriorPower k).sum_repr x]
  rw [map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_smul, map_smul, LinearMap.smul_apply, pairingDual_map_toDual_basis, smul_eq_mul]

/-- **The Cauchy–Binet identity.** The sum over the `k`-element sets of columns of the product of
the two Plücker coordinates is the determinant of the `k × k` matrix of dot products. Over any
commutative ring, and with no hypothesis on either family. -/
theorem sum_plucker_mul_plucker (k : ℕ) (v w : Fin k → (ι → R)) :
    ∑ s : Set.powersetCard ι k, plucker k v s * plucker k w s
      = (Matrix.of fun i j ↦ v i ⬝ᵥ w j).det := by
  have h := pairingDual_map_toDual k (ιMulti R k v) (ιMulti R k w)
  rw [map_apply_ιMulti, pairingDual_ιMulti_ιMulti] at h
  simp only [plucker, Basis.equivFun_apply]
  rw [← h]
  simp only [Function.comp_apply, Pi.basisFun_toDual_apply]
  rw [← Matrix.det_transpose (Matrix.of fun i j ↦ v i ⬝ᵥ w j)]
  rfl

/-- **The Plücker coordinates commute with a ring homomorphism**, each being a determinant. This is
what carries the identity along an embedding of a number field into `ℂ`. -/
theorem plucker_map {S : Type*} [CommRing S] (f : R →+* S) (k : ℕ) (v : Fin k → (ι → R))
    (s : Set.powersetCard ι k) : plucker k (fun i ↦ f ∘ v i) s = f (plucker k v s) := by
  rw [plucker_apply, plucker_apply, RingHom.map_det]
  rfl

end CauchyBinet

end exteriorPower

namespace Matrix

open Module exteriorPower

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- **The Plücker coordinates of a matrix are its maximal minors.** The coordinate at a set `s` of
`m` columns is the determinant of the submatrix on those columns, enumerated in increasing order.
The enumeration is Mathlib's `Finset.orderEmbOfFin`, the one `Set.powersetCard.ofFinEmbEquiv`
already fixes, so no later statement has to choose it again. -/
theorem plucker_row_eq_det_submatrix (A : Matrix (Fin m) ι R) (s : Set.powersetCard ι m) :
    plucker m A.row s =
      (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [plucker_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rfl

section CauchyBinet

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- The Plücker coordinates of the rows commute with a ring homomorphism applied entrywise. -/
theorem plucker_row_map {S : Type*} [CommRing S] (f : R →+* S) (A : Matrix (Fin m) ι R)
    (s : Set.powersetCard ι m) : plucker m (A.map f).row s = f (plucker m A.row s) :=
  plucker_map f m A.row s

/-- **The Cauchy–Binet identity**, for `A Bᵀ`: the determinant of the matrix of dot products of the
rows of `A` with the rows of `B` is the sum over the sets of `m` columns of the products of
corresponding maximal minors. -/
theorem det_mul_transpose_eq_sum_plucker (A B : Matrix (Fin m) ι R) :
    (A * Bᵀ).det = ∑ s : Set.powersetCard ι m, plucker m A.row s * plucker m B.row s :=
  (sum_plucker_mul_plucker m A.row B.row).symm

/-- **The Cauchy–Binet identity**, for a product `A B` of an `m × ι` by an `ι × m` matrix: the
determinant is the sum over the sets of `m` indices of the product of the maximal minor of `A` on
those columns with the maximal minor of `B` on those rows. -/
theorem det_mul_eq_sum_plucker (A : Matrix (Fin m) ι R) (B : Matrix ι (Fin m) R) :
    (A * B).det = ∑ s : Set.powersetCard ι m, plucker m A.row s * plucker m B.col s := by
  conv_lhs => rw [← Matrix.transpose_transpose B]
  exact (sum_plucker_mul_plucker m A.row Bᵀ.row).symm

/-- The Cauchy–Binet identity in the `submatrix` spelling of Layer 3.3: the minors are taken on the
columns of `s`, enumerated in increasing order. -/
theorem det_mul_transpose_eq_sum_det_submatrix (A B : Matrix (Fin m) ι R) :
    (A * Bᵀ).det = ∑ s : Set.powersetCard ι m,
      (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det *
        (B.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [det_mul_transpose_eq_sum_plucker]
  exact Finset.sum_congr rfl fun s _ ↦ by
    rw [plucker_row_eq_det_submatrix, plucker_row_eq_det_submatrix]

/-- The Cauchy–Binet identity for `A B` in the `submatrix` spelling: the maximal minors of `A` on
the columns of `s` against those of `B` on the rows of `s`. -/
theorem det_mul_eq_sum_det_submatrix (A : Matrix (Fin m) ι R) (B : Matrix ι (Fin m) R) :
    (A * B).det = ∑ s : Set.powersetCard ι m,
      (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det *
        (B.submatrix ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s)) id).det := by
  rw [det_mul_eq_sum_plucker]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [plucker_row_eq_det_submatrix, show B.col = Bᵀ.row from rfl, plucker_row_eq_det_submatrix,
    ← Matrix.det_transpose (B.submatrix _ id), Matrix.transpose_submatrix]

end CauchyBinet

end Matrix
