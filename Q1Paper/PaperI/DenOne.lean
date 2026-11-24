
import Q1Paper.PaperI.CompressedGram

/-!
Q1Paper/PaperI/DenOne.lean

**Discharging the integrality hypothesis `hint` of
`Q1Paper.PaperI.windowGram_entry_bitLen_le`.**

`PaperI/CompressedGram.lean` proves the sharp bit-length bound for the entries of
the window Gram matrix `Zᵀ Z` under two hypotheses:

* `hint : ∀ a b, (coeffGram P ω a b).den = 1` — every coefficient of the
  coefficient Gram form is an integer;
* `hS : ∀ a b, bitLenInt ((coeffGram P ω a b).num) ≤ b` — magnitude bound.

The file itself notes (§5) that `hint` "is *not* derived here from an integrality
hypothesis on `P`; that derivation belongs to the `coeffGram` layer", and that the
denominator fact `(windowGram P ω t t').den = 1` "is not stated below".

This file does exactly that, for the integrality hypothesis that matters in
Paper I: `P` has **integer entries** (or, more generally, integer polynomial
entries).  The mathematical content is one sentence — the maximal minors of a
matrix with integer entries are integer polynomials, hence so are all
coefficients of the coefficient Gram form — but its formalisation needs:

1. `poly_coeff_int_den_eq_one` : a coefficient of an integer polynomial, cast to
   `ℚ`, has denominator `1` (`Rat.den_intCast`);
2. `det_int_den_eq_one`, `det_int_coeff_den_eq_one` : determinants over `ℤ`
   remain integral after casting, and the coefficients of the determinant of a
   matrix of integer polynomials are integers — via `RingHom.map_det`
   (`det (A.map f) = f (det A)`) and `Polynomial.coeff_map`;
3. `intMaximalMinor`, `intMinorCoeff` : the integer-side mirrors of
   `maximalMinor` and `minorCoeff` (the library definitions carry a `[Field K]`
   instance, so they cannot be instantiated at `K = ℤ`);
4. `maximalMinor_map_intToRatPoly`, `minorCoeff_eq_intCast` : the minors and
   their coefficients commute with the coefficientwise map `ℤ[X] → ℚ[X]`, so
   each `minorCoeff` over `ℚ` is the cast of an integer;
5. `coeffGram_eq_intCoeffGram` : the double sum of products is the cast of the
   corresponding integer double sum;
6. `coeffGram_den_eq_one_intPoly` / `coeffGram_den_eq_one` / `coeffGram_den_eq_one_all` :
   the hypothesis `hint` of `windowGram_entry_bitLen_le`, discharged;
7. `windowGram_den_eq_one` : the denominator statement noted as missing in
   `CompressedGram.lean` §5;
8. `windowGram_entry_bitLen_le_of_int` : the final corollary — the bit-length
   bound of `windowGram_entry_bitLen_le` with `hint` **discharged**, the only
   hypothesis on `P` being that its entries are integer polynomials.

No `sorry`, no `admit`, no new axioms.  Everything lives in
`namespace Q1Paper.PaperI`.  Check with
  `lake env lean Q1Paper/PaperI/DenOne.lean`.
-/


open Matrix Polynomial
open scoped BigOperators

namespace Q1Paper.PaperI

/-! ## 1.  Coefficients of integer polynomials -/

/-- **The coefficient of `X^d` in an integer polynomial is an integer**, so its
cast to `ℚ` has denominator `1`.  This is the generic "integer ⟹ `den = 1`"
bridge used for every coefficient below. -/
theorem poly_coeff_int_den_eq_one (f : Polynomial ℤ) (d : ℕ) :
    (((f.coeff d : ℤ) : ℚ)).den = 1 :=
  Rat.den_intCast (f.coeff d)

/-! ## 2.  Determinants of integer matrices -/

/-- **The determinant of an integer matrix, viewed in `ℚ`, has denominator
`1`**: `det` of a matrix over `ℤ` is an integer (`Int` is a ring), and the cast
of an integer has `den = 1`. -/
theorem det_int_den_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) : ((A.det : ℚ)).den = 1 :=
  Rat.den_intCast A.det

/-- The coefficientwise reduction `ℤ[X] → ℚ[X]` (`Int.cast` on coefficients), as
a ring homomorphism.  It is the map along which integrality of `P` is
transported. -/
noncomputable def intToRatPoly : Polynomial ℤ →+* Polynomial ℚ :=
  Polynomial.mapRingHom (Int.castRingHom ℚ)

/-- `intToRatPoly` is `Polynomial.map` of `ℤ → ℚ` (definitional). -/
theorem intToRatPoly_eq_map (p : Polynomial ℤ) :
    intToRatPoly p = p.map (Int.castRingHom ℚ) := rfl

/-- **Coefficients of the reduction**: the `d`-th coefficient of `intToRatPoly p`
is the cast of the `d`-th coefficient of `p`. -/
theorem coeff_intToRatPoly (p : Polynomial ℤ) (d : ℕ) :
    (intToRatPoly p).coeff d = ((p.coeff d : ℤ) : ℚ) := by
  rw [intToRatPoly_eq_map, Polynomial.coeff_map]
  rfl

/-- **`det` commutes with the coefficientwise reduction** (a special case of
`RingHom.map_det`). -/
theorem det_map_intToRatPoly {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (Polynomial ℤ)) :
    (A.map intToRatPoly).det = intToRatPoly A.det :=
  (RingHom.map_det intToRatPoly A).symm

/-- **The coefficients of the determinant of a matrix of integer polynomials are
integers.**  This is the "determinant + coefficient" principle: `det` over
`ℤ[X]` is an integer polynomial, and every coefficient of an integer polynomial
has `den = 1` after casting to `ℚ`. -/
theorem det_int_coeff_den_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (Polynomial ℤ)) (d : ℕ) :
    (((A.map intToRatPoly).det).coeff d).den = 1 := by
  rw [det_map_intToRatPoly, coeff_intToRatPoly]
  exact poly_coeff_int_den_eq_one A.det d

/-! ## 3.  Maximal minors and their coefficients over `ℤ` -/

/-- The **`ω × ω` minor of an integer polynomial matrix**: the determinant of the
submatrix selected by `(r, c)`, taken over `ℤ[X]`.  This is the integer-side
mirror of `maximalMinor` (which requires `[Field K]` and hence cannot be
instantiated at `K = ℤ`). -/
noncomputable def intMaximalMinor {m n : Type*} (P : Matrix m n (Polynomial ℤ))
    {ω : ℕ} (r : Fin ω → m) (c : Fin ω → n) : Polynomial ℤ :=
  (P.submatrix r c).det

/-- **`maximalMinor` over `ℚ` is the reduction of `intMaximalMinor` over `ℤ`.** -/
theorem maximalMinor_map_intToRatPoly {m n : Type*} (P : Matrix m n (Polynomial ℤ))
    {ω : ℕ} (r : Fin ω → m) (c : Fin ω → n) :
    maximalMinor (P.map intToRatPoly) r c = intToRatPoly (intMaximalMinor P r c) := by
  unfold maximalMinor intMaximalMinor
  have h : (P.map intToRatPoly).submatrix r c
      = (P.submatrix r c).map intToRatPoly := rfl
  rw [h]
  exact (RingHom.map_det intToRatPoly (P.submatrix r c)).symm

/-- The **coefficient of `X^a` in the minor indexed by `(I, J)`**, taken over
`ℤ` (the integer-side mirror of `minorCoeff`). -/
noncomputable def intMinorCoeff {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) (Polynomial ℤ))
    (ω : ℕ) (a : ℕ) (I : Set.powersetCard (Fin q) ω)
    (J : Set.powersetCard (Fin ℓ) ω) : ℤ :=
  (intMaximalMinor P (rowEmb I) (colEmb J)).coeff a

/-- **Every coefficient of every maximal minor is an integer** (as an element of
`ℚ`): the coefficient `minorCoeff` over `ℚ` is the cast of `intMinorCoeff` over
`ℤ`. -/
theorem minorCoeff_eq_intCast {q ℓ ω : ℕ} (P : Matrix (Fin q) (Fin ℓ) (Polynomial ℤ))
    (a : ℕ) (I : Set.powersetCard (Fin q) ω) (J : Set.powersetCard (Fin ℓ) ω) :
    minorCoeff (P.map intToRatPoly) ω a I J = ((intMinorCoeff P ω a I J : ℤ) : ℚ) := by
  unfold minorCoeff intMinorCoeff
  rw [maximalMinor_map_intToRatPoly, coeff_intToRatPoly]

/-! ## 4.  The coefficient Gram form of an integer polynomial matrix -/

/-- The **integral coefficient Gram form**:
`S_{a,b} = ∑_{I,J} c_{I,J,a} c_{I,J,b}` computed over `ℤ`.  Each `intMinorCoeff`
is an integer, and this is their double sum of products. -/
noncomputable def intCoeffGram {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) (Polynomial ℤ))
    (ω a b : ℕ) : ℤ :=
  ∑ I : Set.powersetCard (Fin q) ω, ∑ J : Set.powersetCard (Fin ℓ) ω,
    intMinorCoeff P ω a I J * intMinorCoeff P ω b I J

/-- **`coeffGram` over `ℚ` is the cast of `intCoeffGram` over `ℤ`.**  This is the
integrality statement in its strongest form: not merely that the denominators are
`1`, but that the value *is* an explicit integer. -/
theorem coeffGram_eq_intCoeffGram {q ℓ ω : ℕ}
    (P : Matrix (Fin q) (Fin ℓ) (Polynomial ℤ)) (a b : ℕ) :
    coeffGram (P.map intToRatPoly) ω a b = ((intCoeffGram P ω a b : ℤ) : ℚ) := by
  simp only [coeffGram, intCoeffGram, minorCoeff_eq_intCast]
  push_cast
  rfl

/-- **The numerator of `coeffGram` is `intCoeffGram`** (so the bit-length
hypothesis `hS` of `windowGram_entry_bitLen_le` can be stated on integers). -/
theorem intCoeffGram_num {q ℓ ω : ℕ} (P : Matrix (Fin q) (Fin ℓ) (Polynomial ℤ))
    (a b : ℕ) :
    (coeffGram (P.map intToRatPoly) ω a b).num = intCoeffGram P ω a b := by
  rw [coeffGram_eq_intCoeffGram, Rat.num_intCast]

/-! ## 5.  The hypothesis `hint`, discharged -/

/-- **`hint` for integer polynomial matrices.**  If `P` has integer polynomial
entries, every coefficient of its maximal minors is an integer, hence every
coefficient `S_{a,b}` of the coefficient Gram form has denominator `1`. -/
theorem coeffGram_den_eq_one_intPoly {q ℓ ω : ℕ}
    (P : Matrix (Fin q) (Fin ℓ) (Polynomial ℤ)) (a b : ℕ) :
    (coeffGram (P.map intToRatPoly) ω a b).den = 1 := by
  rw [coeffGram_eq_intCoeffGram]
  exact Rat.den_intCast _

/-- **`hint`, discharged from integrality of the input matrix `P`.**  If `P` is a
matrix with integer entries (regarded as constant polynomials in `ℚ[X]`), then
every coefficient of every maximal minor of the pencil is an integer, and the
coefficient Gram form is integral:

  `(coeffGram (P.map (Int.cast : ℤ → ℚ[X])) ω a b).den = 1`.

The codomain of `Int.cast` is `ℚ[X]` (a matrix over `ℤ` must land in `ℚ[X]`
before `coeffGram` applies) rather than `ℚ`. -/
theorem coeffGram_den_eq_one {q ℓ ω : ℕ} (P : Matrix (Fin q) (Fin ℓ) ℤ) (a b : ℕ) :
    (coeffGram (P.map (fun z : ℤ => (z : ℚ[X]))) ω a b).den = 1 := by
  have h : P.map (fun z : ℤ => (z : ℚ[X]))
      = (P.map (fun z : ℤ => Polynomial.C z)).map intToRatPoly := by
    funext i j
    simp [intToRatPoly]
  rw [h]
  exact coeffGram_den_eq_one_intPoly _ a b

/-- **`hint`, discharged, in the exact shape taken by
`windowGram_entry_bitLen_le`**: for `P` with integer polynomial entries,
`∀ a b, (coeffGram P ω a b).den = 1`. -/
theorem coeffGram_den_eq_one_all {q ℓ ω : ℕ}
    (P : Matrix (Fin q) (Fin ℓ) (Polynomial ℤ)) :
    ∀ a b, (coeffGram (P.map intToRatPoly) ω a b).den = 1 :=
  fun a b => coeffGram_den_eq_one_intPoly P a b

/-! ## 6.  The missing denominator statement for the window Gram -/

/-- **Every entry of the window Gram matrix is an integer.**  This is the
denominator fact noted as missing in `CompressedGram.lean` §5 (it is what a
`bitLenRat` version of the bound would need).  It follows from
`windowGram_eq_compressed`, `compressedGram_entry_eq_intCast` and the integrality
of `coeffGram`. -/
theorem windowGram_den_eq_one {q ℓ ω : ℕ} (P : Matrix (Fin q) (Fin ℓ) (Polynomial ℤ))
    (t t' : Fin (2 * ω)) :
    (windowGram (P.map intToRatPoly) ω t t').den = 1 := by
  have h1 : windowGram (P.map intToRatPoly) ω t t'
      = compressedGram (P.map intToRatPoly) ω t t' := by
    unfold windowGram
    rw [windowGram_eq_compressed]
  rw [h1, compressedGram_entry_eq_intCast _ ω (coeffGram_den_eq_one_all P) t t',
    Rat.den_intCast]

/-! ## 7.  The final corollary: `windowGram_entry_bitLen_le` without `hint` -/

/-- **The window-Gram bit-length bound with the integrality hypothesis
discharged.**  For `P` with integer polynomial entries and integer coefficient
Gram numerators of bit length at most `b` (`hS`, now stated on the *integer*
`intCoeffGram`, so no rational data occurs), every entry of `Zᵀ Z` has numerator
bit length at most `b + ω.size`.

This is `windowGram_entry_bitLen_le` with `hint` supplied by
`coeffGram_den_eq_one_all`; the only hypothesis on `P` is integrality of its
entries. -/
theorem windowGram_entry_bitLen_le_of_int {q ℓ ω : ℕ}
    (P : Matrix (Fin q) (Fin ℓ) (Polynomial ℤ)) {b : ℕ}
    (hS : ∀ a b', bitLenInt (intCoeffGram P ω a b') ≤ b) (t t' : Fin (2 * ω)) :
    bitLenInt ((windowGram (P.map intToRatPoly) ω t t').num) ≤ b + ω.size := by
  refine windowGram_entry_bitLen_le (P.map intToRatPoly) ω
    (coeffGram_den_eq_one_all P) ?_ t t'
  intro a b'
  rw [intCoeffGram_num]
  exact hS a b'

/-- The cruder form `2 * b + (2 * ω).size + 1` of
`windowGram_entry_bitLen_le_of_int`. -/
theorem windowGram_entry_bitLen_le_of_int_two_mul_add {q ℓ ω : ℕ}
    (P : Matrix (Fin q) (Fin ℓ) (Polynomial ℤ)) {b : ℕ}
    (hS : ∀ a b', bitLenInt (intCoeffGram P ω a b') ≤ b) (t t' : Fin (2 * ω)) :
    bitLenInt ((windowGram (P.map intToRatPoly) ω t t').num)
      ≤ 2 * b + (2 * ω).size + 1 := by
  have h := windowGram_entry_bitLen_le_of_int P hS t t'
  have hω : ω.size ≤ (2 * ω).size := Nat.size_le_size (by omega)
  omega

end Q1Paper.PaperI
