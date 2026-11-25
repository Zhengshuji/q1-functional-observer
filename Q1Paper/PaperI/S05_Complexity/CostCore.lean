
import Q1Paper.PaperI.S04_Rationality.BitLenAdd

/-!
Q1Paper/PaperI/S05_Complexity/CostCore.lean

A **minimal cost model** for the paper's complexity formalisation, with all costs
*derived from the actual data* rather than supplied by the caller.

Contents
========
1. `Cost` — the two-component cost monoid `⟨algorithmic steps, bit operations⟩`
   and its algebra (`zero_add`, `add_assoc`, `add_comm`, `scale_add`, ...).
2. `Op` / `bitOpCost` — schoolbook integer-operation costs
   (`add ↦ a+b+1`, `mul ↦ a*b`, `div ↦ (a+b+1)^2`, `compare ↦ max a b + 1`,
   `gcd ↦ (max a b + 1)^2`) together with monotonicity in both bit lengths.
3. `FieldOp` / `fieldOpBitCost` — the abstract polynomial envelope; on the
   rational side `ratBitCost`, computed from an actual rational representation
   (numerator/denominator sizes of `p` and `q`, the exact integers produced by a
   schoolbook cross-multiplication, and the gcd + exact division that reduces the
   naive fraction).  Theorem `ratBitCost_le_fieldOpBitCost` shows the envelope
   dominates the derived cost; `fieldOpBitCost_not_lower_bound` shows that the
   converse inequality *fails* (with an explicit rational witness), so it cannot
   be proved.
4. `Primitive` — `fieldOp` (carried constant operands), `fieldOpMix` (one operand
   read from the state, one carried constant, result stored in the state),
   `readCell`, `writeCell`; `primitiveCost` is a function of the *values* (`p`,
   `q`, or the state contents) and `evalPrimitive` is a real state semantics.
5. `Prog` — `pure`, `read`, `write`, `primitive`, `bind`, `forFin`; `run` returns
   the final state, the value and the `Cost`.  Since `bind`'s continuation is a
   genuine function `α → Prog σ β`, the interpreter is defined by well-founded
   recursion on the syntactic size `Prog.size`; see the note at `Prog.bind`.
6. Decomposition theorems: `run_bind` (cost additive), `run_forFin` (the loop cost
   is exactly the sum over the iterations, the state threaded through `statesOf`),
   `run_alg_eq_primitiveCount`, `run_bit_le_sum`.
7. A worked example: a `forFin` loop adding `n` rationals held in memory, with its
   final state and its cost computed by `simp`.

No `sorry`, no new axioms.  Check with
`lake env lean Q1Paper/PaperI/CostCore.lean`.
-/


open Q1Paper.PaperI

namespace Q1Complexity

/-! ## 1.  The cost monoid -/

/-- A cost has two components: `alg` counts *algorithmic* steps (field
operations, reads and writes actually executed) and `bit` counts *bit*
operations.  Neither component is supplied by the caller: both are produced by
`run` from the values the program manipulates. -/
structure Cost where
  alg : ℕ
  bit : ℕ
  deriving DecidableEq, Repr

namespace Cost

/-- The zero cost. -/
def zero : Cost := ⟨0, 0⟩

/-- Componentwise addition of costs. -/
def add (x y : Cost) : Cost := ⟨x.alg + y.alg, x.bit + y.bit⟩

/-- `k`-fold scaling of a cost. -/
def scale (k : ℕ) (x : Cost) : Cost := ⟨k * x.alg, k * x.bit⟩

instance : Zero Cost := ⟨zero⟩
instance : Add Cost := ⟨add⟩

@[simp] theorem zero_alg : (0 : Cost).alg = 0 := rfl
@[simp] theorem zero_bit : (0 : Cost).bit = 0 := rfl
@[simp] theorem add_alg (x y : Cost) : (x + y).alg = x.alg + y.alg := rfl
@[simp] theorem add_bit (x y : Cost) : (x + y).bit = x.bit + y.bit := rfl
@[simp] theorem scale_alg (k : ℕ) (x : Cost) : (scale k x).alg = k * x.alg := rfl
@[simp] theorem scale_bit (k : ℕ) (x : Cost) : (scale k x).bit = k * x.bit := rfl

@[ext] theorem ext {x y : Cost} (h1 : x.alg = y.alg) (h2 : x.bit = y.bit) : x = y := by
  cases x; cases y; simp_all

theorem zero_add (x : Cost) : 0 + x = x := by ext <;> simp
theorem add_zero (x : Cost) : x + 0 = x := by ext <;> simp
theorem add_assoc (x y z : Cost) : x + y + z = x + (y + z) := by
  ext <;> simp [Nat.add_assoc]
theorem add_comm (x y : Cost) : x + y = y + x := by ext <;> simp [Nat.add_comm]
theorem add_left_comm (x y z : Cost) : x + (y + z) = y + (x + z) := by
  rw [← add_assoc, add_comm x y, add_assoc]
theorem scale_zero (k : ℕ) : scale k 0 = 0 := by ext <;> simp
theorem scale_one (x : Cost) : scale 1 x = x := by ext <;> simp
theorem scale_add (k : ℕ) (x y : Cost) : scale k (x + y) = scale k x + scale k y := by
  ext <;> simp [Nat.mul_add]
theorem scale_scale (k l : ℕ) (x : Cost) : scale k (scale l x) = scale (k * l) x := by
  ext <;> simp [Nat.mul_assoc]
theorem scale_add' (k l : ℕ) (x : Cost) : scale (k + l) x = scale k x + scale l x := by
  ext <;> simp [Nat.add_mul]

end Cost

/-! ## 2.  Integer operations and their schoolbook cost -/

/-- Integer operations, each carrying the *bit lengths* of its operands. -/
inductive Op where
  /-- Addition of two integers of the given bit lengths. -/
  | add (a b : ℕ)
  /-- Multiplication of two integers of the given bit lengths. -/
  | mul (a b : ℕ)
  /-- Division with remainder of two integers of the given bit lengths. -/
  | div (a b : ℕ)
  /-- Comparison of two integers of the given bit lengths. -/
  | compare (a b : ℕ)
  /-- Greatest common divisor of two integers of the given bit lengths. -/
  | gcd (a b : ℕ)
  deriving DecidableEq, Repr

namespace Op

/-- Rebuild an operation with new operand bit lengths. -/
def withSizes : Op → ℕ → ℕ → Op
  | .add _ _, a, b => .add a b
  | .mul _ _, a, b => .mul a b
  | .div _ _, a, b => .div a b
  | .compare _ _, a, b => .compare a b
  | .gcd _ _, a, b => .gcd a b

end Op

/-- Schoolbook bit-operation count.  The `gcd` entry is the classical `O(n²)`
bound for the Euclidean algorithm on `n`-bit inputs (the operands shrink
geometrically, so the sum of the division costs is dominated by the first). -/
def bitOpCost : Op → ℕ
  | .add a b => a + b + 1
  | .mul a b => a * b
  | .div a b => (a + b + 1) ^ 2
  | .compare a b => max a b + 1
  | .gcd a b => (max a b + 1) ^ 2

/-- Every integer operation is monotone in both operand bit lengths. -/
theorem bitOpCost_mono (op : Op) {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    bitOpCost (op.withSizes a b) ≤ bitOpCost (op.withSizes a' b') := by
  cases op with
  | add x y =>
      simpa [Op.withSizes, bitOpCost] using Nat.add_le_add ha hb
  | mul x y =>
      simpa [Op.withSizes, bitOpCost] using Nat.mul_le_mul ha hb
  | div x y =>
      simpa [Op.withSizes, bitOpCost] using
        Nat.pow_le_pow_left (by omega : a + b + 1 ≤ a' + b' + 1) 2
  | compare x y =>
      simpa [Op.withSizes, bitOpCost] using Nat.add_le_add_right (max_le_max ha hb) 1
  | gcd x y =>
      simpa [Op.withSizes, bitOpCost] using
        Nat.pow_le_pow_left (by omega : max a b + 1 ≤ max a' b' + 1) 2

/-! ## 3.  Field operations: abstract envelope and derived cost -/

/-- Field operations on rational numbers. -/
inductive FieldOp where
  | add
  | sub
  | mul
  | div
  | inv
  deriving DecidableEq, Repr

/-- Abstract polynomial envelope for one field operation on operands of the
given bit lengths.  The constants are chosen generously: the point of
`ratBitCost_le_fieldOpBitCost` is that *some* explicit polynomial dominates the
cost actually incurred, not that these constants are tight.

Each entry is `read + 64 * (schoolbook size)²`, where `read` is the cost of
reading the operands (`a + b`, or `a` for the unary `inv`) and the square covers
the arithmetic together with the gcd normalisation:

* `add`/`sub`: quadratic in `a + b`, because the schoolbook algorithm
  cross-multiplies and then reduces the resulting fraction by a gcd of two
  numbers of `a + b` bits.
* `mul`/`div`: quadratic in `a * b` for the same reason, applied to a fraction
  whose numerator and denominator both have about `a * b` bits.
* `inv`: only swaps numerator and denominator, hence the quadratic bound in `a`.

The constants are not tight; `64` is a comfortable margin (see
`ratBitCost_le_fieldOpBitCost`). -/
def fieldOpBitCost : FieldOp → ℕ → ℕ → ℕ
  | .add, a, b => a + b + 64 * (a + b + 1) ^ 2
  | .sub, a, b => a + b + 64 * (a + b + 1) ^ 2
  | .mul, a, b => a + b + 64 * (a * b + a + b + 1) ^ 2
  | .div, a, b => a + b + 64 * (a * b + a + b + 1) ^ 2
  | .inv, a, _ => a + 64 * (a + 1) ^ 2

/-! ### 3.1  Bit lengths of rationals: what we need beyond `BitLenAdd` -/

theorem bitLenRat_neg (q : ℚ) : bitLenRat (-q) = bitLenRat q := by
  unfold bitLenRat
  rw [Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, bitLenInt_neg]

/-- Inversion swaps numerator and denominator (up to sign), so it preserves the
input bit length exactly. -/
theorem bitLenRat_inv (q : ℚ) : bitLenRat q⁻¹ = bitLenRat q := by
  unfold bitLenRat
  rw [Rat.num_inv, Rat.den_inv]
  simp only [bitLenInt, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_sign]
  by_cases h : q.num = 0
  · have hq : q = 0 := Rat.num_eq_zero.mp h
    subst hq
    norm_num
  · simp only [h, ite_false, Nat.one_mul]
    omega

theorem bitLenRat_sub_le (p q : ℚ) : bitLenRat (p - q) ≤ 1 + bitLenRat p + bitLenRat q := by
  calc bitLenRat (p - q) = bitLenRat (p + -q) := by rw [sub_eq_add_neg]
    _ ≤ 1 + bitLenRat p + bitLenRat (-q) := bitLenRat_add p (-q)
    _ = 1 + bitLenRat p + bitLenRat q := by rw [bitLenRat_neg]

theorem bitLenRat_div_le (p q : ℚ) : bitLenRat (p / q) ≤ bitLenRat p + bitLenRat q := by
  calc bitLenRat (p / q) = bitLenRat (p * q⁻¹) := by rw [div_eq_mul_inv]
    _ ≤ bitLenRat p + bitLenRat q⁻¹ := bitLenRat_mul p q⁻¹
    _ = bitLenRat p + bitLenRat q := by rw [bitLenRat_inv]

/-- Bits of the numerator of a rational, as a plain integer bit length. -/
def numBits (q : ℚ) : ℕ := bitLenInt q.num

/-- Bits of the (reduced, positive) denominator of a rational. -/
def denBits (q : ℚ) : ℕ := q.den.size

theorem numBits_le_bitLenRat (q : ℚ) : numBits q ≤ bitLenRat q := le_max_left _ _
theorem denBits_le_bitLenRat (q : ℚ) : denBits q ≤ bitLenRat q := le_max_right _ _

/-- Bit length of a product of an integer by a natural number. -/
theorem bitLenInt_mul_natCast_le (a : ℤ) (b : ℕ) :
    bitLenInt (a * (b : ℤ)) ≤ bitLenInt a + b.size := by
  calc bitLenInt (a * (b : ℤ)) ≤ bitLenInt a + bitLenInt (b : ℤ) := bitLenInt_mul a (b : ℤ)
    _ = bitLenInt a + b.size := by rw [bitLenInt_natCast]

/-- Bit length of the naive numerator `a * d + c * b` of a cross-multiplication. -/
theorem bitLenInt_cross_add_le (a c : ℤ) (b d : ℕ) :
    bitLenInt (a * (b : ℤ) + c * (d : ℤ)) ≤ 1 + (bitLenInt a + b.size) + (bitLenInt c + d.size) := by
  have h1 := bitLenInt_mul_natCast_le a b
  have h2 := bitLenInt_mul_natCast_le c d
  have h3 := bitLenInt_add (a * (b : ℤ)) (c * (d : ℤ))
  omega

/-- Bit length of the naive numerator `a * d - c * b` of a cross-multiplication. -/
theorem bitLenInt_cross_sub_le (a c : ℤ) (b d : ℕ) :
    bitLenInt (a * (b : ℤ) - c * (d : ℤ)) ≤ 1 + (bitLenInt a + b.size) + (bitLenInt c + d.size) := by
  have h1 := bitLenInt_mul_natCast_le a b
  have h2 := bitLenInt_mul_natCast_le c d
  have h3 := bitLenInt_sub (a * (b : ℤ)) (c * (d : ℤ))
  omega

/-! ### 3.2  The cost derived from an actual rational representation -/

/-- Schoolbook cost of writing the fraction `n / d` in lowest terms: one gcd of
the *actual* integers, followed by the exact division of both parts.  The sizes
are those of the concrete integers produced by the operation, not a parameter. -/
def reduceWork (n : ℤ) (d : ℕ) : ℕ :=
  bitOpCost (.gcd (bitLenInt n) d.size) + bitOpCost (.div (bitLenInt n) d.size)

/-- Bit cost of `p + q`, computed from the representations of `p` and `q`. -/
def addWork (p q : ℚ) : ℕ :=
  (bitOpCost (.mul (numBits p) (denBits q)) + bitOpCost (.mul (numBits q) (denBits p)))
  + bitOpCost (.add (numBits p + denBits q) (numBits q + denBits p))
  + reduceWork (p.num * (q.den : ℤ) + q.num * (p.den : ℤ)) (p.den * q.den)
  + bitLenRat (p + q)

/-- Bit cost of `p - q`, computed from the representations of `p` and `q`. -/
def subWork (p q : ℚ) : ℕ :=
  (bitOpCost (.mul (numBits p) (denBits q)) + bitOpCost (.mul (numBits q) (denBits p)))
  + bitOpCost (.add (numBits p + denBits q) (numBits q + denBits p))
  + reduceWork (p.num * (q.den : ℤ) - q.num * (p.den : ℤ)) (p.den * q.den)
  + bitLenRat (p - q)

/-- Bit cost of `p * q`, computed from the representations of `p` and `q`. -/
def mulWork (p q : ℚ) : ℕ :=
  (bitOpCost (.mul (numBits p) (numBits q)) + bitOpCost (.mul (denBits p) (denBits q)))
  + reduceWork (p.num * q.num) (p.den * q.den)
  + bitLenRat (p * q)

/-- Bit cost of `p / q`: invert (a swap, already paid by reading `q`) and
multiply, i.e. cross-multiply `p.num * q.den` over `p.den * q.num`. -/
def divWork (p q : ℚ) : ℕ :=
  (bitOpCost (.mul (numBits p) (denBits q)) + bitOpCost (.mul (denBits p) (numBits q)))
  + reduceWork (p.num * (q.den : ℤ)) (p.den * q.num.natAbs)
  + bitLenRat (p / q)

/-- **The derived bit cost of a field operation.**  Every summand is computed
from `p` and `q` themselves: reading both operands, the schoolbook arithmetic on
their numerators and denominators, the gcd normalisation of the naive fraction
(with the sizes of the *actual* integer numerator and denominator), and writing
out the reduced result.  For `inv` the second operand is ignored (unary). -/
def ratBitCost : FieldOp → ℚ → ℚ → ℕ
  | .add, p, q => bitLenRat p + bitLenRat q + addWork p q
  | .sub, p, q => bitLenRat p + bitLenRat q + subWork p q
  | .mul, p, q => bitLenRat p + bitLenRat q + mulWork p q
  | .div, p, q => bitLenRat p + bitLenRat q + divWork p q
  | .inv, p, _ => bitLenRat p + bitLenRat p⁻¹

/-! ### 3.3  Arithmetic estimates -/

/-- `P * Q ≤ X ^ 2` when both `P` and `Q` are below `X`. -/
theorem mul_le_sq {P Q X : ℕ} (hP : P ≤ X) (hQ : Q ≤ X) : P * Q ≤ X ^ 2 := by
  calc P * Q ≤ X * X := Nat.mul_le_mul hP hQ
    _ = X ^ 2 := (pow_two X).symm

/-- Reducing the fraction `n / d` (a gcd, then the exact division of both parts)
costs at most `2 (A + B + 1)²` bit operations, where `A` bounds the bits of the
actual numerator and `B` those of the actual denominator. -/
theorem reduceWork_le (n : ℤ) (d : ℕ) (A B : ℕ) (hn : bitLenInt n ≤ A) (hd : d.size ≤ B) :
    reduceWork n d ≤ 2 * (A + B + 1) ^ 2 := by
  have h1 : bitOpCost (.gcd (bitLenInt n) d.size) ≤ (A + B + 1) ^ 2 := by
    have h := bitOpCost_mono (Op.gcd 0 0) hn hd
    simp only [Op.withSizes, bitOpCost] at h
    exact le_trans h (Nat.pow_le_pow_left (by omega) 2)
  have h2 : bitOpCost (.div (bitLenInt n) d.size) ≤ (A + B + 1) ^ 2 := by
    have h := bitOpCost_mono (Op.div 0 0) hn hd
    simp only [Op.withSizes, bitOpCost] at h
    exact le_trans h (Nat.pow_le_pow_left (by omega) 2)
  simp only [reduceWork]
  nlinarith

theorem addWork_le (p q : ℚ) :
    addWork p q ≤ 64 * (bitLenRat p + bitLenRat q + 1) ^ 2 := by
  set P := bitLenRat p with hP
  set Q := bitLenRat q with hQ
  set X := P + Q + 1 with hX
  have hP1 : numBits p ≤ P := numBits_le_bitLenRat p
  have hQ1 : numBits q ≤ Q := numBits_le_bitLenRat q
  have hP2 : denBits p ≤ P := denBits_le_bitLenRat p
  have hQ2 : denBits q ≤ Q := denBits_le_bitLenRat q
  have hX1 : 1 ≤ X := by omega
  have hm1 : bitOpCost (.mul (numBits p) (denBits q)) ≤ P * Q := by
    simp only [bitOpCost]; exact Nat.mul_le_mul hP1 hQ2
  have hm2 : bitOpCost (.mul (numBits q) (denBits p)) ≤ Q * P := by
    simp only [bitOpCost]; exact Nat.mul_le_mul hQ1 hP2
  have ha : bitOpCost (.add (numBits p + denBits q) (numBits q + denBits p)) ≤ 2 * X := by
    simp only [bitOpCost]; omega
  have hn : bitLenInt (p.num * (q.den : ℤ) + q.num * (p.den : ℤ)) ≤ 2 * X := by
    have h := bitLenInt_cross_add_le p.num q.num q.den p.den
    have h1 : bitLenInt p.num ≤ P := hP1
    have h2 : q.den.size ≤ Q := hQ2
    have h3 : bitLenInt q.num ≤ Q := hQ1
    have h4 : p.den.size ≤ P := hP2
    omega
  have hd : (p.den * q.den).size ≤ X := by
    have h := nat_size_mul_le p.den q.den
    have h1 : p.den.size ≤ P := hP2
    have h2 : q.den.size ≤ Q := hQ2
    omega
  have hred : reduceWork (p.num * (q.den : ℤ) + q.num * (p.den : ℤ)) (p.den * q.den)
      ≤ 2 * (2 * X + X + 1) ^ 2 := reduceWork_le _ _ (2 * X) X hn hd
  have hres : bitLenRat (p + q) ≤ X := by
    have h := bitLenRat_add p q
    omega
  have hread : P + Q ≤ X := by omega
  have hPQ : P * Q ≤ X ^ 2 := mul_le_sq (by omega) (by omega)
  unfold addWork
  nlinarith [hm1, hm2, ha, hred, hres, hread, hPQ, hX1]

theorem subWork_le (p q : ℚ) :
    subWork p q ≤ 64 * (bitLenRat p + bitLenRat q + 1) ^ 2 := by
  set P := bitLenRat p with hP
  set Q := bitLenRat q with hQ
  set X := P + Q + 1 with hX
  have hP1 : numBits p ≤ P := numBits_le_bitLenRat p
  have hQ1 : numBits q ≤ Q := numBits_le_bitLenRat q
  have hP2 : denBits p ≤ P := denBits_le_bitLenRat p
  have hQ2 : denBits q ≤ Q := denBits_le_bitLenRat q
  have hX1 : 1 ≤ X := by omega
  have hm1 : bitOpCost (.mul (numBits p) (denBits q)) ≤ P * Q := by
    simp only [bitOpCost]; exact Nat.mul_le_mul hP1 hQ2
  have hm2 : bitOpCost (.mul (numBits q) (denBits p)) ≤ Q * P := by
    simp only [bitOpCost]; exact Nat.mul_le_mul hQ1 hP2
  have ha : bitOpCost (.add (numBits p + denBits q) (numBits q + denBits p)) ≤ 2 * X := by
    simp only [bitOpCost]; omega
  have hn : bitLenInt (p.num * (q.den : ℤ) - q.num * (p.den : ℤ)) ≤ 2 * X := by
    have h := bitLenInt_cross_sub_le p.num q.num q.den p.den
    have h1 : bitLenInt p.num ≤ P := hP1
    have h2 : q.den.size ≤ Q := hQ2
    have h3 : bitLenInt q.num ≤ Q := hQ1
    have h4 : p.den.size ≤ P := hP2
    omega
  have hd : (p.den * q.den).size ≤ X := by
    have h := nat_size_mul_le p.den q.den
    have h1 : p.den.size ≤ P := hP2
    have h2 : q.den.size ≤ Q := hQ2
    omega
  have hred : reduceWork (p.num * (q.den : ℤ) - q.num * (p.den : ℤ)) (p.den * q.den)
      ≤ 2 * (2 * X + X + 1) ^ 2 := reduceWork_le _ _ (2 * X) X hn hd
  have hres : bitLenRat (p - q) ≤ X := by
    have h := bitLenRat_sub_le p q
    omega
  have hread : P + Q ≤ X := by omega
  have hPQ : P * Q ≤ X ^ 2 := mul_le_sq (by omega) (by omega)
  unfold subWork
  nlinarith [hm1, hm2, ha, hred, hres, hread, hPQ, hX1]

theorem mulWork_le (p q : ℚ) :
    mulWork p q ≤ 64 * (bitLenRat p * bitLenRat q + bitLenRat p + bitLenRat q + 1) ^ 2 := by
  set P := bitLenRat p with hP
  set Q := bitLenRat q with hQ
  set X := P * Q + P + Q + 1 with hX
  have hP1 : numBits p ≤ P := numBits_le_bitLenRat p
  have hQ1 : numBits q ≤ Q := numBits_le_bitLenRat q
  have hP2 : denBits p ≤ P := denBits_le_bitLenRat p
  have hQ2 : denBits q ≤ Q := denBits_le_bitLenRat q
  have hX1 : 1 ≤ X := by omega
  have hm1 : bitOpCost (.mul (numBits p) (numBits q)) ≤ X := by
    simp only [bitOpCost]
    have := Nat.mul_le_mul hP1 hQ1
    omega
  have hm2 : bitOpCost (.mul (denBits p) (denBits q)) ≤ X := by
    simp only [bitOpCost]
    have := Nat.mul_le_mul hP2 hQ2
    omega
  have hn : bitLenInt (p.num * q.num) ≤ X := by
    have h := bitLenInt_mul p.num q.num
    have h1 : bitLenInt p.num ≤ P := hP1
    have h2 : bitLenInt q.num ≤ Q := hQ1
    omega
  have hd : (p.den * q.den).size ≤ X := by
    have h := nat_size_mul_le p.den q.den
    have h1 : p.den.size ≤ P := hP2
    have h2 : q.den.size ≤ Q := hQ2
    omega
  have hred : reduceWork (p.num * q.num) (p.den * q.den) ≤ 2 * (X + X + 1) ^ 2 :=
    reduceWork_le _ _ X X hn hd
  have hres : bitLenRat (p * q) ≤ X := by
    have h := bitLenRat_mul p q
    omega
  have hread : P + Q ≤ X := by omega
  unfold mulWork
  nlinarith [hm1, hm2, hred, hres, hread, hX1]

theorem divWork_le (p q : ℚ) :
    divWork p q ≤ 64 * (bitLenRat p * bitLenRat q + bitLenRat p + bitLenRat q + 1) ^ 2 := by
  set P := bitLenRat p with hP
  set Q := bitLenRat q with hQ
  set X := P * Q + P + Q + 1 with hX
  have hP1 : numBits p ≤ P := numBits_le_bitLenRat p
  have hQ1 : numBits q ≤ Q := numBits_le_bitLenRat q
  have hP2 : denBits p ≤ P := denBits_le_bitLenRat p
  have hQ2 : denBits q ≤ Q := denBits_le_bitLenRat q
  have hX1 : 1 ≤ X := by omega
  have hm1 : bitOpCost (.mul (numBits p) (denBits q)) ≤ X := by
    simp only [bitOpCost]
    have := Nat.mul_le_mul hP1 hQ2
    omega
  have hm2 : bitOpCost (.mul (denBits p) (numBits q)) ≤ X := by
    simp only [bitOpCost]
    have := Nat.mul_le_mul hP2 hQ1
    omega
  have hn : bitLenInt (p.num * (q.den : ℤ)) ≤ X := by
    have h := bitLenInt_mul_natCast_le p.num q.den
    have h1 : bitLenInt p.num ≤ P := hP1
    have h2 : q.den.size ≤ Q := hQ2
    omega
  have hd : (p.den * q.num.natAbs).size ≤ X := by
    have h := nat_size_mul_le p.den q.num.natAbs
    have h1 : p.den.size ≤ P := hP2
    have h2 : q.num.natAbs.size ≤ Q := hQ1
    omega
  have hred : reduceWork (p.num * (q.den : ℤ)) (p.den * q.num.natAbs) ≤ 2 * (X + X + 1) ^ 2 :=
    reduceWork_le _ _ X X hn hd
  have hres : bitLenRat (p / q) ≤ X := by
    have h := bitLenRat_div_le p q
    omega
  have hread : P + Q ≤ X := by omega
  unfold divWork
  nlinarith [hm1, hm2, hred, hres, hread, hX1]

/-! ### 3.4  The envelope dominates the derived cost -/

/-- **The abstract envelope bounds the derived cost.**  This is the direction a
complexity upper bound needs: whatever the actual rationals are, the cost that
`ratBitCost` derives from their representation is dominated by the polynomial
`fieldOpBitCost` evaluated at the input bit lengths. -/
theorem ratBitCost_le_fieldOpBitCost (op : FieldOp) (p q : ℚ) :
    ratBitCost op p q ≤ fieldOpBitCost op (bitLenRat p) (bitLenRat q) := by
  cases op with
  | add =>
      have h := addWork_le p q
      simp only [ratBitCost, fieldOpBitCost]
      omega
  | sub =>
      have h := subWork_le p q
      simp only [ratBitCost, fieldOpBitCost]
      omega
  | mul =>
      have h := mulWork_le p q
      simp only [ratBitCost, fieldOpBitCost]
      omega
  | div =>
      have h := divWork_le p q
      simp only [ratBitCost, fieldOpBitCost]
      omega
  | inv =>
      simp only [ratBitCost, fieldOpBitCost, bitLenRat_inv]
      have h1 : 1 ≤ bitLenRat p := bitLenRat_pos p
      nlinarith

/-- **The literal converse requested by the review is false.**  `fieldOpBitCost`
cannot be a *lower* bound of the derived cost.  Witness `p = q = 0`: the envelope
for `mul` is `1 + 1 + 64 * (1*1 + 1 + 1 + 1)^2 = 1026`, while the cost actually
derived from the representations is `12`.  The gap widens with the operands: the
envelope is quadratic in the *product* of the input bit lengths, whereas
normalising a product of integers never squares the numerator length.  So the
envelope is an upper bound (the direction a complexity theorem needs), not a
lower bound. -/
theorem fieldOpBitCost_not_lower_bound :
    ¬ (∀ (op : FieldOp) (p q : ℚ),
        fieldOpBitCost op (bitLenRat p) (bitLenRat q) ≤ ratBitCost op p q) := by
  intro h
  have h2 := h .mul (0 : ℚ) (0 : ℚ)
  simp only [fieldOpBitCost, ratBitCost, mulWork, reduceWork, bitOpCost, numBits, denBits,
    bitLenRat_zero, bitLenInt_zero, Rat.num_zero, Rat.den_zero, Nat.reduceMul, Nat.reduceAdd,
    Nat.reducePow, Nat.size_one] at h2
  norm_num [bitLenRat_zero] at h2

/-! ## 4.  Primitives with a real state semantics -/

/-- The state is a register file: a value (a rational) in every cell. -/
abbrev St (σ : Type) := σ → ℚ

/-- Primitive operations.  Operands are either *carried constants* (`fieldOp`) or
*read from the state* (`fieldOpMix`, `readCell`); the cost of each primitive is
computed from the values, never from a number supplied in the syntax. -/
inductive Primitive (σ : Type) : Type → Type 1 where
  /-- A field operation on two carried constants, returning the result. -/
  | fieldOp (op : FieldOp) (p q : ℚ) : Primitive σ ℚ
  /-- `dst ← (state lhs) op q` with `q` a carried constant. -/
  | fieldOpMix (op : FieldOp) (lhs : σ) (q : ℚ) (dst : σ) : Primitive σ Unit
  /-- Read the rational stored in a cell. -/
  | readCell (c : σ) : Primitive σ ℚ
  /-- Store a carried constant in a cell. -/
  | writeCell (c : σ) (v : ℚ) : Primitive σ Unit

/-- The arithmetic performed by a field operation. -/
def applyFieldOp : FieldOp → ℚ → ℚ → ℚ
  | .add, p, q => p + q
  | .sub, p, q => p - q
  | .mul, p, q => p * q
  | .div, p, q => p / q
  | .inv, p, _ => p⁻¹

/-- **The bit cost of a primitive, derived from the values it touches.** -/
def primitiveCost {σ : Type} (s : St σ) : Primitive σ α → ℕ
  | .fieldOp op p q => ratBitCost op p q
  | .fieldOpMix op lhs q _ => ratBitCost op (s lhs) q
  | .readCell c => bitLenRat (s c)
  | .writeCell _ v => bitLenRat v

/-- **State semantics of a primitive.**  `alg = 1`: every primitive is one
algorithmic step; `bit` is `primitiveCost`.  `fieldOp` really computes
`p op q`, `fieldOpMix` really updates the destination cell, `readCell` really
returns the stored value and `writeCell` really overwrites the cell. -/
def evalPrimitive {σ : Type} [DecidableEq σ] (s : St σ) : Primitive σ α → St σ × α × Cost
  | .fieldOp op p q => (s, applyFieldOp op p q, ⟨1, ratBitCost op p q⟩)
  | .fieldOpMix op lhs q dst =>
      (Function.update s dst (applyFieldOp op (s lhs) q), (), ⟨1, ratBitCost op (s lhs) q⟩)
  | .readCell c => (s, s c, ⟨1, bitLenRat (s c)⟩)
  | .writeCell c v => (Function.update s c v, (), ⟨1, bitLenRat v⟩)

/-- `primitiveCost` is exactly the bit cost of `evalPrimitive`, and every
primitive is one algorithmic step. -/
theorem evalPrimitive_cost {σ : Type} [DecidableEq σ] (s : St σ) (p : Primitive σ α) :
    (evalPrimitive s p).2.2.bit = primitiveCost s p ∧ (evalPrimitive s p).2.2.alg = 1 := by
  cases p with
  | fieldOp op p q => exact ⟨rfl, rfl⟩
  | fieldOpMix op lhs q dst => exact ⟨rfl, rfl⟩
  | readCell c => exact ⟨rfl, rfl⟩
  | writeCell c v => exact ⟨rfl, rfl⟩

/-! ## 5.  Programs and their interpreter -/

/-- Programs.  Note on `bind`: the continuation is a genuine function
`α → Prog σ β`, so a total interpreter cannot recurse structurally on the syntax
(the program `g a` produced at run time need not be a subterm).  The interpreter
below is therefore defined by well-founded recursion on `Prog.size`; this is why
`bind` requires the index type `α` to be finite (`Fintype α`), which makes
`1 + size f + ∑ a, size (g a)` a legitimate decreasing measure.  Infinite index
types (such as `ℚ`) cannot be bound directly; data of that kind flows through
the *state*, via `Primitive.fieldOpMix`. -/
inductive Prog (σ : Type) : Type → Type 1 where
  | pure {α : Type} (a : α) : Prog σ α
  | read (c : σ) : Prog σ ℚ
  | write (c : σ) (v : ℚ) : Prog σ Unit
  | primitive {α : Type} (p : Primitive σ α) : Prog σ α
  | bind {α β : Type} [Fintype α] (f : Prog σ α) (g : α → Prog σ β) : Prog σ β
  | forFin {n : ℕ} (body : Fin n → Prog σ Unit) : Prog σ Unit

namespace Prog

/-- Syntactic size, used as the termination measure of `run`.  For `bind` the
continuation contributes the sum of the sizes of *all* its possible results; that
is why `bind` is restricted to finite index types. -/
noncomputable def size : Prog σ α → ℕ
  | .pure _ => 1
  | .read _ => 1
  | .write _ _ => 1
  | .primitive _ => 1
  | @Prog.bind _ α β _ f g => 1 + size f + Finset.univ.sum (fun a : α => size (g a))
  | @Prog.forFin _ n body => 1 + Finset.univ.sum (fun i : Fin n => size (body i))

theorem size_bind_left {α β : Type} [Fintype α] (f : Prog σ α) (g : α → Prog σ β) :
    size f < size (.bind f g) := by
  simp only [size]
  omega

theorem size_bind_right {α β : Type} [Fintype α] (f : Prog σ α) (g : α → Prog σ β) (a : α) :
    size (g a) < size (.bind f g) := by
  simp only [size]
  have h := Finset.single_le_sum (f := fun a : α => size (g a))
    (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
  omega

theorem size_forFin {n : ℕ} (body : Fin n → Prog σ Unit) (i : Fin n) :
    size (body i) < size (.forFin body) := by
  simp only [size]
  have h := Finset.single_le_sum (f := fun i : Fin n => size (body i))
    (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

end Prog

/-- Iterate a state-and-cost step function over `Fin n`, in order. -/
def iterateFin {σ : Type} : (n : ℕ) → (Fin n → St σ → St σ × Cost) → St σ → St σ × Cost
  | 0, _, s => (s, 0)
  | n + 1, f, s =>
      let r := f 0 s
      let rest := iterateFin n (fun i => f i.succ) r.1
      (rest.1, r.2 + rest.2)

section Interpreter

variable {σ : Type} [DecidableEq σ]

/-- **The interpreter.**  Returns the final state, the computed value and the
cost, all derived from the run. -/
noncomputable def run : Prog σ α → St σ → St σ × α × Cost
  | .pure a, s => (s, a, 0)
  | .read c, s => (s, s c, ⟨1, bitLenRat (s c)⟩)
  | .write c v, s => (Function.update s c v, (), ⟨1, bitLenRat v⟩)
  | .primitive p, s => evalPrimitive s p
  | @Prog.bind _ α β _ f g, s =>
      let r := run f s
      let r2 := run (g r.2.1) r.1
      (r2.1, r2.2.1, r.2.2 + r2.2.2)
  | @Prog.forFin _ n body, s =>
      let r := iterateFin n (fun i st => let x := run (body i) st; (x.1, x.2.2)) s
      (r.1, (), r.2)
  termination_by p => p.size
  decreasing_by
    all_goals
      first
        | exact Prog.size_bind_left _ _
        | exact Prog.size_bind_right _ _ _
        | exact Prog.size_forFin _ _

/-! ### 5.1  The defining equations of `run` -/

theorem run_pure (a : α) (s : St σ) : run (.pure a) s = (s, a, 0) := by
  simp [run]

theorem run_read (c : σ) (s : St σ) : run (.read c) s = (s, s c, ⟨1, bitLenRat (s c)⟩) := by
  simp [run]

theorem run_write (c : σ) (v : ℚ) (s : St σ) :
    run (.write c v) s = (Function.update s c v, (), ⟨1, bitLenRat v⟩) := by
  simp [run]

theorem run_primitive (p : Primitive σ α) (s : St σ) : run (.primitive p) s = evalPrimitive s p := by
  simp [run]

/-- **Sequencing.**  The cost of `bind f g` is the cost of `f` plus the cost of
the actual continuation: costs add, and the value produced by `f` is threaded
into `g`. -/
theorem run_bind {α β : Type} [Fintype α] (f : Prog σ α) (g : α → Prog σ β) (s : St σ) :
    run (.bind f g) s =
      (let r := run f s
       let r2 := run (g r.2.1) r.1
       (r2.1, r2.2.1, r.2.2 + r2.2.2)) := by
  simp [run]

theorem run_bind_state {α β : Type} [Fintype α] (f : Prog σ α) (g : α → Prog σ β) (s : St σ) :
    (run (.bind f g) s).1 = (run (g (run f s).2.1) (run f s).1).1 := by
  simp [run]

theorem run_bind_value {α β : Type} [Fintype α] (f : Prog σ α) (g : α → Prog σ β) (s : St σ) :
    (run (.bind f g) s).2.1 = (run (g (run f s).2.1) (run f s).1).2.1 := by
  simp [run]

theorem run_bind_cost {α β : Type} [Fintype α] (f : Prog σ α) (g : α → Prog σ β) (s : St σ) :
    (run (.bind f g) s).2.2 = (run f s).2.2 + (run (g (run f s).2.1) (run f s).1).2.2 := by
  simp [run]

/-- Run a loop over `Fin n`, threading the state through the iterations in
execution order.  This is the state-threading loop that `forFin` executes. -/
noncomputable def runForFin (n : ℕ) (body : Fin n → Prog σ Unit) (s : St σ) : St σ × Cost :=
  iterateFin n (fun i st => let x := run (body i) st; (x.1, x.2.2)) s

/-- **The loop.**  `forFin` executes `runForFin` and discards the (final) value,
so its cost is exactly the loop's accumulated cost. -/
theorem run_forFin (n : ℕ) (body : Fin n → Prog σ Unit) (s : St σ) :
    run (.forFin body) s = ((runForFin n body s).1, (), (runForFin n body s).2) := by
  simp [run, runForFin]

/-- The state in which the `k`-th iteration of the loop starts.  This is the
precise "state threading": iteration `0` starts in `s`, and iteration `k.succ`
starts in the state produced by iteration `k`. -/
noncomputable def statesOf : (n : ℕ) → (Fin n → Prog σ Unit) → St σ → Fin n → St σ
  | 0, _, _, k => k.elim0
  | n + 1, body, s, k =>
      Fin.cases s (fun j => statesOf n (fun i => body i.succ) (run (body 0) s).1 j) k

end Interpreter

/-! ## 6.  Decomposition theorems -/

section Decomposition

variable {σ : Type} [DecidableEq σ]

/-- **Loop cost is the sum over the iterations.**  The states are the ones
produced by threading, so the summands are exactly the costs that were actually
paid. -/
theorem run_forFin_bit_eq_sum (n : ℕ) (body : Fin n → Prog σ Unit) (s : St σ) :
    (run (.forFin body) s).2.2.bit
      = ∑ k : Fin n, (run (body k) (statesOf n body s k)).2.2.bit := by
  induction n generalizing s with
  | zero => simp [run, iterateFin]
  | succ n ih =>
      have hstep : (run (.forFin body) s).2.2.bit
          = (run (body 0) s).2.2.bit
            + (run (.forFin (fun i => body i.succ)) (run (body 0) s).1).2.2.bit := by
        simp [run, iterateFin]
      rw [hstep, Fin.sum_univ_succ]
      have h0 : (run (body 0) (statesOf (n + 1) body s 0)).2.2.bit = (run (body 0) s).2.2.bit := by
        simp [statesOf]
      have hsucc : ∀ k : Fin n,
          (run (body k.succ) (statesOf (n + 1) body s k.succ)).2.2.bit
            = (run ((fun i => body i.succ) k)
                (statesOf n (fun i => body i.succ) (run (body 0) s).1 k)).2.2.bit := by
        intro k
        simp [statesOf]
      have hsum : (∑ k : Fin n, (run (body k.succ) (statesOf (n + 1) body s k.succ)).2.2.bit)
          = ∑ k : Fin n, (run ((fun i => body i.succ) k)
                (statesOf n (fun i => body i.succ) (run (body 0) s).1 k)).2.2.bit :=
        Finset.sum_congr rfl (fun k _ => hsucc k)
      rw [h0, hsum, ih]

/-- **The `alg` component is the executed-operation count.**  Every summand is
the number of algorithmic steps of one iteration; the total is their sum, with
the state threaded.  In particular no cost can be injected by the caller: the
syntax has no cost field, and this theorem computes the count from the run. -/
theorem run_alg_eq_primitiveCount (n : ℕ) (body : Fin n → Prog σ Unit) (s : St σ) :
    (run (.forFin body) s).2.2.alg
      = ∑ k : Fin n, (run (body k) (statesOf n body s k)).2.2.alg := by
  induction n generalizing s with
  | zero => simp [run, iterateFin]
  | succ n ih =>
      have hstep : (run (.forFin body) s).2.2.alg
          = (run (body 0) s).2.2.alg
            + (run (.forFin (fun i => body i.succ)) (run (body 0) s).1).2.2.alg := by
        simp [run, iterateFin]
      rw [hstep, Fin.sum_univ_succ]
      have h0 : (run (body 0) (statesOf (n + 1) body s 0)).2.2.alg = (run (body 0) s).2.2.alg := by
        simp [statesOf]
      have hsucc : ∀ k : Fin n,
          (run (body k.succ) (statesOf (n + 1) body s k.succ)).2.2.alg
            = (run ((fun i => body i.succ) k)
                (statesOf n (fun i => body i.succ) (run (body 0) s).1 k)).2.2.alg := by
        intro k
        simp [statesOf]
      have hsum : (∑ k : Fin n, (run (body k.succ) (statesOf (n + 1) body s k.succ)).2.2.alg)
          = ∑ k : Fin n, (run ((fun i => body i.succ) k)
                (statesOf n (fun i => body i.succ) (run (body 0) s).1 k)).2.2.alg :=
        Finset.sum_congr rfl (fun k _ => hsucc k)
      rw [h0, hsum, ih]

/-- A loop whose iterations each cost exactly one algorithmic step (a single
field operation, read or write) executes exactly `n` steps. -/
theorem run_alg_forFin_eq (n : ℕ) (body : Fin n → Prog σ Unit) (s : St σ)
    (h : ∀ k : Fin n, (run (body k) (statesOf n body s k)).2.2.alg = 1) :
    (run (.forFin body) s).2.2.alg = n := by
  rw [run_alg_eq_primitiveCount]
  calc ∑ k : Fin n, (run (body k) (statesOf n body s k)).2.2.alg
      = ∑ _k : Fin n, 1 := Finset.sum_congr rfl (fun k _ => h k)
    _ = n := by simp

/-- **Bit cost is bounded by the sum of the per-iteration bounds.** -/
theorem run_bit_le_sum (n : ℕ) (body : Fin n → Prog σ Unit) (s : St σ) (B : ℕ)
    (hB : ∀ k : Fin n, (run (body k) (statesOf n body s k)).2.2.bit ≤ B) :
    (run (.forFin body) s).2.2.bit ≤ n * B := by
  rw [run_forFin_bit_eq_sum]
  calc ∑ k : Fin n, (run (body k) (statesOf n body s k)).2.2.bit
      ≤ ∑ _k : Fin n, B := Finset.sum_le_sum (fun k _ => hB k)
    _ = n * B := by simp [Finset.sum_const]

end Decomposition

/-! ## 7.  Worked example: adding `n` rationals in a loop -/

/-- The body of the accumulator loop: `acc ← acc + vᵢ`, where `vᵢ` is a carried
constant and `acc` lives in the single cell `()` of the state. -/
def addBody (n : ℕ) (v : Fin n → ℚ) (i : Fin n) : Prog Unit Unit :=
  .primitive (.fieldOpMix .add () (v i) ())

/-- Add the `n` rationals `v 0, …, v (n-1)`, accumulating in the cell `()`. -/
def sumProg (n : ℕ) (v : Fin n → ℚ) : Prog Unit Unit :=
  .forFin (addBody n v)

/-- The loop really adds: after two iterations the accumulator holds
`s () + v 0 + v 1`.  This shows that the state semantics is not vacuous. -/
theorem sumProg_run_two (v : Fin 2 → ℚ) (s : St Unit) :
    (run (sumProg 2 v) s).1 ()
      = s () + v 0 + v 1 := by
  simp [sumProg, addBody, run, iterateFin, evalPrimitive, applyFieldOp, Function.update]

/-- The cost of the same two-iteration loop is the sum of the two derived field
costs, with the *actual* intermediate accumulator value in the second summand. -/
theorem sumProg_cost_two (v : Fin 2 → ℚ) (s : St Unit) :
    (run (sumProg 2 v) s).2.2.bit
      = ratBitCost .add (s ()) (v 0) + ratBitCost .add (s () + v 0) (v 1) := by
  simp [sumProg, addBody, run, iterateFin, evalPrimitive, applyFieldOp, Function.update]

/-- The same computation through the general decomposition theorem: the loop cost
is the sum of the two per-iteration costs. -/
theorem sumProg_cost_two_via_sum (v : Fin 2 → ℚ) (s : St Unit) :
    (run (sumProg 2 v) s).2.2.bit
      = ∑ k : Fin 2, (run (addBody 2 v k) (statesOf 2 (addBody 2 v) s k)).2.2.bit :=
  run_forFin_bit_eq_sum 2 (addBody 2 v) s

end Q1Complexity
