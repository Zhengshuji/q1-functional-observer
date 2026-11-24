
import Q1Paper.PaperI.GramCompression
import Q1Paper.PaperI.Claim15iv

/-!
Q1Paper/PaperI/CompressedGram.lean

**Bit-length bound for the entries of the compressed Gram matrix, transferred to
the window Gram.**

*Naming note (read first).*  The guesses in the task are close but not literal:
`Q1Paper.PaperI.compressedGram` is indexed by the polynomial matrix `P` and calls
`coeffGram P ω` on `Nat` indices, so the abstract integer compressed matrix used
below is `compressedGramOf (S : Nat -> Nat -> Int)` rather than
`compressedGram (S : Matrix (Fin (2*ω)) (Fin (2*ω)) Int)`.  The identification
`compressedGram P ω = compressedGramOf (coeffGram P ω)` is definitional (`rfl`),
see `compressedGram_eq_compressedGramOf`.  `windowGram` was not a definition in
the tree; the product `Zᵀ * Z` is packaged here as `windowGram` (definitionally
the matrix product of `Q1Paper.windowMatrix`).

*Route (and why it avoids the `sω` construction).*  The window matrix `Z` of
Claim 10 has rows indexed by `(I, J, j)` with `I ⊆ Fin q`, `J ⊆ Fin ℓ`,
`|I| = |J| = ω` and `j : Fin ω`, hence `s * ω` rows where
`s = C(q,ω) * C(ℓ,ω)`.  The Gram matrix `Zᵀ Z` is only `2ω × 2ω`, and
`Q1Paper.PaperI.windowGram_eq_compressed` proves it is *entrywise* the compressed
coefficient matrix

  `(Zᵀ Z)_{t,t'} = ∑_{j : Fin ω} [j ≤ t and j ≤ t'] * S_{t-j, t'-j}`,

where `S = coeffGram P ω` is the coefficient Gram form.  The bit-length bound is
therefore proved **on the compressed matrix only**: a sum of at most `ω`
coefficients, each of bit length at most `b`, fits in `b + ω.size` bits (and hence
also in `2*b + (2*ω).size + 1`).  The transfer to `Zᵀ Z` is the single rewriting
step `windowGram_eq_compressed`; the `sω`-row matrix is never constructed, and the
factor `s` never enters any arithmetic estimate.

Patching `Q1Paper.Claim15iv.gramEntry_bitLen_le_47` would be the wrong move: that
lemma bounds a `2ω`-term sum for the *square* model and its helper
`bitLenInt_sum_le` is linear in the number of summands (`card + ∑ b`); neither the
term count `ω` versus `sω` nor the logarithmic cost of adding the summands is
visible there.

*What the transfer needs.*  `windowGram_eq_compressed` is an equality of matrices
over an arbitrary field, hence entrywise.  Bit lengths, however, are attached to
integers, so the transfer is stated over `K = ℚ` and uses two explicit facts:

  1. the coefficient values `coeffGram P ω a b` are integers (`den = 1`) — the
     *cleared-coefficient* regime of Claim 15(iv); then the rational sum of the
     coefficients has, as numerator, exactly the integer compressed sum
     (`compressedGram_entry_eq_intCast`);
  2. the numerators obey the coefficient bound `b` (`hS`).

Without (1) the sharp `O(log ω)` bound is false: a sum of `ω` reduced rationals
with `b`-bit numerators and denominators can have a numerator of up to `ω * b`
bits (the lcm of the denominators), so an integrality or common-denominator
hypothesis is essential.  The common-denominator generalisation is noted in §5.

Everything below lives in `namespace Q1Paper.PaperI`.  No `sorry`, no `admit`, no
new axioms.  Check with
  `lake env lean Q1Paper/PaperI/CompressedGram.lean`.
-/


open Matrix Polynomial
open scoped BigOperators

namespace Q1Paper.PaperI

variable {K : Type*} [Field K]

/-! ## 1.  The compressed Gram matrix, abstractly -/

/-- The **compressed coefficient matrix**: the `(t,t')` entry is the sum of the
coefficients `S_{a,b}` over the window shift `j : Fin ω` with `a = t - j`,
`b = t' - j`, whenever `j ≤ t` and `j ≤ t'`.

This is the generic (coefficient-level) form of `compressedGram`: `S` is the
coefficient Gram form `coeffGram P ω` in the application.  Its index type is
`Fin (2 * ω) × Fin (2 * ω)`, independently of the number `s = C(q,ω)*C(ℓ,ω)` of
minor-index pairs. -/
noncomputable def compressedGramOf {α : Type*} [AddCommMonoid α] {ω : ℕ}
    (S : ℕ → ℕ → α) : Matrix (Fin (2 * ω)) (Fin (2 * ω)) α :=
  fun t t' => ∑ j : Fin ω,
    if (j : ℕ) ≤ (t : ℕ) ∧ (j : ℕ) ≤ (t' : ℕ) then
      S ((t : ℕ) - (j : ℕ)) ((t' : ℕ) - (j : ℕ)) else 0

/-- **The coefficient matrix of `GramCompression.lean` is the abstract compressed
matrix.**  This is the definitional identification used by the transfer; it is
`rfl` because the two definitions differ only in the name of the coefficient
function. -/
theorem compressedGram_eq_compressedGramOf {q ℓ : ℕ}
    (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ) :
    compressedGram P ω = compressedGramOf (coeffGram P ω) := rfl

/-- The **window Gram matrix** `Zᵀ Z` of the minor family (the object of Claim 10,
Section III-D).  This is a `2ω × 2ω` matrix; its definition mentions the `sω`-row
window matrix `Z`, but no estimate below ever unfolds this definition. -/
noncomputable def windowGram {q ℓ : ℕ} (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ) :
    Matrix (Fin (2 * ω)) (Fin (2 * ω)) K :=
  (Q1Paper.windowMatrix (windowMinorFamily P ω) ω)ᵀ *
    Q1Paper.windowMatrix (windowMinorFamily P ω) ω

/-- **The window Gram matrix is the abstract compressed matrix**: the composition
of the formalised identity `windowGram_eq_compressed` with the definitional
identification `compressedGram_eq_compressedGramOf`.  This is the entire content of
the transfer: an entrywise equality of a `2ω × 2ω` matrix with a sum of `ω`
coefficients. -/
theorem windowGram_eq_compressedGramOf {q ℓ : ℕ}
    (P : Matrix (Fin q) (Fin ℓ) K[X]) (ω : ℕ) :
    windowGram P ω = compressedGramOf (coeffGram P ω) := by
  unfold windowGram
  rw [windowGram_eq_compressed, compressedGram_eq_compressedGramOf]

/-! ## 2.  Bit length of a sum with a magnitude bound on the summands -/

/-- **Bit length of a sum from a common magnitude bound.**  If every summand is
smaller than `2 ^ b` in absolute value, then the sum has bit length at most
`b + s.card.size`.  This is the logarithmic-cost sum bound: the number of summands
enters only through `Nat.size`.  (The existing `bitLenInt_sum_le` of
`Claim15iv.lean` is linear, `s.card + ∑ b`, and is too lossy for the compressed
Gram, where the summand count is `ω`.) -/
theorem bitLenInt_sum_le_card_size {ι : Type*} (s : Finset ι) (f : ι → ℤ) {b : ℕ}
    (h : ∀ i ∈ s, |f i| < (2 : ℤ) ^ b) :
    bitLenInt (s.sum f) ≤ b + s.card.size := by
  classical
  rw [bitLenInt_le_iff]
  have h1 : |s.sum f| ≤ s.sum (fun i => |f i|) := Finset.abs_sum_le_sum_abs f s
  have h2 : s.sum (fun i => |f i|) ≤ s.sum (fun _ => (2 : ℤ) ^ b) :=
    Finset.sum_le_sum (fun i hi => le_of_lt (h i hi))
  have h3 : s.sum (fun _ => (2 : ℤ) ^ b) = (s.card : ℤ) * (2 : ℤ) ^ b := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (s.card : ℤ) < (2 : ℤ) ^ s.card.size := by
    have hlt := Nat.lt_size_self s.card
    have hlt' : ((s.card : ℕ) : ℤ) < ((2 ^ s.card.size : ℕ) : ℤ) := by
      exact_mod_cast hlt
    simpa using hlt'
  have h4 : (s.card : ℤ) * (2 : ℤ) ^ b < (2 : ℤ) ^ s.card.size * (2 : ℤ) ^ b :=
    mul_lt_mul_of_pos_right hcard (by positivity)
  have h5 : (2 : ℤ) ^ s.card.size * (2 : ℤ) ^ b = (2 : ℤ) ^ (s.card.size + b) :=
    (pow_add _ _ _).symm
  have hlt : |s.sum f| < (2 : ℤ) ^ (b + s.card.size) := by
    calc |s.sum f| ≤ s.sum (fun i => |f i|) := h1
      _ ≤ s.sum (fun _ => (2 : ℤ) ^ b) := h2
      _ = (s.card : ℤ) * (2 : ℤ) ^ b := h3
      _ < (2 : ℤ) ^ s.card.size * (2 : ℤ) ^ b := h4
      _ = (2 : ℤ) ^ (s.card.size + b) := h5
      _ = (2 : ℤ) ^ (b + s.card.size) := by rw [Nat.add_comm]
  have h6 : ((s.sum f).natAbs : ℤ) < ((2 ^ (b + s.card.size) : ℕ) : ℤ) := by
    rw [← Int.abs_eq_natAbs]
    push_cast
    exact hlt
  exact Nat.cast_lt.mp h6

/-! ## 3.  The compressed Gram entry bound -/

/-- **Bit-length bound for the entries of the compressed Gram matrix.**

If every coefficient `S a b` has bit length at most `b`, then the compressed entry

  `compressedGramOf S t t' = ∑_{j : Fin ω} [j ≤ t and j ≤ t'] S_{t-j,t'-j}`

has bit length at most `b + ω.size`.  This is the sharp form: `≤ ω` nonzero
summands of `b` bits each, added with carry, cost `b + log₂ ω` bits (not
`ω * b`).  The `sω`-row window matrix plays no role in this statement. -/
theorem compressedGram_entry_bitLen_le {ω : ℕ} (S : ℕ → ℕ → ℤ) {b : ℕ}
    (hS : ∀ a b', bitLenInt (S a b') ≤ b) (t t' : Fin (2 * ω)) :
    bitLenInt (compressedGramOf S t t') ≤ b + ω.size := by
  classical
  unfold compressedGramOf
  refine le_trans (bitLenInt_sum_le_card_size (Finset.univ : Finset (Fin ω))
    (fun j : Fin ω =>
      if (j : ℕ) ≤ (t : ℕ) ∧ (j : ℕ) ≤ (t' : ℕ) then
        S ((t : ℕ) - (j : ℕ)) ((t' : ℕ) - (j : ℕ)) else 0) (b := b) ?_) ?_
  · intro j _
    by_cases h : (j : ℕ) ≤ (t : ℕ) ∧ (j : ℕ) ≤ (t' : ℕ)
    · rw [ite_eq_left h]
      exact Q1Paper.Claim15iv.abs_lt_two_pow_of_bitLenInt_le (hS _ _)
    · rw [ite_eq_right h, abs_zero]
      positivity
  · simp

/-- The requested (cruder) form of the compressed bound:
`2 * b + (2 * ω).size + 1`.  It follows from the sharp `b + ω.size` because
`ω.size ≤ (2 * ω).size`. -/
theorem compressedGram_entry_bitLen_le_two_mul_add {ω : ℕ} (S : ℕ → ℕ → ℤ) {b : ℕ}
    (hS : ∀ a b', bitLenInt (S a b') ≤ b) (t t' : Fin (2 * ω)) :
    bitLenInt (compressedGramOf S t t') ≤ 2 * b + (2 * ω).size + 1 := by
  have h := compressedGram_entry_bitLen_le S hS t t'
  have hω : ω.size ≤ (2 * ω).size := Nat.size_le_size (by omega)
  omega

/-! ## 4.  Transfer to the window Gram over `ℚ` -/

/-- A rational number with denominator `1` is the cast of its numerator. -/
theorem rat_eq_num_of_den_eq_one {x : ℚ} (h : x.den = 1) :
    ((x.num : ℤ) : ℚ) = x := by
  have hx := Rat.mul_den_eq_num x
  rw [h, Nat.cast_one, mul_one] at hx
  exact hx.symm

/-- **The compressed Gram entry over `ℚ` is the cast of an integer compressed
entry**, provided every coefficient is an integer.  This is exactly where the
integrality (cleared-coefficient) hypothesis is used: the numerator of the sum is
the sum of the numerators. -/
theorem compressedGram_entry_eq_intCast {q ℓ : ℕ}
    (P : Matrix (Fin q) (Fin ℓ) ℚ[X]) (ω : ℕ)
    (hint : ∀ a b, (coeffGram P ω a b).den = 1) (t t' : Fin (2 * ω)) :
    compressedGram P ω t t' =
      ((compressedGramOf (fun a b => (coeffGram P ω a b).num) t t' : ℤ) : ℚ) := by
  classical
  unfold compressedGram compressedGramOf
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (j : ℕ) ≤ (t : ℕ) ∧ (j : ℕ) ≤ (t' : ℕ)
  · rw [ite_eq_left h, ite_eq_left h]
    exact (rat_eq_num_of_den_eq_one (hint _ _)).symm
  · rw [ite_eq_right h, ite_eq_right h]
    simp

/-- **Transfer of the bit-length bound to the window Gram.**

For a rational polynomial matrix `P` whose coefficient Gram form is integral
(`hint`) with coefficient numerators of bit length at most `b` (`hS`), every entry
of the window Gram matrix `Zᵀ Z` (taken at its numerator) has bit length at most
`b + ω.size`.

The proof uses the *entrywise* equality `windowGram_eq_compressed` and nothing
else about `Z`: no `s * ω`-row matrix is built.  Note the honest restriction: the
entries of `windowGram` are rationals; the statement bounds their numerators. -/
theorem windowGram_entry_bitLen_le {q ℓ : ℕ}
    (P : Matrix (Fin q) (Fin ℓ) ℚ[X]) (ω : ℕ)
    (hint : ∀ a b, (coeffGram P ω a b).den = 1) {b : ℕ}
    (hS : ∀ a b', bitLenInt ((coeffGram P ω a b').num) ≤ b) (t t' : Fin (2 * ω)) :
    bitLenInt ((windowGram P ω t t').num) ≤ b + ω.size := by
  have h1 : windowGram P ω t t' = compressedGram P ω t t' := by
    unfold windowGram
    rw [windowGram_eq_compressed]
  rw [h1, compressedGram_entry_eq_intCast P ω hint t t', Rat.num_intCast]
  exact compressedGram_entry_bitLen_le (fun a b => (coeffGram P ω a b).num) hS t t'

/-- The requested (cruder) form of the window-Gram bound:
`2 * b + (2 * ω).size + 1`. -/
theorem windowGram_entry_bitLen_le_two_mul_add {q ℓ : ℕ}
    (P : Matrix (Fin q) (Fin ℓ) ℚ[X]) (ω : ℕ)
    (hint : ∀ a b, (coeffGram P ω a b).den = 1) {b : ℕ}
    (hS : ∀ a b', bitLenInt ((coeffGram P ω a b').num) ≤ b) (t t' : Fin (2 * ω)) :
    bitLenInt ((windowGram P ω t t').num) ≤ 2 * b + (2 * ω).size + 1 := by
  have h := windowGram_entry_bitLen_le P ω hint hS t t'
  have hω : ω.size ≤ (2 * ω).size := Nat.size_le_size (by omega)
  omega

/-! ## 5.  Remarks / what remains

* The hypothesis `hint` (every coefficient has denominator `1`) is the
  cleared-coefficient regime: for `P` with integer entries every maximal minor has
  integer coefficients, so `hint` holds.  It is *not* derived here from an
  integrality hypothesis on `P`; that derivation belongs to the `coeffGram` layer.
* The same argument covers a *common* denominator `D` (replace `den = 1` by
  `den = D`): the reduced numerator of `∑ n_j / D` divides `∑ n_j`, so the sharp
  bound survives.  Only the `D = 1` case is formalised here.
* A `bitLenRat` version of `windowGram_entry_bitLen_le` follows once
  `(windowGram P ω t t').den = 1` is observed (the entry is an integer cast); that
  denominator fact is not stated below.
-/

end Q1Paper.PaperI