
import Q1Paper.PaperI.Claim15iv

/-!
Q1Paper/PaperI/GramRows.lean

The Gram entry of a **non-square** window matrix.

The paper's window matrix `Z` has shape `(s * omega) x (2 * omega)` (`s` = the
number of maximal minors, `omega` = their degree), with `Z_{(i,j),t} = c_{i,t-j}`.
Hence

  `(Zᵀ * Z) i j = ∑ k : Fin (s * omega), Z k i * Z k j`

has `s * omega` summands, not `2 * omega`.

`PaperI/Claim15iv.lean`'s `gramEntry_bitLen_le_47` is stated for the **square**
shape `Fin (2ω) → Fin (2ω) → ℤ`, so it does not cover the real object.  This
file supplies the row-count-generic replacement.  Main results:

* `bitLenInt_sum_mul_le_rows` : a sum of `m` products of `b`-bit integers has
  bit length at most `2b + log₂ m` (sharp: the `m` summands cost only
  `Nat.size m` bits, not `m`);
* `gramEntry_bitLen_le_of_rows_sharp` : `bitLenInt ((Zᵀ * Z) i j) ≤ 2b + size m`;
* `gramEntry_bitLen_le_of_rows` : `≤ 2b + size m + 1` (the requested slack form);
* `gramEntry_bitLen_le_of_rows_log` : `… ≤ 2b + r + 1` whenever `m ≤ 2^r`.

The instantiation at a *concrete* row count is left to the consumer: for the
paper's window matrix the rows are indexed by `(I, J, j)` and the number of
maximal minors is `s = C(q,ω) * C(ℓ,ω)`, so the instantiation belongs to the
compression route rather than here.

**Why the `Claim15iv` sum bound alone is not enough.**  The induction behind
`gramEntry_bitLen_le_47` is `bitLenInt_sum_mul_le_univ`, which gives
`bitLenInt (∑ k, f k * g k) ≤ Fintype.card ι + bf + bg`, i.e. `m + 2b` for
`ι = Fin m`.  That does **not** imply `2b + Nat.size m + 1`: it would require
`m ≤ Nat.size m + 1`, which already fails at `m = 7` (`Nat.size 7 = 3`, and
`7 ≤ 4` is false).  The log-sized bound therefore needs the *magnitude*
estimate

  `|∑ k, u k * v k| ≤ ∑ k |u k| * |v k| ≤ m * 2 ^ (2b) < 2 ^ (size m + 2b)`,

which is what `bitLenInt_sum_mul_le_rows` proves.  Per-term ingredients:
`bitLenInt z ≤ b → z.natAbs < 2 ^ b` is `bitLenInt_le_iff` (the same bridge as
`Claim15iv.abs_lt_two_pow_of_bitLenInt_le`), and the summation is bounded with
`Int.natAbs_sum_le`, `Nat.mul_le_mul_right`, `Nat.mul_lt_mul_of_pos_left`,
`Nat.pow_add`, `Nat.lt_size_self`.

No `sorry`, no `admit`, no new axioms.  Check with
  lake env lean Q1Paper/PaperI/GramRows.lean
-/


open Matrix

open scoped BigOperators

namespace Q1Paper.ScratchGramRows

open Q1Paper.PaperI

/-! ## 1.  A sum of `m` products of `b`-bit integers -/

/-- **Sum of products, log-sized bound.**  If every `u k` and every `v k`
(`k : Fin m`) has bit length at most `b`, then `∑ k, u k * v k` has bit length
at most `2 * b + Nat.size m`.  This is the sharp form needed for a Gram entry:
the cost of the `m` summands is `log₂ m`, not `m`. -/
theorem bitLenInt_sum_mul_le_rows {m : ℕ} (u v : Fin m → ℤ) {b : ℕ}
    (hu : ∀ k, bitLenInt (u k) ≤ b) (hv : ∀ k, bitLenInt (v k) ≤ b) :
    bitLenInt (∑ k : Fin m, u k * v k) ≤ 2 * b + Nat.size m := by
  rw [bitLenInt, Nat.size_le]
  -- every product has absolute value `< 2 ^ (2b)`
  have hterm : ∀ k : Fin m, (u k * v k).natAbs < 2 ^ (2 * b) := by
    intro k
    rw [Int.natAbs_mul]
    have hu' : (u k).natAbs < 2 ^ b := bitLenInt_le_iff.mp (hu k)
    have hv' : (v k).natAbs < 2 ^ b := bitLenInt_le_iff.mp (hv k)
    have hpos : 0 < 2 ^ b := by positivity
    calc (u k).natAbs * (v k).natAbs
        ≤ 2 ^ b * (v k).natAbs := Nat.mul_le_mul_right _ (le_of_lt hu')
      _ < 2 ^ b * 2 ^ b := Nat.mul_lt_mul_of_pos_left hv' hpos
      _ = 2 ^ (2 * b) := by rw [← Nat.pow_add]; ring_nf
  -- the sum is bounded by `m * 2 ^ (2b)`
  have hsum : (∑ k : Fin m, u k * v k).natAbs ≤ m * 2 ^ (2 * b) := by
    calc (∑ k : Fin m, u k * v k).natAbs
        ≤ ∑ k : Fin m, (u k * v k).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _k : Fin m, 2 ^ (2 * b) :=
          Finset.sum_le_sum (fun k _ => le_of_lt (hterm k))
      _ = m * 2 ^ (2 * b) := by simp
  -- `m * 2 ^ (2b) < 2 ^ (size m) * 2 ^ (2b) = 2 ^ (size m + 2b)`
  calc (∑ k : Fin m, u k * v k).natAbs
      ≤ m * 2 ^ (2 * b) := hsum
    _ < 2 ^ (Nat.size m) * 2 ^ (2 * b) :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self m) (by positivity)
    _ = 2 ^ (Nat.size m + 2 * b) := (Nat.pow_add 2 (Nat.size m) (2 * b)).symm
    _ = 2 ^ (2 * b + Nat.size m) := by rw [Nat.add_comm (Nat.size m) (2 * b)]

/-! ## 2.  Gram entries of a matrix with `m` rows -/

/-- **Sharp form.**  `(Zᵀ * Z) i j` is a sum of exactly `m` products
`Z k i * Z k j`, so its bit length is at most `2b + Nat.size m`. -/
theorem gramEntry_bitLen_le_of_rows_sharp {m ω b : ℕ} (Z : Matrix (Fin m) (Fin (2 * ω)) ℤ)
    (hZ : ∀ i j, bitLenInt (Z i j) ≤ b) (i j : Fin (2 * ω)) :
    bitLenInt ((Zᵀ * Z) i j) ≤ 2 * b + Nat.size m := by
  rw [Matrix.mul_apply]
  have hrow := bitLenInt_sum_mul_le_rows (fun k : Fin m => Z k i)
    (fun k : Fin m => Z k j) (fun k => hZ k i) (fun k => hZ k j)
  simpa [Matrix.transpose_apply] using hrow

/-- **The Gram entry of a matrix with `m` rows.**  `(Zᵀ * Z) i j` is a sum of
exactly `m` products `Z k i * Z k j`, so its bit length is at most
`2b + Nat.size m + 1`.  The `+1` is slack: `gramEntry_bitLen_le_of_rows_sharp`
gives `2b + Nat.size m`. -/
theorem gramEntry_bitLen_le_of_rows {m ω b : ℕ} (Z : Matrix (Fin m) (Fin (2 * ω)) ℤ)
    (hZ : ∀ i j, bitLenInt (Z i j) ≤ b) (i j : Fin (2 * ω)) :
    bitLenInt ((Zᵀ * Z) i j) ≤ 2 * b + Nat.size m + 1 := by
  have h := gramEntry_bitLen_le_of_rows_sharp Z hZ i j
  exact le_trans h (Nat.le_succ _)

/-- **Logarithmic form.**  If the row count is bounded by `2 ^ r`, the Gram
entry has at most `2b + r + 1` bits.  (`m ≤ 2 ^ r` gives
`Nat.size m ≤ r + 1`; the bound on `m` is not strict, so one extra bit is
unavoidable at `m = 2 ^ r`.) -/
theorem gramEntry_bitLen_le_of_rows_log {m ω b : ℕ} (Z : Matrix (Fin m) (Fin (2 * ω)) ℤ)
    (hZ : ∀ i j, bitLenInt (Z i j) ≤ b) (r : ℕ) (hm : m ≤ 2 ^ r)
    (i j : Fin (2 * ω)) :
    bitLenInt ((Zᵀ * Z) i j) ≤ 2 * b + r + 1 := by
  have h := gramEntry_bitLen_le_of_rows_sharp Z hZ i j
  have hsize : Nat.size m ≤ r + 1 := by
    rw [Nat.size_le]
    calc m ≤ 2 ^ r := hm
      _ < 2 ^ (r + 1) :=
          Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self r)
  calc bitLenInt ((Zᵀ * Z) i j) ≤ 2 * b + Nat.size m := h
    _ ≤ 2 * b + (r + 1) := Nat.add_le_add_left hsize (2 * b)
    _ = 2 * b + r + 1 := by ring

/-! ## 3.  Axiom audit (stripped on promotion) -/


end Q1Paper.ScratchGramRows
