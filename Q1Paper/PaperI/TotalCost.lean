
import Q1Paper.PaperI.ComplexityCounts
import Q1Paper.PaperI.TauMConst

/-!
Q1Paper/PaperI/TotalCost.lean

**Total bit cost of the Bareiss field operations: `O(n^27 * L^4)`, not `O(n^21 * L^2)`.**

The requested headline was

    bareissFieldOpCount n * fieldOpBitCost .div B B <= 20000000 * n ^ 21 * L ^ 2
      (under `3 <= n`, `2 <= L`, `B <= 123 * n ^ 6 * L`).

That statement is **false**, and not merely by a constant: on that region the left
side grows like `n ^ 27 * L ^ 4`, so no constant whatsoever can replace
`20000000`.  The arithmetic reason is that `CostCore.fieldOpBitCost` for `div` is
*quartic* in `B`,

    fieldOpBitCost .div B B = 2 * B + 64 * (B + 1) ^ 4        (`rfl` + `ring`),

because the `div` case squares `a * b + a + b + 1`.  With
`bareissFieldOpCount n <= 4 * n ^ 3` and `B <= 123 * n ^ 6 * L` this yields
`n ^ 3 * (n ^ 6 * L) ^ 4 = n ^ 27 * L ^ 4`.  The exponent pair `(21, 2)` would
require the per-operation cost to be merely *quadratic* in `B` (the `add`/`sub`
envelope), which is not what `div` charges.

Concrete counterexample (checked below by `decide`), at the *smallest* admissible
parameters `n = 3`, `L = 2`, `B = 123 * 3 ^ 6 * 2 = 179334`:

* `bareissFieldOpCount 3 = 56`;
* `fieldOpBitCost .div B B = 66197288767886909019334`;
* left side `= 3707048171001666905082704`;
* right side `= 20000000 * 3 ^ 21 * 2 ^ 2 = 836828256240000000`;

so the left side exceeds the right side by a factor of about `4.43 * 10 ^ 6`.

What this file proves instead (all kernel-checked, no `sorry`, no new axioms):

* `fieldOpBitCost_div_apply`      : the definitional unfolding (a `rfl`);
* `fieldOpBitCost_div_eq`         : `fieldOpBitCost .div B B = 2 * B + 64 * (B + 1) ^ 4`;
* `fieldOpBitCost_div_le_quartic` : `fieldOpBitCost .div B B <= 66 * (B + 1) ^ 4`
  for **every** `B` (no side condition, so `B = 0` needs no separate case);
* `le_pow_four`                   : `x <= x ^ 4`;
* **`bareiss_total_bit_cost_le`** (headline, corrected exponents):
  `bareissFieldOpCount n * fieldOpBitCost .div B B <= 10 ^ 12 * n ^ 27 * L ^ 4`
  under the *same* hypotheses `3 <= n`, `2 <= L`, `B <= 123 * n ^ 6 * L`.
  The exact constant produced by this route is
  `4 * 66 * 16 * 123 ^ 4 = 966817171584`, rounded up to `10 ^ 12`; it is *not*
  inflated beyond that rounding;
* `bareiss_total_bit_cost_le_tauM` : the same bound with `B := tauM M (bitLenMat M)`,
  where `B <= 123 * n ^ 6 * L` is supplied by
  `TauMConst.tauM_le_paper_constant` (the reuse of the Claim 13 constant);
* `bareissFieldOpCount_three`     : `bareissFieldOpCount 3 = 56`;
* `requested_constant_fails`      : the requested inequality fails at
  `n = 3`, `L = 2`, `B = 123 * 3 ^ 6 * 2` (closed, by `decide`);
* `bareiss_total_bit_cost_le_n21_L2_false` : therefore the requested universally
  quantified statement is false.

Check with
`lake env lean Q1Paper/PaperI/TotalCost.lean`.
-/


open Q1Paper.PaperI

namespace Q1Paper.PaperI.ComplexityCounts

/-! ## 1.  The per-operation cost of one division -/

/-- The `div` branch of `CostCore.fieldOpBitCost`, unfolded definitionally. -/
theorem fieldOpBitCost_div_apply (B : ℕ) :
    Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div B B
      = B + B + 64 * (B * B + B + B + 1) ^ 2 := rfl

/-- The same cost in the form that exhibits the quartic growth:
`2 * B + 64 * (B + 1) ^ 4` (since `B * B + B + B + 1 = (B + 1) ^ 2`). -/
theorem fieldOpBitCost_div_eq (B : ℕ) :
    Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div B B
      = 2 * B + 64 * (B + 1) ^ 4 := by
  rw [fieldOpBitCost_div_apply]
  ring

/-- `x <= x ^ 4` for every natural number. -/
theorem le_pow_four (x : ℕ) : x ≤ x ^ 4 := by
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h
    norm_num
  · calc x = x * 1 := (Nat.mul_one x).symm
      _ ≤ x * x ^ 3 := Nat.mul_le_mul_left x (Nat.succ_le_of_lt (pow_pos h 3))
      _ = x ^ 4 := by ring

/-- **Quartic envelope of one division at operand bit length `B`.**
`2 * B + 64 * (B + 1) ^ 4 <= 66 * (B + 1) ^ 4`, so the `2 * B` reading cost is
absorbed: no hypothesis on `B` is needed. -/
theorem fieldOpBitCost_div_le_quartic (B : ℕ) :
    Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div B B ≤ 66 * (B + 1) ^ 4 := by
  rw [fieldOpBitCost_div_eq]
  have h2B : 2 * B ≤ 2 * (B + 1) ^ 4 :=
    Nat.mul_le_mul_left 2 (le_trans (Nat.le_succ B) (le_pow_four (B + 1)))
  calc 2 * B + 64 * (B + 1) ^ 4
      ≤ 2 * (B + 1) ^ 4 + 64 * (B + 1) ^ 4 := Nat.add_le_add_right h2B _
    _ = 66 * (B + 1) ^ 4 := by ring

/-! ## 2.  The corrected total bound -/

/-- **Total bit cost of the Bareiss field operations, `O(n ^ 27 * L ^ 4)`.**

`bareissFieldOpCount n` operations, each of the quartic cost
`fieldOpBitCost .div B B <= 66 * (B + 1) ^ 4`, with `B + 1 <= 2 * (123 * n ^ 6 * L)`
(since `1 <= 123 * n ^ 6 * L`), give

`4 * n ^ 3 * 66 * (2 * 123 * n ^ 6 * L) ^ 4 = (4 * 66 * 16 * 123 ^ 4) * n ^ 27 * L ^ 4`,

and `4 * 66 * 16 * 123 ^ 4 = 966817171584 <= 1000000000000`.

The exponent pair of the requested statement, `n ^ 21 * L ^ 2`, is **not**
reachable: the left side is `Theta(n ^ 27 * L ^ 4)` on this region (see
`bareiss_total_bit_cost_le_n21_L2_false` for the refutation). -/
theorem bareiss_total_bit_cost_le {n L B : ℕ} (hn : 3 ≤ n) (hL : 2 ≤ L)
    (hB : B ≤ 123 * n ^ 6 * L) :
    Q1Paper.PaperI.ComplexityCounts.bareissFieldOpCount n *
        Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div B B
      ≤ 1000000000000 * n ^ 27 * L ^ 4 := by
  have hn0 : 0 < n := by omega
  have hL0 : 0 < L := by omega
  -- `1 <= 123 * n ^ 6 * L`
  have hXpos : 0 < 123 * n ^ 6 * L :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos hn0 6)) hL0
  have hX1 : 1 ≤ 123 * n ^ 6 * L := Nat.succ_le_of_lt hXpos
  -- `B + 1 <= 2 * (123 * n ^ 6 * L)`
  have hB1 : B + 1 ≤ 2 * (123 * n ^ 6 * L) := by
    have h := Nat.add_le_add hB hX1
    calc B + 1 ≤ 123 * n ^ 6 * L + 123 * n ^ 6 * L := h
      _ = 2 * (123 * n ^ 6 * L) := by ring
  have hpow : (B + 1) ^ 4 ≤ (2 * (123 * n ^ 6 * L)) ^ 4 := Nat.pow_le_pow_left hB1 4
  have hcost : Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div B B
      ≤ 66 * (B + 1) ^ 4 := fieldOpBitCost_div_le_quartic B
  calc Q1Paper.PaperI.ComplexityCounts.bareissFieldOpCount n *
        Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div B B
      ≤ (4 * n ^ 3) * (66 * (B + 1) ^ 4) :=
        Nat.mul_le_mul (bareiss_field_op_count_le n) hcost
    _ ≤ (4 * n ^ 3) * (66 * (2 * (123 * n ^ 6 * L)) ^ 4) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 66 hpow)
    _ = (4 * 66 * 16 * 123 ^ 4) * (n ^ 27 * L ^ 4) := by ring
    _ ≤ 1000000000000 * (n ^ 27 * L ^ 4) :=
        Nat.mul_le_mul_right _ (by norm_num : 4 * 66 * 16 * 123 ^ 4 ≤ 1000000000000)
    _ = 1000000000000 * n ^ 27 * L ^ 4 := by ring

/-- **The same bound at the Claim 13 scale `tauM M (bitLenMat M)`.**

This is the intended use: `TauMConst.tauM_le_paper_constant` supplies the
hypothesis `B <= 123 * n ^ 6 * L` for `B = tauM M (bitLenMat M)`, and the
total cost is then `O(n ^ 27 * L ^ 4)` (not `O(n ^ 21 * L ^ 2)`). -/
theorem bareiss_total_bit_cost_le_tauM {m n L : ℕ} (M : Matrix (Fin m) (Fin n) ℚ)
    (hLm : bitLenMat M ≤ L) (hn : 3 ≤ n) (hL : 2 ≤ L) :
    Q1Paper.PaperI.ComplexityCounts.bareissFieldOpCount n *
        Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div
          (tauM M (bitLenMat M)) (tauM M (bitLenMat M))
      ≤ 1000000000000 * n ^ 27 * L ^ 4 :=
  bareiss_total_bit_cost_le hn hL (tauM_le_paper_constant M hLm hn hL)

/-! ## 3.  The requested `n ^ 21 * L ^ 2` form is false -/

/-- `bareissFieldOpCount 3 = 56` (`= 4 * (3 ^ 2 + 2 ^ 2 + 1 ^ 2)`). -/
theorem bareissFieldOpCount_three : bareissFieldOpCount 3 = 56 := by
  decide

/-- **The requested inequality fails at the smallest admissible parameters.**
At `n = 3`, `L = 2`, `B = 123 * 3 ^ 6 * 2 = 179334` the left side is
`3707048171001666905082704` while the right side is `836828256240000000`. -/
theorem requested_constant_fails :
    ¬ (bareissFieldOpCount 3 *
        Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div
          (123 * 3 ^ 6 * 2) (123 * 3 ^ 6 * 2)
      ≤ 20000000 * 3 ^ 21 * 2 ^ 2) := by
  rw [bareissFieldOpCount_three]
  decide

/-- **The universally quantified statement requested as the headline is false.**
No constant can work, because the left side is `Theta(n ^ 27 * L ^ 4)` on the
region `3 <= n`, `2 <= L`, `B <= 123 * n ^ 6 * L`; the particular constant
`20000000` already fails at `n = 3`, `L = 2`, `B = 123 * 3 ^ 6 * 2`. -/
theorem bareiss_total_bit_cost_le_n21_L2_false :
    ¬ (∀ (n L B : ℕ), 3 ≤ n → 2 ≤ L → B ≤ 123 * n ^ 6 * L →
        Q1Paper.PaperI.ComplexityCounts.bareissFieldOpCount n *
            Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div B B
          ≤ 20000000 * n ^ 21 * L ^ 2) := by
  intro h
  exact requested_constant_fails
    (h 3 2 (123 * 3 ^ 6 * 2) (by norm_num) (by norm_num) (by norm_num))

end Q1Paper.PaperI.ComplexityCounts
