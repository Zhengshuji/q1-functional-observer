
import Q1Paper.PaperI.ComplexityCounts

/-!
Q1Paper/PaperI/ExactDiv.lean

**Charging the Bareiss divisions as exact integer divisions: a quadratic per-operation
cost, hence `O(n^15 * L^2)` total.**

Why this module exists, and why the charge changes
==================================================

`CostCore.fieldOpBitCost .div B B = 2 * B + 64 * (B + 1) ^ 4`
(`fieldOpBitCost_div_eq`) models a **general rational division**: "multiply out the
denominators, then normalise", so numerator and denominator of the resulting fraction both
have about `B * B` bits and the schoolbook normalisation is *quartic* in `B`.  For a
division in `Q` that is the right charge; e.g. Gaussian elimination over `Q` genuinely
grows denominators, and `PaperI/TotalCost.lean` records the resulting `n ^ 27 * L ^ 4`
total.

It is **not** the right charge for the Bareiss elimination steps of this paper.  There,
every division is an *exact integer* division: the fraction-free tableau of an integer
matrix has denominator `1` in every entry on the nonzero-leading-minor locus, which this
project already proves as

    `Q1Paper.PaperI.ComplexityCounts.bareiss_entry_den_eq_one`
    (every tableau entry is a bordered minor of `A` -- `tab_entry_eq_bMinor` -- hence an
     integer; `tab_entry_den_eq_one_of_le_one` covers the hypothesis-free steps `k <= 1`).

So the dividend is an integer of at most `2 * B` bits (the border product
`a_kk * a_ij - a_ik * a_kj` of two `<= B`-bit entries) and the divisor is an integer of at
most `B` bits (`BareissAssemble.tab_entry_bitLen_inputLen` bounds the numerator; the
denominator is `1`).  The schoolbook cost of dividing a `<= 2B`-bit integer by a `<= B`-bit
integer is **quadratic** in `B` -- exactly the envelope the `add`/`sub` branches of
`fieldOpBitCost` use.  Hence

    exactDivCost B = 2 * B + 64 * (2 * B + 1) ^ 2,

whose second summand is the `(dividend bits + divisor bits + 1) ^ 2` schoolbook square, and
the first is the operand reads.  `exactDivCost_le_add_envelope` shows it is *literally* the
`add`/`sub` envelope at `(B, B)`.

The two charges are charges for **different operations** and must not be conflated:
  * `exactDivCost`        -- Bareiss / fraction-free: `den = 1`, integer division,
    quadratic in `B`; this is what the `n ^ 15 * L ^ 2` (resp. `n ^ 21 * L ^ 2`) total below
    uses;
  * `fieldOpBitCost .div` -- general rational division with gcd normalisation, quartic in
    `B`; this remains the right charge for a general division in `Q`, and it is what
    `PaperI/TotalCost.lean` bounds.  The difference is the modelling step, not a slack
    choice: `den = 1` removes the quartic factor.

Contents
========
§1  The per-division cost.
  * `exactDivCost`                  : the definition above;
  * `exactDivCost_le_add_envelope`  : `exactDivCost B <= fieldOpBitCost .add B B` (an equality);
  * `exactDivCost_le_odd_quadratic` : `<= 65 * (2 * B + 1) ^ 2` (no side condition; the sharp
    form used for the aggregation);
  * `exactDivCost_le_quadratic`     : `<= 1000 * (B + 1) ^ 2` (no side condition).

§2  A sharper operation count.
  * `three_mul_bareissFieldOpCount_le` : `3 * bareissFieldOpCount n <= 7 * n ^ 3` for `3 <= n`,
    improving `bareiss_field_op_count_le` (`4 * n ^ 3`) by the factor `7 / 3`.

§3  The total bit cost, with the exact-division charge.
  * `bareiss_total_bit_cost_le_quadratic` : `bareissFieldOpCount n * exactDivCost B <=
    10 ^ 7 * n ^ 15 * L ^ 2` under `3 <= n`, `2 <= L`, `B <= 123 * n ^ 6 * L`;
  * `pow15_le_pow21` / `bareiss_total_bit_cost_le_n21_L2` : the requested
    `10 ^ 6 * n ^ 21 * L ^ 2` form, which is a corollary since `n ^ 15 <= n ^ 21`.

§4  Honesty: the `10 ^ 6 * n ^ 15 * L ^ 2` form is false.
  * `bareissFieldOpCount_three_eq` : `bareissFieldOpCount 3 = 56`;
  * `exactDivCost_one_million_fails` : `56 * exactDivCost (123 * 3 ^ 6 * 2) =
    461058150480032 > 1000000 * 3 ^ 15 * 2 ^ 2 = 57395628000000`;
  * `bareiss_total_bit_cost_le_quadratic_one_million_false` : therefore the same statement
    with the constant `10 ^ 6` is not merely hard but **false**.

Constants, honestly
===================
The route below gives the constant `7 * 65 * 247 ^ 2 = 27759095` for
`3 * (total) / (n ^ 15 * L ^ 2)`, i.e. `27759095 / 3 = 9253031.67` for the total itself; it
is rounded up to the round value `10 ^ 7` and not inflated beyond that rounding.  The true
supremum of `total / (n ^ 15 * L ^ 2)` on the region is about `8.03 * 10 ^ 6` (attained at
the smallest admissible parameters `n = 3`, `L = 2`, `B = 123 * 3 ^ 6 * 2`, see §4), so
`10 ^ 6` cannot work for the `n ^ 15` form, while the `n ^ 21` form has ample room:
`10 ^ 6 * n ^ 21` beats `10 ^ 7 * n ^ 15` as soon as `10 <= n ^ 6`.

This is the same phenomenon as in `PaperI/TotalCost.lean` (where the quartic `div` charge
gave `n ^ 27 * L ^ 4` and refuted `n ^ 21 * L ^ 2`): the per-operation cost being
*quadratic* in `B` buys the exponent pair `(15, 2)`.

No `sorry`, no `admit`, no new axioms.  Check with
`lake env lean Q1Paper/PaperI/ExactDiv.lean`.
-/


namespace Q1Paper.PaperI.ComplexityCounts

/-! ## 1.  The per-division cost of an exact integer division -/

/-- The cost of one exact integer division of a (`<= 2 * B`)-bit numerator by a `B`-bit
divisor, plus the operand reads.  This is the same quadratic envelope the `add`/`sub`
branches use.

This is the honest per-division charge for a Bareiss update
`(a_kk * a_ij - a_ik * a_kj) / d`: the quotient is an exact integer division because
`d = Delta (k+1)` divides the border product, and the tableau of an integer matrix has
`den = 1` (`bareiss_entry_den_eq_one`).  It is **not** a substitute for
`fieldOpBitCost .div`, which charges a general rational division; see the file header. -/
def exactDivCost (B : ℕ) : ℕ := 2 * B + 64 * (2 * B + 1) ^ 2

/-- `exactDivCost` is *literally* the `add`/`sub` envelope of `CostCore` at bit lengths
`(B, B)`: `B + B + 64 * (B + B + 1) ^ 2 = 2 * B + 64 * (2 * B + 1) ^ 2`. -/
theorem exactDivCost_le_add_envelope (B : ℕ) :
    exactDivCost B ≤ Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.add B B := by
  refine le_of_eq ?_
  simp only [exactDivCost, Q1Complexity.fieldOpBitCost]
  ring

/-- **The sharp quadratic form used below**: `2 * B + 64 * (2B+1) ^ 2 <= 65 * (2B+1) ^ 2`,
because the `2 * B` read cost is at most `(2 * B + 1) ^ 2`.  No side condition on `B`. -/
theorem exactDivCost_le_odd_quadratic (B : ℕ) :
    exactDivCost B ≤ 65 * (2 * B + 1) ^ 2 := by
  unfold exactDivCost
  have hP : 2 * B ≤ (2 * B + 1) ^ 2 := by
    have h1 : 2 * B + 1 ≤ (2 * B + 1) ^ 2 := by
      calc 2 * B + 1 = (2 * B + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (2 * B + 1) * (2 * B + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (2 * B + 1) ^ 2 := by ring
    omega
  calc 2 * B + 64 * (2 * B + 1) ^ 2
      ≤ (2 * B + 1) ^ 2 + 64 * (2 * B + 1) ^ 2 := Nat.add_le_add_right hP _
    _ = 65 * (2 * B + 1) ^ 2 := by ring

/-- **The round quadratic envelope**: `exactDivCost B <= 1000 * (B + 1) ^ 2` for every `B`
(no side condition), by `2 * B + 1 <= 2 * (B + 1)`. -/
theorem exactDivCost_le_quadratic (B : ℕ) : exactDivCost B ≤ 1000 * (B + 1) ^ 2 := by
  have hb : 2 * B + 1 ≤ 2 * (B + 1) := by omega
  have h2 : (2 * B + 1) ^ 2 ≤ 4 * (B + 1) ^ 2 := by
    calc (2 * B + 1) ^ 2 ≤ (2 * (B + 1)) ^ 2 := Nat.pow_le_pow_left hb 2
      _ = 4 * (B + 1) ^ 2 := by ring
  calc exactDivCost B ≤ 65 * (2 * B + 1) ^ 2 := exactDivCost_le_odd_quadratic B
    _ ≤ 65 * (4 * (B + 1) ^ 2) := Nat.mul_le_mul_left 65 h2
    _ = 260 * (B + 1) ^ 2 := by ring
    _ ≤ 1000 * (B + 1) ^ 2 := Nat.mul_le_mul_right _ (by norm_num : 260 ≤ 1000)

/-! ## 2.  A sharper operation count -/

/-- **A sharper cubic bound on the field-operation count**: `3 * bareissFieldOpCount n ≤
7 * n ^ 3` for `3 ≤ n`.

From `6 * bareissUpdateCount n = n (n+1) (2n+1)` (`bareissUpdateCount_mul_six`) we get
`3 * bareissFieldOpCount n = 2 n (n+1) (2n+1) = 4 n ^ 3 + 6 n ^ 2 + 2 n`, and
`6 n ^ 2 + 2 n ≤ 3 n ^ 3` for `n ≥ 3`; so the count is at most `(7/3) n ^ 3`, improving
`bareiss_field_op_count_le` (`4 * n ^ 3`) by the factor `7/3`. -/
theorem three_mul_bareissFieldOpCount_le {n : ℕ} (hn : 3 ≤ n) :
    3 * bareissFieldOpCount n ≤ 7 * n ^ 3 := by
  unfold bareissFieldOpCount
  have h := bareissUpdateCount_mul_six n
  have e : 3 * (4 * bareissUpdateCount n) = 2 * (6 * bareissUpdateCount n) := by ring
  rw [e, h]
  nlinarith

/-! ## 3.  The total bit cost with the exact-division charge -/

/-- **Total bit cost of the Bareiss elimination with the exact-division cost,
`O(n ^ 15 * L ^ 2)`.**

`bareissFieldOpCount n` exact integer divisions, each of the quadratic cost
`exactDivCost B <= 65 * (2 * B + 1) ^ 2`, with `2 * B + 1 <= 247 * (n ^ 6 * L)` (from
`B <= 123 * n ^ 6 * L` and `1 <= n ^ 6 * L`), and `3 * bareissFieldOpCount n <= 7 * n ^ 3`,
give

`3 * (bareissFieldOpCount n * exactDivCost B) <= 7 * n ^ 3 * 65 * (247 * n ^ 6 * L) ^ 2`
`  = (7 * 65 * 247 ^ 2) * (n ^ 15 * L ^ 2) = 27759095 * n ^ 15 * L ^ 2`,

and `27759095 <= 3 * 10 ^ 7`.  See `bareiss_total_bit_cost_le_quadratic_one_million_false`
for why the constant cannot be `10 ^ 6`. -/
theorem bareiss_total_bit_cost_le_quadratic {n L B : ℕ} (hn : 3 ≤ n) (hL : 2 ≤ L)
    (hB : B ≤ 123 * n ^ 6 * L) :
    Q1Paper.PaperI.ComplexityCounts.bareissFieldOpCount n * exactDivCost B
      ≤ 10000000 * n ^ 15 * L ^ 2 := by
  have hn0 : 0 < n := by omega
  have hL0 : 0 < L := by omega
  -- `1 <= n ^ 6 * L`
  have hN1 : 1 ≤ n ^ 6 * L :=
    Nat.succ_le_of_lt (Nat.mul_pos (pow_pos hn0 6) hL0)
  -- `2 * B + 1 <= 247 * (n ^ 6 * L)`
  have h2B : 2 * B + 1 ≤ 247 * (n ^ 6 * L) := by
    have h1 : B ≤ 123 * (n ^ 6 * L) := by
      calc B ≤ 123 * n ^ 6 * L := hB
        _ = 123 * (n ^ 6 * L) := by ring
    linarith
  have hcost : exactDivCost B ≤ 65 * (2 * B + 1) ^ 2 := exactDivCost_le_odd_quadratic B
  have hpow : (2 * B + 1) ^ 2 ≤ (247 * (n ^ 6 * L)) ^ 2 := Nat.pow_le_pow_left h2B 2
  have hcnt : 3 * bareissFieldOpCount n ≤ 7 * n ^ 3 := three_mul_bareissFieldOpCount_le hn
  -- the numerical core
  have hnum : (7 * n ^ 3) * (65 * (247 * (n ^ 6 * L)) ^ 2)
      ≤ 3 * (10000000 * n ^ 15 * L ^ 2) := by
    have e1 : (7 * n ^ 3) * (65 * (247 * (n ^ 6 * L)) ^ 2) = 27759095 * (n ^ 15 * L ^ 2) := by
      ring
    have e2 : 3 * (10000000 * n ^ 15 * L ^ 2) = 30000000 * (n ^ 15 * L ^ 2) := by ring
    rw [e1, e2]
    exact Nat.mul_le_mul_right _ (by norm_num : 27759095 ≤ 30000000)
  have hmain : 3 * (Q1Paper.PaperI.ComplexityCounts.bareissFieldOpCount n * exactDivCost B)
      ≤ 3 * (10000000 * n ^ 15 * L ^ 2) := by
    calc 3 * (Q1Paper.PaperI.ComplexityCounts.bareissFieldOpCount n * exactDivCost B)
        = (3 * Q1Paper.PaperI.ComplexityCounts.bareissFieldOpCount n) * exactDivCost B := by
          ring
      _ ≤ (7 * n ^ 3) * (65 * (2 * B + 1) ^ 2) := Nat.mul_le_mul hcnt hcost
      _ ≤ (7 * n ^ 3) * (65 * (247 * (n ^ 6 * L)) ^ 2) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 65 hpow)
      _ ≤ 3 * (10000000 * n ^ 15 * L ^ 2) := hnum
  exact (Nat.le_of_mul_le_mul_left hmain (by norm_num : 0 < 3))

/-- `n ^ 15 <= n ^ 21` for `1 <= n`. -/
theorem pow15_le_pow21 {n : ℕ} (hn : 1 ≤ n) : n ^ 15 ≤ n ^ 21 := by
  have h6 : 1 ≤ n ^ 6 :=
    Nat.succ_le_of_lt (pow_pos (by omega : 0 < n) 6)
  calc n ^ 15 = n ^ 15 * 1 := (Nat.mul_one _).symm
    _ ≤ n ^ 15 * n ^ 6 := Nat.mul_le_mul_left _ h6
    _ = n ^ 21 := by ring

/-- **The corollary the paper wants, `10 ^ 6 * n ^ 21 * L ^ 2`.**

Since `n ^ 15 <= n ^ 21` (for `n >= 1`), the `10 ^ 7 * n ^ 15 * L ^ 2` bound of
`bareiss_total_bit_cost_le_quadratic` implies `10 ^ 6 * n ^ 21 * L ^ 2`: it suffices that
`10 * n ^ 15 <= n ^ 21`, i.e. `10 <= n ^ 6`, which holds for `n >= 3`. -/
theorem bareiss_total_bit_cost_le_n21_L2 {n L B : ℕ} (hn : 3 ≤ n) (hL : 2 ≤ L)
    (hB : B ≤ 123 * n ^ 6 * L) :
    Q1Paper.PaperI.ComplexityCounts.bareissFieldOpCount n * exactDivCost B
      ≤ 1000000 * n ^ 21 * L ^ 2 := by
  have hbase := bareiss_total_bit_cost_le_quadratic hn hL hB
  have hn6 : 10 ≤ n ^ 6 := by
    calc 10 ≤ 3 ^ 6 := by norm_num
      _ ≤ n ^ 6 := Nat.pow_le_pow_left hn 6
  have hstep : 10000000 * n ^ 15 * L ^ 2 ≤ 1000000 * n ^ 21 * L ^ 2 := by
    have h1 : 10 * n ^ 15 ≤ n ^ 21 := by
      calc 10 * n ^ 15 = n ^ 15 * 10 := by ring
        _ ≤ n ^ 15 * n ^ 6 := Nat.mul_le_mul_left _ hn6
        _ = n ^ 21 := by ring
    calc 10000000 * n ^ 15 * L ^ 2
        = 1000000 * (10 * n ^ 15) * L ^ 2 := by ring
      _ ≤ 1000000 * n ^ 21 * L ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 1000000 h1) (le_refl (L ^ 2))
  exact le_trans hbase hstep

/-! ## 4.  Honesty: `10 ^ 6 * n ^ 15 * L ^ 2` is false -/

/-- `bareissFieldOpCount 3 = 4 * (3 ^ 2 + 2 ^ 2 + 1 ^ 2) = 56`. -/
theorem bareissFieldOpCount_three_eq : bareissFieldOpCount 3 = 56 := by
  decide

/-- **The requested `10 ^ 6 * n ^ 15 * L ^ 2` inequality fails at the smallest admissible
parameters.**  At `n = 3`, `L = 2`, `B = 123 * 3 ^ 6 * 2 = 179334` the left side is
`56 * exactDivCost 179334 = 461058150480032`, while the right side is
`1000000 * 3 ^ 15 * 2 ^ 2 = 57395628000000`. -/
theorem exactDivCost_one_million_fails :
    ¬ (Q1Paper.PaperI.ComplexityCounts.bareissFieldOpCount 3
          * exactDivCost (123 * 3 ^ 6 * 2)
        ≤ 1000000 * 3 ^ 15 * 2 ^ 2) := by
  rw [bareissFieldOpCount_three_eq]
  decide

/-- **The `10 ^ 6 * n ^ 15 * L ^ 2` form of the headline is false.**  This is why the
headline above carries the constant `10 ^ 7`: the true supremum of
`total / (n ^ 15 * L ^ 2)` on the region is about `8.03 * 10 ^ 6`, so `10 ^ 6` has no
chance.  (The `n ^ 21` form is a different matter -- see
`bareiss_total_bit_cost_le_n21_L2`.) -/
theorem bareiss_total_bit_cost_le_quadratic_one_million_false :
    ¬ (∀ (n L B : ℕ), 3 ≤ n → 2 ≤ L → B ≤ 123 * n ^ 6 * L →
        Q1Paper.PaperI.ComplexityCounts.bareissFieldOpCount n * exactDivCost B
          ≤ 1000000 * n ^ 15 * L ^ 2) := by
  intro h
  exact exactDivCost_one_million_fails
    (h 3 2 (123 * 3 ^ 6 * 2) (by norm_num) (by norm_num) (by norm_num))

end Q1Paper.PaperI.ComplexityCounts
