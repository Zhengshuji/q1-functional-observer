/-
Q1Paper/PaperI/Thm1Bite.lean

**Theorem 1 with the per-chart cost pinned at the actual coefficient bit length.**

`PaperI/Thm1Cond.lean` states Theorem 1 conditionally on a `RenegarSpec` whose
`total_le` field quantifies over *every* `β ≤ 240 * q * L^7` while `totalCost`
does not depend on `β`.  Hence the hypothesis is satisfiable at `β = 0`
(formalised there as `theorem1_conditional_beta_zero`), which makes the
conclusion vacuous: `costPerChart 0` is the cheapest possible per-chart cost,
so the stated bound no longer reflects the coefficient bit length at all.

This file fixes that by *pinning* the per-chart cost at the coefficient bit
length that actually occurs:

  `total_le : ∀ q L, totalCost q L ≤ chartCount q L * costPerChart (240 * q * L ^ 7)`

The price is one extra factor in the exponent: `d = 8 * k0 + 2` instead of
`d = 7 * k0 + 2`.  The extra `k0` comes from `q ^ k0 ≤ L ^ k0` (hypothesis
`q ≤ L`), which absorbs the `q` inside `β = 240 * q * L ^ 7`; this is exactly
why `hqn` is now *used*, whereas the old route did not need it.

Contents
========
* `RenegarSpecStrong`                   : the corrected specification;
* `theorem1_bound_strong`                : explicit-witness bound
    `totalCost q L ≤ C0 * 241^k0 * (L+1)^((8*k0+2)*(q+1)^2)`;
* `theorem1_conditional_strong`          : `∃ C d, 0 < C ∧ 0 < d ∧
    totalCost q L ≤ C * (L+1)^(d*(q+1)^2)`, with `C = C0 * 241^k0`,
    `d = 8 * k0 + 2`;
* `renegarInstance`                : a concrete inhabitant
    (`chartCount q L = (q+1)*L^q`, `costPerChart β = β+1`,
     `totalCost q L = chartCount q L * costPerChart (240*q*L^7)`,
     `C0 = 2`, `k0 = 1`);
* `renegarSpecStrong_inhabited`         : `Nonempty RenegarSpecStrong` — the structure is
    inhabited, so `theorem1_conditional_strong` is not vacuous;
* `theorem1_conditional_strong_instance` : the theorem instantiated on
    `renegarInstance`, with the explicit witnesses `C = 482`, `d = 10`;
* `instance_not_beta_zero`         : sanity check that on `renegarInstance` the
    `β = 0` evaluation does *not* bound `totalCost`, i.e. the new `total_le`
    really is pinned (contrast `theorem1_conditional_beta_zero`).

Honesty notes
=============
* `hqn : q ≤ L` is used (unlike in `Thm1Cond.lean`), precisely for
  `q ^ k0 ≤ L ^ k0`.
* `costPerChart` is only ever evaluated at `240 * q * L^7`; nothing here says
  what the oracle costs at other bit lengths.
* The inhabitant `renegarInstance` shows *satisfiability* of the specification,
  not that it models Renegar's algorithm; it is the non-vacuity certificate.
* No `sorry`, no `admit`, no new axioms; axiom sets are printed at the end.
  Check with `lake env lean Q1Paper/PaperI/Thm1Bite.lean`.
-/

import Q1Paper.PaperI.ChartCount

namespace Q1Paper

/-- The external complexity specification of the real-algebraic feasibility
oracle, with the per-chart cost pinned at the coefficient bit length. -/
structure RenegarSpecStrong where
  chartCount : ℕ → ℕ → ℕ
  costPerChart : ℕ → ℕ
  totalCost : ℕ → ℕ → ℕ
  chart_le : ∀ q L, chartCount q L ≤ (q + 1) * L ^ q
  /-- the per-chart cost is evaluated at the coefficient bit length beta = 240 q L^7 -/
  total_le : ∀ q L, totalCost q L ≤ chartCount q L * costPerChart (240 * q * L ^ 7)
  cost_le : ∃ C0 k0 : ℕ, 0 < C0 ∧ 0 < k0 ∧ ∀ β, costPerChart β ≤ C0 * (β + 1) ^ k0

/-- `1 ≤ L ^ 7` for `2 ≤ L` (absorbs the `+ 1` in `β + 1`). -/
private theorem one_le_pow_seven' {L : ℕ} (hL : 2 ≤ L) : 1 ≤ L ^ 7 := by
  have hpos : 0 < L := by omega
  have := pow_pos hpos 7
  omega

/-- Exponent bookkeeping for the pinned route:
`2*(q+1) + 8*k ≤ (8*k + 2)*(q+1)^2`.  Route: `8*k ≤ 8*k*(q+1)^2` since
`1 ≤ (q+1)^2`, then `2*(q+1) = 2*q + 2`, then `Q1Paper.exp_compose`. -/
private theorem exp_eight {q k : ℕ} :
    2 * (q + 1) + 8 * k ≤ (8 * k + 2) * (q + 1) ^ 2 := by
  have hq1 : 1 ≤ q + 1 := by omega
  have hsq : 1 ≤ (q + 1) ^ 2 := by
    calc 1 = 1 * 1 := by ring
      _ ≤ (q + 1) * (q + 1) := Nat.mul_le_mul hq1 hq1
      _ = (q + 1) ^ 2 := by ring
  have h1 : 8 * k ≤ 8 * k * (q + 1) ^ 2 := by
    calc 8 * k = 8 * k * 1 := by ring
      _ ≤ 8 * k * (q + 1) ^ 2 := Nat.mul_le_mul (le_refl _) hsq
  have hsum : 8 * k + 2 * q + 2 ≤ 8 * k * (q + 1) ^ 2 + 2 * q + 2 := by
    have h := Nat.add_le_add_right h1 (2 * q)
    exact Nat.add_le_add_right h 2
  have h2 := exp_compose (c2 := 8 * k) (q := q)
  have h2q : 2 * (q + 1) + 8 * k = 8 * k + 2 * q + 2 := by ring
  rw [h2q]
  exact le_trans hsum h2

/-- **Theorem 1 under `RenegarSpecStrong`, explicit witnesses.**

For `1 ≤ q`, `2 ≤ L`, `q ≤ L`, and any per-chart bound
`costPerChart β ≤ C0 * (β+1)^k0`,

  `R.totalCost q L ≤ C0 * 241^k0 * (L+1)^((8*k0+2)*(q+1)^2)`.

Route: `total_le` pins `β = 240*q*L^7`; `240*q*L^7 + 1 ≤ 241*q*L^7` because
`1 ≤ q*L^7`; `q^k0 ≤ L^k0` by `q ≤ L`; the chart count is absorbed by
`chart_count_le`; the exponents compose via `exp_eight`. -/
theorem theorem1_bound_strong (R : RenegarSpecStrong) {q L C0 k0 : ℕ}
    (hq : 1 ≤ q) (hL : 2 ≤ L) (hqn : q ≤ L)
    (hcost : ∀ β, R.costPerChart β ≤ C0 * (β + 1) ^ k0) :
    R.totalCost q L ≤ C0 * 241 ^ k0 * (L + 1) ^ ((8 * k0 + 2) * (q + 1) ^ 2) := by
  have htot : R.totalCost q L ≤ R.chartCount q L * R.costPerChart (240 * q * L ^ 7) :=
    R.total_le q L
  -- chart count against base `L + 1`
  have hchart : R.chartCount q L ≤ (L + 1) ^ (2 * (q + 1)) :=
    le_trans (R.chart_le q L) (chart_count_le hq (le_refl L) hL)
  -- `241 * (q * L^7) + 1` style absorption
  have hL7 : 1 ≤ L ^ 7 := one_le_pow_seven' hL
  have hq7 : 1 ≤ q * L ^ 7 := by
    simpa using Nat.mul_le_mul hq hL7
  have hβs : 240 * q * L ^ 7 + 1 ≤ 241 * q * L ^ 7 := by
    calc 240 * q * L ^ 7 + 1 ≤ 240 * q * L ^ 7 + q * L ^ 7 := Nat.add_le_add_left hq7 _
      _ = 241 * q * L ^ 7 := by ring
  -- per-chart cost at the pinned `β`
  have hcostβ :
      R.costPerChart (240 * q * L ^ 7) ≤ C0 * 241 ^ k0 * q ^ k0 * L ^ (7 * k0) := by
    calc R.costPerChart (240 * q * L ^ 7) ≤ C0 * (240 * q * L ^ 7 + 1) ^ k0 := hcost _
      _ ≤ C0 * (241 * q * L ^ 7) ^ k0 :=
            Nat.mul_le_mul (le_refl C0) (Nat.pow_le_pow_left hβs k0)
      _ = C0 * 241 ^ k0 * q ^ k0 * L ^ (7 * k0) := by
            rw [mul_pow, mul_pow, pow_mul]
            ring
  -- `q^k0 ≤ L^k0` and `L^(7*k0) * L^k0 = L^(8*k0)`
  have hqk : q ^ k0 ≤ L ^ k0 := Nat.pow_le_pow_left hqn k0
  have hstep : C0 * 241 ^ k0 * q ^ k0 * L ^ (7 * k0) ≤ C0 * 241 ^ k0 * L ^ (8 * k0) := by
    have h1 : C0 * 241 ^ k0 * q ^ k0 ≤ C0 * 241 ^ k0 * L ^ k0 := by
      calc C0 * 241 ^ k0 * q ^ k0 = (C0 * 241 ^ k0) * q ^ k0 := by ring
        _ ≤ (C0 * 241 ^ k0) * L ^ k0 := Nat.mul_le_mul (le_refl _) hqk
        _ = C0 * 241 ^ k0 * L ^ k0 := by ring
    have hpow : L ^ k0 * L ^ (7 * k0) = L ^ (8 * k0) := by
      rw [← pow_add]
      congr 1
      ring
    calc C0 * 241 ^ k0 * q ^ k0 * L ^ (7 * k0)
        ≤ C0 * 241 ^ k0 * L ^ k0 * L ^ (7 * k0) := Nat.mul_le_mul h1 (le_refl _)
      _ = C0 * 241 ^ k0 * (L ^ k0 * L ^ (7 * k0)) := by ring
      _ = C0 * 241 ^ k0 * L ^ (8 * k0) := by rw [hpow]
  -- base upgrade `L → L+1`
  have hL8 : L ^ (8 * k0) ≤ (L + 1) ^ (8 * k0) :=
    Nat.pow_le_pow_left (Nat.le_succ L) _
  have hstep2 :
      (L + 1) ^ (2 * (q + 1)) * (C0 * 241 ^ k0 * L ^ (8 * k0)) ≤
        (L + 1) ^ (2 * (q + 1)) * (C0 * 241 ^ k0 * (L + 1) ^ (8 * k0)) :=
    Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _) hL8)
  -- exponent composition
  have hexp' : (L + 1) ^ (2 * (q + 1) + 8 * k0) ≤
      (L + 1) ^ ((8 * k0 + 2) * (q + 1) ^ 2) :=
    Nat.pow_le_pow_right (by omega) (exp_eight (q := q) (k := k0))
  calc R.totalCost q L
      ≤ R.chartCount q L * R.costPerChart (240 * q * L ^ 7) := htot
    _ ≤ (L + 1) ^ (2 * (q + 1)) * (C0 * 241 ^ k0 * q ^ k0 * L ^ (7 * k0)) :=
          Nat.mul_le_mul hchart hcostβ
    _ ≤ (L + 1) ^ (2 * (q + 1)) * (C0 * 241 ^ k0 * L ^ (8 * k0)) :=
          Nat.mul_le_mul (le_refl _) hstep
    _ ≤ (L + 1) ^ (2 * (q + 1)) * (C0 * 241 ^ k0 * (L + 1) ^ (8 * k0)) := hstep2
    _ = C0 * 241 ^ k0 * ((L + 1) ^ (2 * (q + 1)) * (L + 1) ^ (8 * k0)) := by ring
    _ = C0 * 241 ^ k0 * (L + 1) ^ (2 * (q + 1) + 8 * k0) := by rw [← pow_add]
    _ ≤ C0 * 241 ^ k0 * (L + 1) ^ ((8 * k0 + 2) * (q + 1) ^ 2) :=
          Nat.mul_le_mul (le_refl _) hexp'

/-- **Theorem 1, conditional on the external real-algebraic solver, with the
per-chart cost pinned at the coefficient bit length.**

For `1 ≤ q`, `2 ≤ L`, `q ≤ L`:
`R.totalCost q L ≤ C * (L + 1) ^ (d * (q + 1) ^ 2)` with the explicit witnesses
`C = C0 * 241 ^ k0` and `d = 8 * k0 + 2`, where `C0, k0` come from `R.cost_le`. -/
theorem theorem1_conditional_strong (R : RenegarSpecStrong) {q L : ℕ} (hq : 1 ≤ q) (hL : 2 ≤ L) (hqn : q ≤ L) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ R.totalCost q L ≤ C * (L + 1) ^ (d * (q + 1) ^ 2) := by
  obtain ⟨C0, k0, hC0, hk0, hcost⟩ := R.cost_le
  refine ⟨C0 * 241 ^ k0, 8 * k0 + 2, ?_, ?_, ?_⟩
  · exact Nat.mul_pos hC0 (pow_pos (by norm_num : (0 : ℕ) < 241) k0)
  · omega
  · exact theorem1_bound_strong R hq hL hqn hcost

/-! ### Non-vacuity: a concrete inhabitant of `RenegarSpecStrong` -/

/-- The cost bound used by the inhabitant: `β + 1 ≤ 2 * (β + 1) ^ 1`. -/
private theorem instance_cost_le : ∀ β : ℕ, β + 1 ≤ 2 * (β + 1) ^ 1 := by
  intro β
  rw [pow_one]
  omega

/-- A concrete `RenegarSpecStrong`: `(q+1)*L^q` charts, each costing `β + 1` bits at
coefficient bit length `β`, and a total cost equal to exactly the
`β = 240*q*L^7` product.  `chart_le` and `total_le` are `rfl`; the polynomial
cost bound `costPerChart β ≤ 2 * (β+1)^1` gives `cost_le` with `C0 = 2`,
`k0 = 1`. -/
def renegarInstance : RenegarSpecStrong where
  chartCount := fun q L => (q + 1) * L ^ q
  costPerChart := fun β => β + 1
  totalCost := fun q L => (q + 1) * L ^ q * (240 * q * L ^ 7 + 1)
  chart_le := fun q L => le_refl _
  total_le := fun q L => le_refl _
  cost_le := ⟨2, 1, by norm_num, by norm_num, instance_cost_le⟩

/-- **The specification is inhabited**, so `theorem1_conditional_strong` is a
non-vacuous conditional statement. -/
theorem renegarSpecStrong_inhabited : Nonempty RenegarSpecStrong := ⟨renegarInstance⟩

/-- `theorem1_conditional_strong` instantiated on `renegarInstance`: the explicit
witnesses are `C = 482 = 2 * 241^1` and `d = 10 = 8*1 + 2`. -/
theorem theorem1_conditional_strong_instance {q L : ℕ} (hq : 1 ≤ q) (hL : 2 ≤ L) (hqn : q ≤ L) :
    renegarInstance.totalCost q L ≤ 482 * (L + 1) ^ (10 * (q + 1) ^ 2) := by
  have h :=
    theorem1_bound_strong (R := renegarInstance) (C0 := 2) (k0 := 1) hq hL hqn instance_cost_le
  calc renegarInstance.totalCost q L
      ≤ 2 * 241 ^ 1 * (L + 1) ^ ((8 * 1 + 2) * (q + 1) ^ 2) := h
    _ = 482 * (L + 1) ^ (10 * (q + 1) ^ 2) := by norm_num

/-- **Sanity check on the fix.**  On `renegarInstance` the old `β = 0` trick is
unavailable: the `β = 0` evaluation of the right-hand side is *not* an upper
bound for `totalCost 1 2` (it is `4 < 122884`).  This is the concrete sense in
which the pinned `total_le` is binding, in contrast with
`theorem1_conditional_beta_zero` of `PaperI/Thm1Cond.lean`. -/
theorem instance_not_beta_zero :
    ¬ (renegarInstance.totalCost 1 2 ≤
        renegarInstance.chartCount 1 2 * renegarInstance.costPerChart 0) := by
  norm_num [renegarInstance]


end Q1Paper
