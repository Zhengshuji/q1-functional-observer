/-
Q1Paper/PaperI/Thm1Cond.lean

**Conditional assembly of Theorem 1 (the external real-algebraic solver is a hypothesis).**

Theorem 1 of the paper states that the fixed-order decision problem runs in
`L ^ O(q^2)` bit operations.  The internal pieces are already formalised:
Bareiss operation counts (`PaperI/ComplexityCounts.lean`), bit lengths
(`PaperI/InputLen.lean`), and the chart-count arithmetic (`PaperI/ChartCount.lean`).
What this file supplies is the *conditional* assembly: the real-algebraic
feasibility oracle (Renegar) enters as an explicitly declared hypothesis
`R : RenegarSpec`, and the theorem is proved from `R`'s three fields alone.

Contents
========
* `RenegarSpec`              : the external complexity specification;
* `theorem1_conditional`     : `∃ C d, 0 < C ∧ 0 < d ∧
                               R.totalCost q L ≤ C * (L+1)^(d*(q+1)^2)`,
  with the **explicit** witnesses `C = C0 * 241 ^ k0` and `d = 7 * k0 + 2`,
  where `C0, k0` are the constants produced by `R.cost_le`;
* `theorem1_conditional_beta_zero` : a remark showing that, as stated, the
  specification's `total_le` is *not* binding on the coefficient bit length
  (`β` is universally quantified and `totalCost` does not depend on it), so
  `β = 0` already yields `C = C0`, `d = 2`.  The main theorem above is the
  paper-shaped route (β at its worst admissible value `240 * L^7`); the remark
  records that the specification may be weaker than intended.

Proof route of `theorem1_conditional`
=====================================
Let `β := 240 * L ^ 7` (the bound furnished by `Q1Paper.beta_le_L_pow`, in the
form in which `total_le` accepts it: `1 ≤ q` gives `240 * L^7 ≤ 240*q*L^7`).
Then

  * `chartCount q L ≤ (q+1) * L^q ≤ (L+1)^(2*(q+1))`   (`R.chart_le`, `chart_count_le`);
  * `β + 1 = 240*L^7 + 1 ≤ 241*L^7`                     (`1 ≤ L^7`, since `2 ≤ L`);
    hence `costPerChart β ≤ C0 * (β+1)^k0 ≤ C0 * 241^k0 * L^(7*k0)`   (`R.cost_le`);
  * product `≤ C0 * 241^k0 * (L+1)^(2*(q+1) + 7*k0)`
    (`L ≤ L+1`, `pow_add`), and
    `2*(q+1) + 7*k0 ≤ (7*k0 + 2)*(q+1)^2`               (`Q1Paper.exp_compose`).

Hence `C = C0 * 241^k0`, `d = 7*k0 + 2`.

Honesty notes
=============
* `Q1Paper.beta_le_L_pow` has hypothesis `β ≤ 240*q*n^5*L` (with `n ≤ L`), which
  the spec's `β ≤ 240*q*L^7` does *not* imply; it is therefore not applied
  literally.  Its conclusion `β ≤ 240*L^7` is used instead, and is exactly the
  value at which `total_le` is instantiated.  The needed step
  `240*L^7 ≤ 240*q*L^7` only uses `1 ≤ q`.
* `hqn : q ≤ L` is not needed by this route (the paper uses it in
  `beta_le_L_pow`); the specification's hypothesis already carries `L^7`.
* No `sorry`, no `admit`, no new axioms.  Check with
  `lake env lean Q1Paper/PaperI/Thm1Cond.lean`.
-/

import Q1Paper.PaperI.ChartCount

/- `hqn : q ≤ L` is part of the paper's interface (`Q1Paper.beta_le_L_pow` uses it),
but the specification's hypothesis `β ≤ 240*q*L^7` is already in the `L^7` form,
so the route below only needs `1 ≤ q`.  The statement is kept verbatim, and the
unused-variable linter is silenced for this scratch file rather than weakening it. -/
set_option linter.unusedVariables false

namespace Q1Paper

/-- The external complexity specification of the real-algebraic feasibility oracle. -/
structure RenegarSpec where
  /-- number of charts for order q and input length L -/
  chartCount : ℕ → ℕ → ℕ
  /-- per-chart variable count bound -/
  vars : ℕ → ℕ → ℕ
  /-- per-chart bit cost as a function of the coefficient bit length beta -/
  costPerChart : ℕ → ℕ
  /-- total bit cost -/
  totalCost : ℕ → ℕ → ℕ
  chart_le : ∀ q L, chartCount q L ≤ (q + 1) * L ^ q
  total_le : ∀ q L β, β ≤ 240 * q * L ^ 7 → totalCost q L ≤ chartCount q L * costPerChart β
  cost_le : ∃ C0 k0 : ℕ, 0 < C0 ∧ 0 < k0 ∧ ∀ β, costPerChart β ≤ C0 * (β + 1) ^ k0

/-- `1 ≤ L ^ 7` for `2 ≤ L` (used to absorb the `+ 1` in `β + 1`). -/
private theorem one_le_pow_seven {L : ℕ} (hL : 2 ≤ L) : 1 ≤ L ^ 7 := by
  have hpos : 0 < L := by omega
  have := pow_pos hpos 7
  omega

/-- **Theorem 1, conditional on the external real-algebraic solver.**

For `1 ≤ q`, `2 ≤ L`, `q ≤ L`, the total bit cost of the Renegar-oracle route is
`R.totalCost q L ≤ C * (L + 1) ^ (d * (q + 1) ^ 2)` with the explicit witnesses
`C = C0 * 241 ^ k0` and `d = 7 * k0 + 2`, where `C0, k0` come from `R.cost_le`. -/
theorem theorem1_conditional
    (R : RenegarSpec) {q L : ℕ} (hq : 1 ≤ q) (hL : 2 ≤ L) (hqn : q ≤ L) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ R.totalCost q L ≤ C * (L + 1) ^ (d * (q + 1) ^ 2) := by
  obtain ⟨C0, k0, hC0, hk0, hcost⟩ := R.cost_le
  refine ⟨C0 * 241 ^ k0, 7 * k0 + 2, ?_, ?_, ?_⟩
  · exact Nat.mul_pos hC0 (pow_pos (by norm_num : (0 : ℕ) < 241) k0)
  · omega
  · -- Instantiate `total_le` at `β = 240 * L^7`; `1 ≤ q` makes this admissible.
    have hq240 : 240 ≤ 240 * q := by
      simpa using Nat.mul_le_mul_left 240 hq
    have hβ : 240 * L ^ 7 ≤ 240 * q * L ^ 7 :=
      Nat.mul_le_mul hq240 (le_refl (L ^ 7))
    have htot : R.totalCost q L ≤ R.chartCount q L * R.costPerChart (240 * L ^ 7) :=
      R.total_le q L (240 * L ^ 7) hβ
    -- Chart count against base `L + 1`.
    have hchart : R.chartCount q L ≤ (L + 1) ^ (2 * (q + 1)) :=
      le_trans (R.chart_le q L) (chart_count_le hq (le_refl L) hL)
    -- Per-chart cost at `β = 240 * L^7`.
    have hL7 : 1 ≤ L ^ 7 := one_le_pow_seven hL
    have hβs : 240 * L ^ 7 + 1 ≤ 241 * L ^ 7 := by
      calc 240 * L ^ 7 + 1 ≤ 240 * L ^ 7 + L ^ 7 := Nat.add_le_add_left hL7 _
        _ = 241 * L ^ 7 := by ring
    have hcostβ : R.costPerChart (240 * L ^ 7) ≤ C0 * 241 ^ k0 * L ^ (7 * k0) := by
      calc R.costPerChart (240 * L ^ 7) ≤ C0 * (240 * L ^ 7 + 1) ^ k0 := hcost _
        _ ≤ C0 * (241 * L ^ 7) ^ k0 :=
            Nat.mul_le_mul (le_refl C0) (Nat.pow_le_pow_left hβs k0)
        _ = C0 * 241 ^ k0 * L ^ (7 * k0) := by
            rw [mul_pow, pow_mul]
            ring
    -- `L^(7*k0) ≤ (L+1)^(7*k0)`.
    have hLp : L ^ (7 * k0) ≤ (L + 1) ^ (7 * k0) :=
      Nat.pow_le_pow_left (Nat.le_succ L) (7 * k0)
    have hstep :
        (L + 1) ^ (2 * (q + 1)) * (C0 * 241 ^ k0 * L ^ (7 * k0)) ≤
          (L + 1) ^ (2 * (q + 1)) * (C0 * 241 ^ k0 * (L + 1) ^ (7 * k0)) :=
      Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _) hLp)
    -- Exponent bookkeeping: `2*(q+1) + 7*k0 ≤ (7*k0+2)*(q+1)^2`.
    have hexp : 2 * (q + 1) + 7 * k0 ≤ (7 * k0 + 2) * (q + 1) ^ 2 := by
      have hq1 : 1 ≤ q + 1 := by omega
      have hsq : 1 ≤ (q + 1) ^ 2 := by
        calc 1 = 1 * 1 := by ring
          _ ≤ (q + 1) * (q + 1) := Nat.mul_le_mul hq1 hq1
          _ = (q + 1) ^ 2 := by ring
      have h1 : 7 * k0 ≤ 7 * k0 * (q + 1) ^ 2 := by
        calc 7 * k0 = 7 * k0 * 1 := by ring
          _ ≤ 7 * k0 * (q + 1) ^ 2 := Nat.mul_le_mul (le_refl _) hsq
      have hsum : 7 * k0 + 2 * q + 2 ≤ 7 * k0 * (q + 1) ^ 2 + 2 * q + 2 := by
        have h := Nat.add_le_add_right h1 (2 * q)
        exact Nat.add_le_add_right h 2
      have h2 := exp_compose (c2 := 7 * k0) (q := q)
      have h2q : 2 * (q + 1) + 7 * k0 = 7 * k0 + 2 * q + 2 := by ring
      rw [h2q]
      exact le_trans hsum h2
    have hexp' :
        (L + 1) ^ (2 * (q + 1) + 7 * k0) ≤
          (L + 1) ^ ((7 * k0 + 2) * (q + 1) ^ 2) :=
      Nat.pow_le_pow_right (by omega) hexp
    calc R.totalCost q L
        ≤ R.chartCount q L * R.costPerChart (240 * L ^ 7) := htot
      _ ≤ (L + 1) ^ (2 * (q + 1)) * (C0 * 241 ^ k0 * L ^ (7 * k0)) :=
            Nat.mul_le_mul hchart hcostβ
      _ ≤ (L + 1) ^ (2 * (q + 1)) * (C0 * 241 ^ k0 * (L + 1) ^ (7 * k0)) := hstep
      _ = C0 * 241 ^ k0 * ((L + 1) ^ (2 * (q + 1)) * (L + 1) ^ (7 * k0)) := by ring
      _ = C0 * 241 ^ k0 * (L + 1) ^ (2 * (q + 1) + 7 * k0) := by rw [← pow_add]
      _ ≤ C0 * 241 ^ k0 * (L + 1) ^ ((7 * k0 + 2) * (q + 1) ^ 2) :=
            Nat.mul_le_mul (le_refl _) hexp'

/-- **Remark on the strength of `RenegarSpec`.**

`total_le` quantifies over every `β ≤ 240*q*L^7`, while `totalCost` does not
depend on `β`; taking `β = 0` therefore gives
`totalCost q L ≤ chartCount q L * costPerChart 0 ≤ C0 * chartCount q L`,
which already yields the `L^O(q^2)` shape with `C = C0`, `d = 2`.  This shows
that, as stated, the specification does not force the per-chart cost to be
evaluated at the actual coefficient bit length.  The paper-shaped bound is
`theorem1_conditional` above. -/
theorem theorem1_conditional_beta_zero
    (R : RenegarSpec) {q L : ℕ} (hq : 1 ≤ q) (hL : 2 ≤ L) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ R.totalCost q L ≤ C * (L + 1) ^ (d * (q + 1) ^ 2) := by
  obtain ⟨C0, k0, hC0, hk0, hcost⟩ := R.cost_le
  refine ⟨C0, 2, hC0, by omega, ?_⟩
  have h0 : 0 ≤ 240 * q * L ^ 7 := by omega
  have htot : R.totalCost q L ≤ R.chartCount q L * R.costPerChart 0 := R.total_le q L 0 h0
  have hc0 : R.costPerChart 0 ≤ C0 := by
    have := hcost 0
    simpa using this
  have hchart : R.chartCount q L ≤ (L + 1) ^ (2 * (q + 1)) :=
    le_trans (R.chart_le q L) (chart_count_le hq (le_refl L) hL)
  have hexp : 2 * (q + 1) ≤ 2 * (q + 1) ^ 2 := by
    have hq1 : 1 ≤ q + 1 := by omega
    have hsq : q + 1 ≤ (q + 1) ^ 2 := by
      calc q + 1 = (q + 1) * 1 := (Nat.mul_one (q + 1)).symm
        _ ≤ (q + 1) * (q + 1) := Nat.mul_le_mul (le_refl (q + 1)) hq1
        _ = (q + 1) ^ 2 := by ring
    exact Nat.mul_le_mul (le_refl 2) hsq
  calc R.totalCost q L
      ≤ R.chartCount q L * R.costPerChart 0 := htot
    _ ≤ R.chartCount q L * C0 := Nat.mul_le_mul (le_refl _) hc0
    _ = C0 * R.chartCount q L := by ring
    _ ≤ C0 * (L + 1) ^ (2 * (q + 1)) := Nat.mul_le_mul (le_refl _) hchart
    _ ≤ C0 * (L + 1) ^ (2 * (q + 1) ^ 2) :=
        Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_right (by omega) hexp)


end Q1Paper
