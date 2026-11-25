
import Q1Paper.PaperI.S06_Algorithms.ChartCount

/-!
Q1Paper/PaperI/S06_Algorithms/RenegarParams.lean

**Theorem 1 with the parameters of every chart made explicit.**

`PaperI/Thm1Bite.lean` pins the per-chart cost at the coefficient bit length
`β = 240 * q * L^7`, but its `costPerChart : ℕ → ℕ` is an arbitrary function of
the bit length alone: the chart's variable count, constraint count and degree
never occur, so "the Renegar cost of the chart" is not a function of the chart.
This file makes the parameters explicit.

  * `ChartParams` : a chart is `(vars, polys, deg)`;
  * `renegarCost p = p.vars * (p.polys + 1) ^ p.deg`;
  * `ChartSpec` : the specification, *verbatim as requested* (including the tie
    fields `params_vars_le`, `params_polys_le`, `params_deg_le` to `beta q L L`);
  * `theorem1_bound_params`, `theorem1_conditional_params` : Theorem 1 with the
    **tightened** exponent `d = 8 * k0 + 1` and witnesses `C = C0 * 241 ^ k0`.

The verbatim spec is empty
==========================
`chartSpec_empty : ¬ Nonempty ChartSpec`.  The `renegar_le` field asks for one
polynomial `C0 * (β + 1) ^ k0`, uniform in the parameter bound `β`, but
`p = (β, β, β)` satisfies all three hypotheses and has
`renegarCost p = β * (β + 1) ^ β`, which no fixed polynomial in `β + 1`
dominates.  Hence `ChartSpec` has no inhabitant, and
`theorem1_conditional_params` is *vacuous* — the same defect the review found in
`Thm1Bite.lean`, one level down.  (This is proved, not asserted.)

The repair
==========
The real charts have a *fixed* degree (the input degree `d`), while `vars` and
`polys` grow with `β`; that is exactly what makes the polynomial bound true.  So
the repaired structure `ChartSpecFixedDeg` keeps every field of `ChartSpec` and
changes only `renegar_le`, whose degree hypothesis becomes `p.deg ≤ degBound`
(plus the tie `params_deg_le_bound`).  It is inhabited
(`chartSpecFixedDeg_inhabited`), the same tightened exponent `8 * k0 + 1` is
proved for it, and the inhabitant instantiates the theorem with the explicit
numbers `C = 241`, `d = 9`.

Contents
========
* `ChartParams`, `renegarCost`, `ChartSpec`  : the verbatim interface;
* `renegarCost_le_pow`  : `renegarCost p ≤ (β+1)^(D+1)` when `p.vars ≤ β`,
  `p.polys ≤ β`, `p.deg ≤ D` — the bound that exists exactly at fixed degree;
* `exp_eight_add_one`   : `2*(q+1) + 7*k ≤ (8*k+1)*(q+1)^2` for `1 ≤ q`
  (this replaces `exp_eight` of `Thm1Bite.lean`; the `7` instead of `8` comes
  from using `β = beta q L L = 240 q L^6` rather than `240 q L^7`);
* `chart_cost_bound`    : the single arithmetic step;
* `theorem1_bound_params`       : explicit witnesses `C = C0 * 241^k0`,
  `d = 8*k0 + 1`;
* `theorem1_conditional_params` : the requested `∃ C d` statement, verbatim;
* `chartSpec_empty`             : `¬ Nonempty ChartSpec`;
* `ChartSpecFixedDeg`, `theorem1_bound_params_fixedDeg`,
  `theorem1_conditional_params_fixedDeg` : repaired spec + theorem;
* `chartSpecFixedDegInstance`, `chartSpecFixedDeg_inhabited` : all fields
  discharged (`C0 = 1`, `k0 = 1`, `degBound = 0`);
* `theorem1_conditional_params_instance` : the theorem at the inhabitant,
  `C = 241`, `d = 9`.

Honesty notes
=============
* `hn : n ≤ L` is not used: the chart parameters are evaluated at the worst case
  `n = L` (`beta q L L`), and `beta_le` at `n = L` already gives `240 q L^6`.
  The `hn`-free sharpening is `theorem1_conditional_params_no_hn`.
* `hqn : q ≤ L` is used (`q ^ k0 ≤ L ^ k0`); `hq : 1 ≤ q` is used
  (`2*(q+1) ≤ (q+1)^2` in `exp_eight_add_one`); `hL : 2 ≤ L` is used for
  `1 ≤ L^6` and for `chart_count_le`.
* `chartSpecFixedDegInstance` witnesses *satisfiability* of the repaired
  specification; it is not a model of Renegar's algorithm, and its `totalCost`
  is by construction exactly `chartCount * renegarCost`.
* No `sorry`, no `admit`, no new axioms; `#print axioms` at the end.

Check with `lake env lean Q1Paper/PaperI/RenegarParams.lean`.
-/


namespace Q1Paper

/-! ### The parameters of one chart, and its Renegar cost -/

/-- The parameters of one chart of the fixed-order algorithm. -/
structure ChartParams where
  vars : ℕ
  polys : ℕ
  deg : ℕ

/-- The Renegar cost of one chart, as a function of its parameters. -/
def renegarCost (p : ChartParams) : ℕ := p.vars * (p.polys + 1) ^ p.deg

/-- The specification of Theorem 1 with the parameters of every chart explicit.

`params q L` are the parameters of the chart chosen at order `q` and bit length
`L`; `beta q n L = 240 q n^5 L` is the coefficient bit length of the chart at
`n` variables, and the three tie fields say that the chart's `vars`, `polys`
and `deg` are all bounded by `beta q L L` (the worst case `n = L`).

`renegar_le` is the polynomial bound on the per-chart cost.  As stated it is
**unsatisfiable** (see `chartSpec_empty`); `ChartSpecFixedDeg` is the
satisfiable repair. -/
structure ChartSpec where
  /-- the parameters of the chart used at order `q` and bit length `L` -/
  params : ℕ → ℕ → ChartParams
  /-- the coefficient bit length `240 q n^5 L` -/
  beta : ℕ → ℕ → ℕ → ℕ
  chartCount : ℕ → ℕ → ℕ
  totalCost : ℕ → ℕ → ℕ
  beta_def : ∀ q n L, beta q n L = 240 * q * n ^ 5 * L
  beta_le : ∀ q n L, n ≤ L → beta q n L ≤ 240 * q * L ^ 6
  chart_le : ∀ q L, chartCount q L ≤ (q + 1) * L ^ q
  total_le : ∀ q L, totalCost q L ≤ chartCount q L * renegarCost (params q L)
  renegar_le : ∃ C0 k0 : ℕ, 0 < C0 ∧ 0 < k0 ∧
    ∀ (p : ChartParams) (β : ℕ), p.vars ≤ β → p.polys ≤ β → p.deg ≤ β →
      renegarCost p ≤ C0 * (β + 1) ^ k0
  /-- the chart's variable count is bounded by the coefficient bit length -/
  params_vars_le : ∀ q L, (params q L).vars ≤ beta q L L
  /-- the chart's constraint count is bounded by the coefficient bit length -/
  params_polys_le : ∀ q L, (params q L).polys ≤ beta q L L
  /-- the chart's degree is bounded by the coefficient bit length -/
  params_deg_le : ∀ q L, (params q L).deg ≤ beta q L L

/-! ### Arithmetic -/

/-- `1 ≤ L ^ 6` for `2 ≤ L` (absorbs the `+ 1` in `β + 1`). -/
private theorem one_le_pow_six {L : ℕ} (hL : 2 ≤ L) : 1 ≤ L ^ 6 := by
  have hpos : 0 < L := by omega
  have := pow_pos hpos 6
  omega

/-- **The polynomial bound on `renegarCost` at fixed degree.**
If `p.vars ≤ β`, `p.polys ≤ β` and `p.deg ≤ D`, then
`renegarCost p ≤ (β + 1) ^ (D + 1)`.

Route: `p.vars ≤ β + 1`, `(p.polys+1)^p.deg ≤ (β+1)^p.deg`, multiply,
and `(β+1) * (β+1)^p.deg = (β+1)^(p.deg+1) ≤ (β+1)^(D+1)`.

The bound is false with `D` replaced by `β` — that is `chartSpec_empty`. -/
theorem renegarCost_le_pow {D β : ℕ} {p : ChartParams}
    (hv : p.vars ≤ β) (hp : p.polys ≤ β) (hd : p.deg ≤ D) :
    renegarCost p ≤ (β + 1) ^ (D + 1) := by
  have h1 : (p.polys + 1) ^ p.deg ≤ (β + 1) ^ p.deg :=
    Nat.pow_le_pow_left (by omega) p.deg
  have h2 : p.vars ≤ β + 1 := by omega
  have h3 : p.deg + 1 ≤ D + 1 := by omega
  calc renegarCost p = p.vars * (p.polys + 1) ^ p.deg := rfl
    _ ≤ (β + 1) * (β + 1) ^ p.deg := Nat.mul_le_mul h2 h1
    _ = (β + 1) ^ (p.deg + 1) := by rw [pow_succ]; ring
    _ ≤ (β + 1) ^ (D + 1) := Nat.pow_le_pow_right (by omega) h3

/-- **Exponent bookkeeping for the tightened exponent.**
`2*(q+1) + 7*k ≤ (8*k + 1)*(q + 1)^2` for `1 ≤ q`.

Route: `2*(q+1) ≤ (q+1)^2` (needs `q ≥ 1`), `7*k ≤ 8*k*(q+1)^2` (needs
`1 ≤ (q+1)^2`), and `8*k*(q+1)^2 + (q+1)^2 = (8*k+1)*(q+1)^2`. -/
private theorem exp_eight_add_one {q k : ℕ} (hq : 1 ≤ q) :
    2 * (q + 1) + 7 * k ≤ (8 * k + 1) * (q + 1) ^ 2 := by
  have hQ : 2 ≤ q + 1 := by omega
  have hsq : 2 * (q + 1) ≤ (q + 1) ^ 2 := by
    calc 2 * (q + 1) = (q + 1) * 2 := by ring
      _ ≤ (q + 1) * (q + 1) := Nat.mul_le_mul (le_refl _) hQ
      _ = (q + 1) ^ 2 := by ring
  have hone : 1 ≤ (q + 1) ^ 2 := by
    have h := pow_pos (by omega : 0 < q + 1) 2
    omega
  have hk : 7 * k ≤ 8 * k * (q + 1) ^ 2 := by
    calc 7 * k ≤ 8 * k := by omega
      _ = 8 * k * 1 := (Nat.mul_one (8 * k)).symm
      _ ≤ 8 * k * (q + 1) ^ 2 := Nat.mul_le_mul (le_refl _) hone
  have hexpand : (8 * k + 1) * (q + 1) ^ 2 = 8 * k * (q + 1) ^ 2 + (q + 1) ^ 2 := by
    ring
  rw [hexpand]
  calc 2 * (q + 1) + 7 * k ≤ (q + 1) ^ 2 + 8 * k * (q + 1) ^ 2 :=
        Nat.add_le_add hsq hk
    _ = 8 * k * (q + 1) ^ 2 + (q + 1) ^ 2 := by ring

/-! ### The conditional bound -/

/-- **The single arithmetic step of Theorem 1.**

Given a chart-count bound `cc`, a total cost `tc`, a chart `p` whose Renegar
cost is at most `C0 * (β+1)^k0`, and `β ≤ 240 q L^6`, one gets

  `tc ≤ C0 * 241^k0 * (L+1)^((8*k0+1)*(q+1)^2)`.

Route: `chartCount ≤ (q+1) L^q ≤ (L+1)^(2(q+1))` (`chart_count_le`);
`β + 1 ≤ 241 q L^6` because `1 ≤ q L^6`; the power `(241 q L^6)^k0` splits into
`241^k0 q^k0 L^(6 k0)`; `q^k0 ≤ L^k0` absorbs the `q` (`q ≤ L`);
`L^(7 k0) ≤ (L+1)^(7 k0)`; the exponents compose by `exp_eight_add_one`. -/
theorem chart_cost_bound {q L C0 k0 β : ℕ} {cc tc : ℕ} {p : ChartParams}
    (hq : 1 ≤ q) (hL : 2 ≤ L) (hqn : q ≤ L)
    (hchart : cc ≤ (q + 1) * L ^ q)
    (htot : tc ≤ cc * renegarCost p)
    (hrc : renegarCost p ≤ C0 * (β + 1) ^ k0)
    (hβ : β ≤ 240 * q * L ^ 6) :
    tc ≤ C0 * 241 ^ k0 * (L + 1) ^ ((8 * k0 + 1) * (q + 1) ^ 2) := by
  have hchart' : cc ≤ (L + 1) ^ (2 * (q + 1)) :=
    le_trans hchart (chart_count_le hq (le_refl L) hL)
  have hL6 : 1 ≤ L ^ 6 := one_le_pow_six hL
  have hq6 : 1 ≤ q * L ^ 6 := by
    have h := Nat.mul_le_mul hq hL6
    simpa using h
  -- `β + 1` against `241 q L^6`
  have hβ1 : β + 1 ≤ 241 * q * L ^ 6 := by
    calc β + 1 ≤ 240 * q * L ^ 6 + q * L ^ 6 := Nat.add_le_add hβ hq6
      _ = 241 * q * L ^ 6 := by ring
  -- the per-chart cost against `C0 * 241^k0 * q^k0 * L^(6*k0)`
  have hrc' : renegarCost p ≤ C0 * 241 ^ k0 * q ^ k0 * L ^ (6 * k0) := by
    calc renegarCost p ≤ C0 * (β + 1) ^ k0 := hrc
      _ ≤ C0 * (241 * q * L ^ 6) ^ k0 :=
            Nat.mul_le_mul (le_refl C0) (Nat.pow_le_pow_left hβ1 k0)
      _ = C0 * 241 ^ k0 * q ^ k0 * L ^ (6 * k0) := by
            rw [mul_pow, mul_pow, pow_mul]
            ring
  -- absorb the `q` into the `L`
  have hqk : q ^ k0 ≤ L ^ k0 := Nat.pow_le_pow_left hqn k0
  have hstep : C0 * 241 ^ k0 * q ^ k0 * L ^ (6 * k0) ≤
      C0 * 241 ^ k0 * (L + 1) ^ (7 * k0) := by
    have h1 : C0 * 241 ^ k0 * q ^ k0 ≤ C0 * 241 ^ k0 * L ^ k0 := by
      calc C0 * 241 ^ k0 * q ^ k0 = (C0 * 241 ^ k0) * q ^ k0 := by ring
        _ ≤ (C0 * 241 ^ k0) * L ^ k0 := Nat.mul_le_mul (le_refl _) hqk
        _ = C0 * 241 ^ k0 * L ^ k0 := by ring
    have hpow : L ^ k0 * L ^ (6 * k0) = L ^ (7 * k0) := by
      rw [← pow_add]
      congr 1
      ring
    have hL7 : L ^ (7 * k0) ≤ (L + 1) ^ (7 * k0) :=
      Nat.pow_le_pow_left (Nat.le_succ L) _
    calc C0 * 241 ^ k0 * q ^ k0 * L ^ (6 * k0)
        ≤ C0 * 241 ^ k0 * L ^ k0 * L ^ (6 * k0) := Nat.mul_le_mul h1 (le_refl _)
      _ = C0 * 241 ^ k0 * (L ^ k0 * L ^ (6 * k0)) := by ring
      _ = C0 * 241 ^ k0 * L ^ (7 * k0) := by rw [hpow]
      _ ≤ C0 * 241 ^ k0 * (L + 1) ^ (7 * k0) := Nat.mul_le_mul (le_refl _) hL7
  have hexp : (L + 1) ^ (2 * (q + 1) + 7 * k0) ≤
      (L + 1) ^ ((8 * k0 + 1) * (q + 1) ^ 2) :=
    Nat.pow_le_pow_right (by omega) (exp_eight_add_one hq)
  calc tc ≤ cc * renegarCost p := htot
    _ ≤ (L + 1) ^ (2 * (q + 1)) * (C0 * 241 ^ k0 * (L + 1) ^ (7 * k0)) :=
          Nat.mul_le_mul hchart' (le_trans hrc' hstep)
    _ = C0 * 241 ^ k0 * ((L + 1) ^ (2 * (q + 1)) * (L + 1) ^ (7 * k0)) := by ring
    _ = C0 * 241 ^ k0 * (L + 1) ^ (2 * (q + 1) + 7 * k0) := by rw [← pow_add]
    _ ≤ C0 * 241 ^ k0 * (L + 1) ^ ((8 * k0 + 1) * (q + 1) ^ 2) :=
          Nat.mul_le_mul (le_refl _) hexp

/-- **Theorem 1 under `ChartSpec`, explicit witnesses.**

For `1 ≤ q`, `2 ≤ L`, `q ≤ L`, and a polynomial per-chart bound
`renegarCost p ≤ C0 * (β+1)^k0` valid for every chart whose parameters are at
most `β`,

  `R.totalCost q L ≤ C0 * 241^k0 * (L+1)^((8*k0+1)*(q+1)^2)`.

The chart's own parameters enter through `params_vars_le`, `params_polys_le`,
`params_deg_le` at `β = beta q L L`, and `beta_le` at `n = L` gives
`beta q L L ≤ 240 q L^6`. -/
theorem theorem1_bound_params (R : ChartSpec) {q L C0 k0 : ℕ}
    (hq : 1 ≤ q) (hL : 2 ≤ L) (hqn : q ≤ L)
    (hcost : ∀ (p : ChartParams) (β : ℕ), p.vars ≤ β → p.polys ≤ β → p.deg ≤ β →
      renegarCost p ≤ C0 * (β + 1) ^ k0) :
    R.totalCost q L ≤ C0 * 241 ^ k0 * (L + 1) ^ ((8 * k0 + 1) * (q + 1) ^ 2) :=
  chart_cost_bound (q := q) (L := L) (C0 := C0) (k0 := k0)
    (β := R.beta q L L) (cc := R.chartCount q L) (tc := R.totalCost q L)
    (p := R.params q L) hq hL hqn (R.chart_le q L) (R.total_le q L)
    (hcost (R.params q L) (R.beta q L L) (R.params_vars_le q L)
      (R.params_polys_le q L) (R.params_deg_le q L))
    (R.beta_le q L L (le_refl L))

/-- **Theorem 1, conditional on the parameter-explicit specification.**

`∃ C d, 0 < C ∧ 0 < d ∧ totalCost q L ≤ C * (L+1)^(d*(q+1)^2)`, with the
explicit witnesses `C = C0 * 241^k0` and `d = 8*k0 + 1`, where `C0, k0` come
from `R.renegar_le`.

`hn : n ≤ L` is part of the paper's hypothesis list but is not needed: the chart
parameters are evaluated at the worst case `n = L`.  See
`theorem1_conditional_params_no_hn` for the sharpened form.

Beware: `ChartSpec` has no inhabitant (`chartSpec_empty`), so this statement is
*vacuous*; the non-vacuous version is
`theorem1_conditional_params_fixedDeg`. -/
theorem theorem1_conditional_params (R : ChartSpec) {q n L : ℕ}
    (hq : 1 ≤ q) (hL : 2 ≤ L) (hqn : q ≤ L) (hn : n ≤ L) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ R.totalCost q L ≤ C * (L + 1) ^ (d * (q + 1) ^ 2) := by
  obtain ⟨C0, k0, hC0, hk0, hcost⟩ := R.renegar_le
  exact ⟨C0 * 241 ^ k0, 8 * k0 + 1,
    Nat.mul_pos hC0 (pow_pos (by norm_num : (0 : ℕ) < 241) k0),
    by omega,
    theorem1_bound_params R hq hL hqn hcost⟩

/-- `theorem1_conditional_params` without the unused hypothesis `n ≤ L`. -/
theorem theorem1_conditional_params_no_hn (R : ChartSpec) {q L : ℕ}
    (hq : 1 ≤ q) (hL : 2 ≤ L) (hqn : q ≤ L) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ R.totalCost q L ≤ C * (L + 1) ^ (d * (q + 1) ^ 2) :=
  theorem1_conditional_params R hq hL hqn (le_refl L)

/-! ### The verbatim specification has no inhabitant -/

/-- **`ChartSpec` is empty.**

`renegar_le` requires a single polynomial `C0 * (β+1)^k0`, uniform in the
parameter bound `β`, but `p = (β, β, β)` satisfies `p.vars, p.polys, p.deg ≤ β`
and has `renegarCost p = β * (β+1)^β`.

At `β = C0 + k0 + 1` one would get

  `(β+1)^(k0+1) = (β+1)^k0 * (β+1) ≤ (β+1)^β`
  `≤ C0 * (β+1)^k0 < (β+1)^k0 * (β+1) = (β+1)^(k0+1)`,

using `C0 < β + 1` and `k0 + 1 ≤ β`.  Contradiction. -/
theorem chartSpec_empty : ¬ Nonempty ChartSpec := by
  rintro ⟨R⟩
  obtain ⟨C0, k0, hC0, hk0, hcost⟩ := R.renegar_le
  set β := C0 + k0 + 1 with hβ
  -- the three parameter bounds hold by reflexivity, so the polynomial bound applies
  have hle : renegarCost ⟨β, β, β⟩ ≤ C0 * (β + 1) ^ k0 :=
    hcost ⟨β, β, β⟩ β (le_refl β) (le_refl β) (le_refl β)
  have hval : renegarCost ⟨β, β, β⟩ = β * (β + 1) ^ β := by simp [renegarCost]
  rw [hval] at hle
  have hβ1 : 1 ≤ β := by omega
  have hmono : (β + 1) ^ β ≤ β * (β + 1) ^ β := by
    calc (β + 1) ^ β = 1 * (β + 1) ^ β := (Nat.one_mul _).symm
      _ ≤ β * (β + 1) ^ β := Nat.mul_le_mul hβ1 (le_refl _)
  have h2 : (β + 1) ^ β ≤ C0 * (β + 1) ^ k0 := le_trans hmono hle
  have h5 : (β + 1) ^ (k0 + 1) ≤ (β + 1) ^ β :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : C0 * (β + 1) ^ k0 < (β + 1) ^ (k0 + 1) := by
    rw [pow_succ]
    calc C0 * (β + 1) ^ k0 < (β + 1) * (β + 1) ^ k0 :=
          Nat.mul_lt_mul_of_pos_right (by omega : C0 < β + 1)
            (pow_pos (by omega : 0 < β + 1) k0)
      _ = (β + 1) ^ k0 * (β + 1) := by ring
  exact absurd (lt_of_lt_of_le h6 h5) (Nat.not_lt.mpr h2)

/-! ### The repaired specification: a fixed degree bound -/

/-- **The repaired specification.**  Identical to `ChartSpec` except that the
polynomial bound `renegar_le` is required only up to a *fixed* degree bound
`degBound`, independent of the bit length `β`.

This is what the algorithm actually satisfies: the charts produced at order `q`
have degree at most the input degree, while their variable and constraint counts
grow with `β`.  With `p.deg ≤ degBound` and `p.vars, p.polys ≤ β`,
`renegarCost p ≤ (β+1)^(degBound+1)`, so `renegar_le` is provable. -/
structure ChartSpecFixedDeg where
  /-- the fixed bound on the chart degree (the input degree) -/
  degBound : ℕ
  params : ℕ → ℕ → ChartParams
  beta : ℕ → ℕ → ℕ → ℕ
  chartCount : ℕ → ℕ → ℕ
  totalCost : ℕ → ℕ → ℕ
  beta_def : ∀ q n L, beta q n L = 240 * q * n ^ 5 * L
  beta_le : ∀ q n L, n ≤ L → beta q n L ≤ 240 * q * L ^ 6
  chart_le : ∀ q L, chartCount q L ≤ (q + 1) * L ^ q
  total_le : ∀ q L, totalCost q L ≤ chartCount q L * renegarCost (params q L)
  renegar_le : ∃ C0 k0 : ℕ, 0 < C0 ∧ 0 < k0 ∧
    ∀ (p : ChartParams) (β : ℕ), p.vars ≤ β → p.polys ≤ β → p.deg ≤ degBound →
      renegarCost p ≤ C0 * (β + 1) ^ k0
  params_vars_le : ∀ q L, (params q L).vars ≤ beta q L L
  params_polys_le : ∀ q L, (params q L).polys ≤ beta q L L
  params_deg_le : ∀ q L, (params q L).deg ≤ beta q L L
  /-- the chart degree is bounded by the fixed `degBound` -/
  params_deg_le_bound : ∀ q L, (params q L).deg ≤ degBound

/-- **Theorem 1 under the repaired spec, explicit witnesses.**  Same statement
and same witnesses (`C = C0 * 241^k0`, `d = 8*k0 + 1`) as
`theorem1_bound_params`; the only difference is that the degree hypothesis of
`hcost` is `p.deg ≤ R.degBound`. -/
theorem theorem1_bound_params_fixedDeg (R : ChartSpecFixedDeg) {q L C0 k0 : ℕ}
    (hq : 1 ≤ q) (hL : 2 ≤ L) (hqn : q ≤ L)
    (hcost : ∀ (p : ChartParams) (β : ℕ), p.vars ≤ β → p.polys ≤ β →
      p.deg ≤ R.degBound → renegarCost p ≤ C0 * (β + 1) ^ k0) :
    R.totalCost q L ≤ C0 * 241 ^ k0 * (L + 1) ^ ((8 * k0 + 1) * (q + 1) ^ 2) :=
  chart_cost_bound (q := q) (L := L) (C0 := C0) (k0 := k0)
    (β := R.beta q L L) (cc := R.chartCount q L) (tc := R.totalCost q L)
    (p := R.params q L) hq hL hqn (R.chart_le q L) (R.total_le q L)
    (hcost (R.params q L) (R.beta q L L) (R.params_vars_le q L)
      (R.params_polys_le q L) (R.params_deg_le_bound q L))
    (R.beta_le q L L (le_refl L))

/-- **Theorem 1, conditional on the repaired (satisfiable) specification.**
Witnesses `C = C0 * 241^k0`, `d = 8*k0 + 1`. -/
theorem theorem1_conditional_params_fixedDeg (R : ChartSpecFixedDeg) {q n L : ℕ}
    (hq : 1 ≤ q) (hL : 2 ≤ L) (hqn : q ≤ L) (hn : n ≤ L) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ R.totalCost q L ≤ C * (L + 1) ^ (d * (q + 1) ^ 2) := by
  obtain ⟨C0, k0, hC0, hk0, hcost⟩ := R.renegar_le
  exact ⟨C0 * 241 ^ k0, 8 * k0 + 1,
    Nat.mul_pos hC0 (pow_pos (by norm_num : (0 : ℕ) < 241) k0),
    by omega,
    theorem1_bound_params_fixedDeg R hq hL hqn hcost⟩

/-! ### Non-vacuity: a concrete inhabitant of the repaired specification -/

/-- The coefficient bit length of the paper: `240 q n^5 L`. -/
def stdBeta (q n L : ℕ) : ℕ := 240 * q * n ^ 5 * L

/-- `240 q L^5 * L = 240 q L^6`. -/
private theorem stdBeta_self (q L : ℕ) : 240 * q * L ^ 5 * L = 240 * q * L ^ 6 := by
  ring

/-- A concrete `ChartSpecFixedDeg`:
* `degBound = 0` (every chart has degree `0`);
* the chart at `(q, L)` has `vars = beta q L L = 240 q L^6`, `polys = 0`,
  `deg = 0`, so its Renegar cost is exactly `beta q L L`;
* `chartCount q L = (q+1) * L^q`, `totalCost q L = chartCount q L * beta q L L`;
* the polynomial bound is `renegarCost p = p.vars ≤ β ≤ β + 1 = 1 * (β+1)^1`,
  i.e. `C0 = 1`, `k0 = 1`.

`chart_le` and `total_le` are `rfl`; `beta_def` is `rfl`; the rest is the
arithmetic above. -/
def chartSpecFixedDegInstance : ChartSpecFixedDeg where
  degBound := 0
  beta := stdBeta
  params := fun q L => ⟨stdBeta q L L, 0, 0⟩
  chartCount := fun q L => (q + 1) * L ^ q
  totalCost := fun q L => (q + 1) * L ^ q * stdBeta q L L
  beta_def := fun q n L => rfl
  beta_le := fun q n L hn => by
    have hn5 : n ^ 5 ≤ L ^ 5 := Nat.pow_le_pow_left hn 5
    have h1 : 240 * q * n ^ 5 ≤ 240 * q * L ^ 5 := Nat.mul_le_mul (le_refl _) hn5
    have h2 : 240 * q * n ^ 5 * L ≤ 240 * q * L ^ 5 * L :=
      Nat.mul_le_mul h1 (le_refl L)
    calc stdBeta q n L = 240 * q * n ^ 5 * L := rfl
      _ ≤ 240 * q * L ^ 5 * L := h2
      _ = 240 * q * L ^ 6 := stdBeta_self q L
  chart_le := fun q L => le_refl _
  total_le := fun q L => by
    -- the Renegar cost of `⟨stdBeta q L L, 0, 0⟩` is `stdBeta q L L`
    show (q + 1) * L ^ q * stdBeta q L L ≤
      (q + 1) * L ^ q * renegarCost ⟨stdBeta q L L, 0, 0⟩
    have h : renegarCost ⟨stdBeta q L L, 0, 0⟩ = stdBeta q L L := by
      simp [renegarCost]
    rw [h]
  renegar_le := ⟨1, 1, by norm_num, by norm_num, fun p β hv hp hd => by
    have h := renegarCost_le_pow (D := 0) hv hp hd
    simpa using h⟩
  params_vars_le := fun q L => le_refl _
  params_polys_le := fun q L => Nat.zero_le _
  params_deg_le := fun q L => Nat.zero_le _
  params_deg_le_bound := fun q L => le_refl 0

/-- **The repaired specification is inhabited**, so
`theorem1_conditional_params_fixedDeg` is not vacuous. -/
theorem chartSpecFixedDeg_inhabited : Nonempty ChartSpecFixedDeg :=
  ⟨chartSpecFixedDegInstance⟩

/-- The inhabitant's charts really cost something: at `q = 1`, `L = 2` the
chart's Renegar cost is `240 * 1 * 2^6 = 15360 ≠ 0`.  (So the inhabitant is not
the degenerate `totalCost = 0` instance.) -/
theorem chartSpecFixedDegInstance_cost_pos :
    0 < renegarCost (chartSpecFixedDegInstance.params 1 2) := by
  norm_num [chartSpecFixedDegInstance, stdBeta, renegarCost]

/-- `theorem1_conditional_params_fixedDeg` instantiated on
`chartSpecFixedDegInstance`: the explicit witnesses are `C = 241 = 1 * 241^1`
and `d = 9 = 8*1 + 1`. -/
theorem theorem1_conditional_params_instance {q n L : ℕ}
    (hq : 1 ≤ q) (hL : 2 ≤ L) (hqn : q ≤ L) (hn : n ≤ L) :
    chartSpecFixedDegInstance.totalCost q L ≤ 241 * (L + 1) ^ (9 * (q + 1) ^ 2) := by
  have h := theorem1_bound_params_fixedDeg (R := chartSpecFixedDegInstance)
    (C0 := 1) (k0 := 1) hq hL hqn ?_
  · calc chartSpecFixedDegInstance.totalCost q L
        ≤ 1 * 241 ^ 1 * (L + 1) ^ ((8 * 1 + 1) * (q + 1) ^ 2) := h
      _ = 241 * (L + 1) ^ (9 * (q + 1) ^ 2) := by norm_num
  · intro p β hv hp hd
    have h2 := renegarCost_le_pow (D := 0) hv hp hd
    simpa using h2

/-! ### Axiom audit -/


end Q1Paper
