/-
Q1Paper/PaperI/FptSpec.lean

**The FPT analogue of `PaperI/RenegarParams.lean`, with the fixed-degree lesson applied.**

`PaperI/FptCore.lean` proves the Renegar-free FPT core: the dimension bookkeeping
(`FptDimensions`), the Grassmannian chart count `2 ^ m'` (= `∑ t, choose m' t`),
and `2 ^ m' ≤ 4 ^ ℓ` from `m' ≤ 2ℓ`.  `PaperI/RenegarParams.lean` supplies the
single-order specification `ChartSpecFixedDeg`, whose `degBound` field is what
makes it non-empty (the version without a fixed degree, `ChartSpec`, was *proved*
unsatisfiable: `chartSpec_empty`).  This file assembles the FPT analogue.

Design decisions (each is forced by provability, and each is documented again
where it occurs):

* §1 `RenegarBackend` keeps correctness and cost apart: the only content is a
  polynomial cost bound
  `Cost vars polys deg β ≤ C0 * (β+1)^k0 * (polys (deg+1) + 1)^(k0 (vars+1))`,
  valid at **fixed degree** (`deg ≤ 2`, the charts are linear/quadratic in `Y`).
  Without `deg ≤ 2` the bound is false (`PaperI/RenegarParams.lean`'s
  `chartSpec_empty` counterexample), so the hypothesis is kept.  A backend is
  exhibited (`fptBackendInhabited`).

* §2 `FptChartSpec`: the chart count is **not a field**.  It is the definition
  `fptChartCount dims = 2 ^ dims.m'`, and `2 ^ m' ≤ 4 ^ ℓ` is *proved* from the
  field `dims.m'_le_two_ell` (`fptChartCount_le_four_pow`), so no specification
  can choose its own chart count.  `total_le` then bounds the total cost by
  `chartCount × per-chart Renegar cost`.

* The one thing the request's §2 field list does not yet contain — and which is
  *necessary* for §3 to be provable at all — is a bound on the chart's own
  `vars` and `polys`.  `Cost vars polys deg β` has the exponent `k0 * (vars + 1)`
  and the base `polys * (deg + 1) + 1`; with `vars` and `polys` completely free
  no bound `C (ℓ+2)^(C(ℓ+1)^2) (β+1)^d` can hold (take `β` arbitrary and `vars`
  growing with `ℓ`; the `(β+1)^(k0*(vars+1))` factor then beats any fixed power
  of `β+1`).  This is exactly the FPT content: the chart's semialgebraic system
  must have size bounded by a function of the **parameter** `ℓ` alone, not by
  `n, k, d0`, otherwise the exponent would depend on the input.  So the spec
  carries

      params_vars_le    : (params 0 0).vars  ≤ (dims.ell + 1) ^ 2
      params_polys_le   : (params 0 0).polys ≤ (dims.ell + 1) ^ 2
      params_deg_le_two : (params 0 0).deg   ≤ 2

  (`ℓ²` is the dimension of a chart of the Grassmannian `Gr(t, m')` with
  `t, m' ≤ 2ℓ`; the number of chart constraints is of the same order.)

* §3 `theorem2_fpt_conditional`, with the **explicit** witnesses

      C = 8 * k0 + C0 + 2,      d = k0

  where `C0, k0` come from `R.renegar.cost_bound`.  The hypotheses
  `1 ≤ R.dims.ell` and `1 ≤ R.beta` are part of the requested statement but are
  **not used** by the proof; `theorem2_fpt_conditional_unconditional` drops them.

* §4 Non-vacuity: `fptChartSpecInstance`, `fptChartSpec_inhabited`, and
  `fptChartSpecInstance_cost_pos` (`totalCost = 4 ≠ 0`).  `FptDimensions`,
  `RenegarBackend` and `FptChartSpec` all get inhabitants.

No `sorry`, no `admit`, no new axioms.  Check with
`lake env lean Q1Paper/PaperI/FptSpec.lean`.
-/

import Q1Paper.PaperI.FptCore
import Q1Paper.PaperI.RenegarParams

namespace Q1Paper

/-! ## §1  The Renegar backend: correctness and cost kept separate -/

/-- A real-algebraic feasibility oracle: **correctness and bit complexity are
separate fields, and neither implies the other.**

`Cost vars polys deg β` is the bit cost of deciding a chart with `vars`
variables, `polys` polynomial constraints of degree `deg` and coefficient bit
length `β`.  The field `cost_bound` is *only* a polynomial upper bound on that
cost, at **fixed degree** (`deg ≤ 2`: the charts are linear/quadratic in `Y`).

Keeping `deg ≤ 2` is essential: with the degree free, `Cost β β β β` may be
`β * (β+1)^β`, which no fixed polynomial in `β+1` dominates — that is exactly
`PaperI/RenegarParams.lean`'s `chartSpec_empty` counterexample, one level up.

Nothing here says the oracle is *correct* (no `Correct`/`Decide` field): a
backend is a cost model only, so no correctness statement about the algorithm is
claimed or needed — the separation of correctness from cost is literally that
this structure carries cost and the consumers carry the semantic content. -/
structure RenegarBackend where
  /-- bit cost of one chart: `(vars, polys, deg, beta) ↦ cost` -/
  Cost : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- polynomial cost bound, uniform in the parameters, at fixed degree `≤ 2` -/
  cost_bound : ∃ C0 k0 : ℕ, 0 < C0 ∧ 0 < k0 ∧
    ∀ (vars polys deg β : ℕ), deg ≤ 2 →
      Cost vars polys deg β ≤
        C0 * (β + 1) ^ k0 * (polys * (deg + 1) + 1) ^ (k0 * (vars + 1))

/-- The polynomial in `β` that bounds a constant cost: `1 ≤ (β+1)^1 * P^(vars+1)`
for every `P ≥ 1`.  Used to discharge `RenegarBackend.cost_bound` for the
constant backend. -/
private theorem one_le_constCost (vars polys deg β : ℕ) :
    (1 : ℕ) ≤ 1 * (β + 1) ^ 1 * (polys * (deg + 1) + 1) ^ (1 * (vars + 1)) := by
  have hβ : 1 ≤ (β + 1) ^ 1 := pow_pos (show 0 < β + 1 by omega) 1
  have hP : 1 ≤ (polys * (deg + 1) + 1) ^ (1 * (vars + 1)) :=
    pow_pos (show 0 < polys * (deg + 1) + 1 by omega) (1 * (vars + 1))
  calc (1 : ℕ) = 1 * 1 := (Nat.mul_one 1).symm
    _ ≤ (β + 1) ^ 1 * (polys * (deg + 1) + 1) ^ (1 * (vars + 1)) := Nat.mul_le_mul hβ hP
    _ = 1 * (β + 1) ^ 1 * (polys * (deg + 1) + 1) ^ (1 * (vars + 1)) := by ring

/-- The constant backend: every chart costs one bit.  Its `cost_bound` holds
with `C0 = k0 = 1`.  (A cost model, not an algorithm.) -/
def constRenegarBackend : RenegarBackend where
  Cost := fun _ _ _ _ => 1
  cost_bound := ⟨1, 1, by norm_num, by norm_num, fun vars polys deg β _ =>
    one_le_constCost vars polys deg β⟩

/-- **`RenegarBackend` is inhabited** — the cost-bound field is satisfiable, so
§1 is not a vacuous interface. -/
theorem fptBackendInhabited : Nonempty RenegarBackend :=
  ⟨constRenegarBackend⟩

/-- The per-chart cost at the constant backend, at any parameters with `deg ≤ 2`:
`Cost = 1` is bounded by the required polynomial.  (The `deg ≤ 2` argument is
unused, as it must be for a constant cost.) -/
theorem constRenegarBackend_cost_le (vars polys deg β : ℕ) (_hd : deg ≤ 2) :
    constRenegarBackend.Cost vars polys deg β ≤
      1 * (β + 1) ^ 1 * (polys * (deg + 1) + 1) ^ (1 * (vars + 1)) :=
  one_le_constCost vars polys deg β

/-! ## §2  The FPT chart specification: the chart count comes from `FptCore` -/

/-- **The number of Grassmannian charts: `2 ^ m'`.**

This is a *definition*, not a structure field: the chart count is forced by the
dimension `m'` and cannot be chosen by an implementation.  The equality with the
`t`-subset count `∑ t, choose m' t` is `fptChartCount_eq_sum_choose` (from
`FptCore.sum_choose_eq_two_pow`), and the bound `≤ 4 ^ ℓ` is
`fptChartCount_le_four_pow` (from `FptCore.chart_count_le_four_pow`). -/
def fptChartCount (D : FptDimensions) : ℕ := 2 ^ D.m'

/-- The chart count is the Grassmannian count: `2 ^ m' = ∑_{t} (m' choose t)`. -/
theorem fptChartCount_eq_sum_choose (D : FptDimensions) :
    fptChartCount D = ∑ t ∈ Finset.range (D.m' + 1), Nat.choose D.m' t := by
  rw [fptChartCount, sum_choose_eq_two_pow]

/-- **`2 ^ m' ≤ 4 ^ ℓ`, proved from `m' ≤ 2ℓ`** (the field `D.m'_le_two_ell`),
via `4 ^ ℓ = (2 ^ 2) ^ ℓ = 2 ^ (2ℓ)`. -/
theorem fptChartCount_le_four_pow (D : FptDimensions) : fptChartCount D ≤ 4 ^ D.ell := by
  rw [fptChartCount]
  calc 2 ^ D.m' ≤ 2 ^ (2 * D.ell) := Nat.pow_le_pow_right (by norm_num) D.m'_le_two_ell
    _ = 4 ^ D.ell := by
        rw [pow_mul]
        norm_num

/-- The specification of the FPT theorem.

* `dims` carries the dimension relations (proved elsewhere: rank–nullity);
* `renegar` is the backend of §1;
* `params q L` are the chart parameters at order `q` and bit length `L`; only
  `params 0 0` enters the cost, as in the request;
* `beta` is the coefficient bit length of the chart;
* the chart count is **not** a field (see `fptChartCount`);
* `total_le` bounds the total cost by `chartCount × per-chart Renegar cost`;
* `params_vars_le`, `params_polys_le`, `params_deg_le_two` are the FPT content:
  the chart's system has size bounded by a function of the parameter `ℓ` alone,
  and degree `≤ 2`.  Without them §3 is false (with `vars` free, `Cost` has the
  exponent `k0 * (vars+1)`); see the file header.

Note that no field here mentions the *correctness* of the oracle: the spec is a
cost specification, so `theorem2_fpt_conditional` is a statement about cost
only. -/
structure FptChartSpec where
  /-- the dimension symbols and their relations -/
  dims : FptDimensions
  /-- the Renegar cost model -/
  renegar : RenegarBackend
  /-- the parameters of the chart at (order, bit length) -/
  params : ℕ → ℕ → ChartParams
  /-- the coefficient bit length -/
  beta : ℕ
  /-- the total cost of the algorithm -/
  totalCost : ℕ
  /-- the chart is linear/quadratic in `Y` -/
  params_deg_le_two : (params 0 0).deg ≤ 2
  /-- the chart's variable count is bounded by `(ℓ+1)^2` (FPT content) -/
  params_vars_le : (params 0 0).vars ≤ (dims.ell + 1) ^ 2
  /-- the chart's constraint count is bounded by `(ℓ+1)^2` (FPT content) -/
  params_polys_le : (params 0 0).polys ≤ (dims.ell + 1) ^ 2
  /-- **the total cost is at most `chartCount × per-chart cost`**, where
  `chartCount = 2 ^ m'` is the Grassmannian count -/
  total_le : totalCost ≤ fptChartCount dims *
    renegar.Cost (params 0 0).vars (params 0 0).polys (params 0 0).deg beta

/-- The chart count of a spec is `2 ^ m'` (definitional), and it is `≤ 4 ^ ℓ`. -/
theorem fptChartSpec_chartCount_le (R : FptChartSpec) : 2 ^ R.dims.m' ≤ 4 ^ R.dims.ell :=
  fptChartCount_le_four_pow R.dims

/-! ## §2′  Pure arithmetic for the exponent bookkeeping -/

/-- `1 ≤ (ℓ+1)^2`. -/
private theorem one_le_sq_succ (ell : ℕ) : 1 ≤ (ell + 1) ^ 2 := by
  have key : (ell + 1) ^ 2 = 1 + (ell ^ 2 + 2 * ell) := by ring
  rw [key]
  omega

/-- `ℓ ≤ (ℓ+1)^2`. -/
private theorem le_sq_succ (ell : ℕ) : ell ≤ (ell + 1) ^ 2 := by
  have key : (ell + 1) ^ 2 = ell + (ell ^ 2 + ell + 1) := by ring
  rw [key]
  omega

/-- `3(ℓ+1)^2 + 1 ≤ (ℓ+2)^3`.  Proved by exhibiting the difference as a sum of
nonnegative monomials (so `omega` finishes):
`(ℓ+2)^3 = 3(ℓ+1)^2 + 1 + (ℓ^3 + 3ℓ^2 + 6ℓ + 4)`. -/
private theorem three_sq_add_one_le_cube (ell : ℕ) : 3 * (ell + 1) ^ 2 + 1 ≤ (ell + 2) ^ 3 := by
  have key : (ell + 2) ^ 3 = 3 * (ell + 1) ^ 2 + 1 + (ell ^ 3 + 3 * ell ^ 2 + 6 * ell + 4) := by
    ring
  rw [key]
  omega

/-- **The chart's polynomial count is controlled by `ℓ`**: `polys ≤ (ℓ+1)^2` and
`deg ≤ 2` give `polys * (deg + 1) + 1 ≤ (ℓ+2)^3`. -/
private theorem fpt_poly_count_le (ell polys deg : ℕ)
    (hp : polys ≤ (ell + 1) ^ 2) (hd : deg ≤ 2) :
    polys * (deg + 1) + 1 ≤ (ell + 2) ^ 3 := by
  have hd1 : deg + 1 ≤ 3 := by omega
  have hmul : polys * (deg + 1) ≤ (ell + 1) ^ 2 * 3 := Nat.mul_le_mul hp hd1
  calc polys * (deg + 1) + 1 ≤ (ell + 1) ^ 2 * 3 + 1 := Nat.add_le_add_right hmul 1
    _ = 3 * (ell + 1) ^ 2 + 1 := by ring
    _ ≤ (ell + 2) ^ 3 := three_sq_add_one_le_cube ell

/-- **The exponent of the per-chart cost is controlled by `ℓ`**:
`k0 * (vars + 1) ≤ 2k0(ℓ+1)^2` when `vars ≤ (ℓ+1)^2`. -/
private theorem fpt_vars_exp_le (ell vars k0 : ℕ) (hv : vars ≤ (ell + 1) ^ 2) :
    k0 * (vars + 1) ≤ 2 * k0 * (ell + 1) ^ 2 := by
  have h1 : vars + 1 ≤ 2 * (ell + 1) ^ 2 := by
    have h2 := one_le_sq_succ ell
    omega
  calc k0 * (vars + 1) ≤ k0 * (2 * (ell + 1) ^ 2) := Nat.mul_le_mul_left k0 h1
    _ = 2 * k0 * (ell + 1) ^ 2 := by ring

/-- **The per-chart cost is bounded by `(ℓ+2)^(6 k0 (ℓ+1)^2)`** at fixed degree,
using `fpt_poly_count_le` for the base and `fpt_vars_exp_le` for the exponent. -/
private theorem fpt_cost_le_pow (ell polys deg vars k0 : ℕ)
    (hp : polys ≤ (ell + 1) ^ 2) (hd : deg ≤ 2) (hv : vars ≤ (ell + 1) ^ 2) :
    (polys * (deg + 1) + 1) ^ (k0 * (vars + 1)) ≤ (ell + 2) ^ (6 * k0 * (ell + 1) ^ 2) := by
  have hP : polys * (deg + 1) + 1 ≤ (ell + 2) ^ 3 := fpt_poly_count_le ell polys deg hp hd
  have hE : k0 * (vars + 1) ≤ 2 * k0 * (ell + 1) ^ 2 := fpt_vars_exp_le ell vars k0 hv
  calc (polys * (deg + 1) + 1) ^ (k0 * (vars + 1))
      ≤ ((ell + 2) ^ 3) ^ (k0 * (vars + 1)) := Nat.pow_le_pow_left hP _
    _ = (ell + 2) ^ (3 * (k0 * (vars + 1))) := by rw [← pow_mul]
    _ ≤ (ell + 2) ^ (3 * (2 * k0 * (ell + 1) ^ 2)) :=
        Nat.pow_le_pow_right (show 1 ≤ ell + 2 by omega) (Nat.mul_le_mul_left 3 hE)
    _ = (ell + 2) ^ (6 * k0 * (ell + 1) ^ 2) := by
        congr 1
        ring

/-- **The chart count is bounded by `(ℓ+2)^(2(ℓ+1)^2)`.**
`2 ^ m' ≤ 4 ^ ℓ = 2 ^ (2ℓ) ≤ (ℓ+2)^(2ℓ) ≤ (ℓ+2)^(2(ℓ+1)^2)`. -/
private theorem fpt_chart_count_le_pow (ell m' : ℕ) (hm : m' ≤ 2 * ell) :
    2 ^ m' ≤ (ell + 2) ^ (2 * (ell + 1) ^ 2) := by
  have h4 : 2 ^ m' ≤ 4 ^ ell := by
    calc 2 ^ m' ≤ 2 ^ (2 * ell) := Nat.pow_le_pow_right (by norm_num) hm
      _ = 4 ^ ell := by
          rw [pow_mul]
          norm_num
  have h5 : 4 ^ ell ≤ (ell + 2) ^ (2 * ell) := by
    have h4le : (4 : ℕ) ≤ (ell + 2) ^ 2 := by
      have h2 : (2 : ℕ) ≤ ell + 2 := by omega
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ (ell + 2) ^ 2 := Nat.pow_le_pow_left h2 2
    calc 4 ^ ell ≤ ((ell + 2) ^ 2) ^ ell := Nat.pow_le_pow_left h4le ell
      _ = (ell + 2) ^ (2 * ell) := by rw [pow_mul]
  have h6 : (ell + 2) ^ (2 * ell) ≤ (ell + 2) ^ (2 * (ell + 1) ^ 2) := by
    refine Nat.pow_le_pow_right (by omega) ?_
    have h := le_sq_succ ell
    omega
  exact le_trans h4 (le_trans h5 h6)

/-! ## §3  The conditional FPT theorem -/

/-- **The FPT cost bound with explicit witnesses.**

For a spec `R` and *any* admissible pair `(C0, k0)` for its backend, the total
cost is at most

  `(8 k0 + C0 + 2) * (ℓ+2)^((8 k0 + C0 + 2) * (ℓ+1)^2) * (β+1)^k0`.

Route: `totalCost ≤ 2^m' * Cost` (`R.total_le`); `2^m' ≤ (ℓ+2)^(2(ℓ+1)^2)`
(`fpt_chart_count_le_pow`); `Cost ≤ C0 (β+1)^k0 (ℓ+2)^(6 k0 (ℓ+1)^2)`
(`fpt_cost_le_pow`); the exponents add to `(6k0+2)(ℓ+1)^2`, which is
`≤ (8k0+C0+2)(ℓ+1)^2`, and `C0 ≤ 8k0+C0+2` absorbs the constant. -/
theorem theorem2_fpt_bound (R : FptChartSpec) {C0 k0 : ℕ} (hC0 : 0 < C0) (hk0 : 0 < k0)
    (hcost : ∀ (vars polys deg β : ℕ), deg ≤ 2 →
      R.renegar.Cost vars polys deg β ≤
        C0 * (β + 1) ^ k0 * (polys * (deg + 1) + 1) ^ (k0 * (vars + 1))) :
    R.totalCost ≤ (8 * k0 + C0 + 2) *
      (R.dims.ell + 2) ^ ((8 * k0 + C0 + 2) * (R.dims.ell + 1) ^ 2) *
      (R.beta + 1) ^ k0 := by
  have hc := hcost (R.params 0 0).vars (R.params 0 0).polys (R.params 0 0).deg R.beta
    R.params_deg_le_two
  have hmain : R.totalCost ≤ 2 ^ R.dims.m' * (C0 * (R.beta + 1) ^ k0 *
      ((R.params 0 0).polys * ((R.params 0 0).deg + 1) + 1) ^
        (k0 * ((R.params 0 0).vars + 1))) :=
    le_trans R.total_le (Nat.mul_le_mul_left _ hc)
  have hA : 2 ^ R.dims.m' ≤ (R.dims.ell + 2) ^ (2 * (R.dims.ell + 1) ^ 2) :=
    fpt_chart_count_le_pow R.dims.ell R.dims.m' R.dims.m'_le_two_ell
  have hB : ((R.params 0 0).polys * ((R.params 0 0).deg + 1) + 1) ^
        (k0 * ((R.params 0 0).vars + 1)) ≤
      (R.dims.ell + 2) ^ (6 * k0 * (R.dims.ell + 1) ^ 2) :=
    fpt_cost_le_pow R.dims.ell (R.params 0 0).polys (R.params 0 0).deg
      (R.params 0 0).vars k0 R.params_polys_le R.params_deg_le_two R.params_vars_le
  calc R.totalCost
      ≤ 2 ^ R.dims.m' * (C0 * (R.beta + 1) ^ k0 *
          ((R.params 0 0).polys * ((R.params 0 0).deg + 1) + 1) ^
            (k0 * ((R.params 0 0).vars + 1))) := hmain
    _ ≤ (R.dims.ell + 2) ^ (2 * (R.dims.ell + 1) ^ 2) *
          (C0 * (R.beta + 1) ^ k0 * (R.dims.ell + 2) ^ (6 * k0 * (R.dims.ell + 1) ^ 2)) :=
        Nat.mul_le_mul hA (Nat.mul_le_mul_left _ hB)
    _ = C0 * (R.beta + 1) ^ k0 *
          ((R.dims.ell + 2) ^ (2 * (R.dims.ell + 1) ^ 2) *
           (R.dims.ell + 2) ^ (6 * k0 * (R.dims.ell + 1) ^ 2)) := by ring
    _ = C0 * (R.beta + 1) ^ k0 *
          (R.dims.ell + 2) ^ ((6 * k0 + 2) * (R.dims.ell + 1) ^ 2) := by
        rw [← pow_add]
        congr 1
        ring
    _ ≤ (8 * k0 + C0 + 2) * (R.dims.ell + 2) ^
          ((8 * k0 + C0 + 2) * (R.dims.ell + 1) ^ 2) * (R.beta + 1) ^ k0 := by
        have h1 : C0 ≤ 8 * k0 + C0 + 2 := by omega
        have h2 : (6 * k0 + 2) * (R.dims.ell + 1) ^ 2 ≤
            (8 * k0 + C0 + 2) * (R.dims.ell + 1) ^ 2 :=
          Nat.mul_le_mul_right _ (by omega)
        have h3 : (R.dims.ell + 2) ^ ((6 * k0 + 2) * (R.dims.ell + 1) ^ 2) ≤
            (R.dims.ell + 2) ^ ((8 * k0 + C0 + 2) * (R.dims.ell + 1) ^ 2) :=
          Nat.pow_le_pow_right (by omega) h2
        calc C0 * (R.beta + 1) ^ k0 *
              (R.dims.ell + 2) ^ ((6 * k0 + 2) * (R.dims.ell + 1) ^ 2)
            ≤ (8 * k0 + C0 + 2) * (R.beta + 1) ^ k0 *
                (R.dims.ell + 2) ^ ((8 * k0 + C0 + 2) * (R.dims.ell + 1) ^ 2) :=
              Nat.mul_le_mul (Nat.mul_le_mul_right ((R.beta + 1) ^ k0) h1) h3
          _ = (8 * k0 + C0 + 2) * (R.dims.ell + 2) ^
                ((8 * k0 + C0 + 2) * (R.dims.ell + 1) ^ 2) * (R.beta + 1) ^ k0 := by ring

/-- **Theorem 2 (FPT), existential form, with no side hypotheses.**

`∃ C d, 0 < C ∧ 0 < d ∧ totalCost ≤ C * (ℓ+2)^(C(ℓ+1)^2) * (β+1)^d`,
with the explicit witnesses `C = 8 * k0 + C0 + 2` and `d = k0`, where `C0, k0`
come from `R.renegar.cost_bound`. -/
theorem theorem2_fpt_exists (R : FptChartSpec) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      R.totalCost ≤ C * (R.dims.ell + 2) ^ (C * (R.dims.ell + 1) ^ 2) * (R.beta + 1) ^ d := by
  obtain ⟨C0, k0, hC0, hk0, hcost⟩ := R.renegar.cost_bound
  exact ⟨8 * k0 + C0 + 2, k0, by omega, hk0, theorem2_fpt_bound R hC0 hk0 hcost⟩

/-- **Theorem 2 (FPT), conditional on `FptChartSpec`** (the requested statement).

Witnesses: `C = 8 * k0 + C0 + 2`, `d = k0`.

The hypotheses `1 ≤ ℓ` and `1 ≤ β` are part of the requested statement; the
proof does **not** use them — see `theorem2_fpt_conditional_unconditional`. -/
theorem theorem2_fpt_conditional (R : FptChartSpec) (hℓ : 1 ≤ R.dims.ell) (hβ : R.beta ≥ 1) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      R.totalCost ≤ C * (R.dims.ell + 2) ^ (C * (R.dims.ell + 1) ^ 2) * (R.beta + 1) ^ d :=
  theorem2_fpt_exists R

/-- The same conclusion **without** the two hypotheses `1 ≤ ℓ`, `1 ≤ β` (the
honesty note for §3: the bound is uniform in them, so they are not needed). -/
theorem theorem2_fpt_conditional_unconditional (R : FptChartSpec) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      R.totalCost ≤ C * (R.dims.ell + 2) ^ (C * (R.dims.ell + 1) ^ 2) * (R.beta + 1) ^ d :=
  theorem2_fpt_exists R

/-! ## §4  Non-vacuity -/

/-- A concrete `FptDimensions`: `k = d0 = ℓ = ω = 1`, `t = m' = 2`.  All six
relations hold. -/
def fptDimsInstance : FptDimensions :=
  ⟨0, 0, 1, 1, 1, 1, 2, 2, le_rfl, le_rfl, le_rfl, by norm_num, by norm_num,
    by norm_num⟩

/-- A concrete `FptChartSpec`:
* `dims` is `fptDimsInstance` (`ℓ = 1`, `m' = 2`, so the chart count is `2^2 = 4`);
* the backend is the constant one (cost `1` per chart), so the per-chart budget
  available to `totalCost` is `4 * 1 = 4`;
* `params = (0, 0, 0)` (degree `0`, so `deg ≤ 2`; `vars, polys = 0 ≤ 4 = (ℓ+1)^2`);
* `beta = 1`, `totalCost = 2 ^ m' = 4`.

`totalCost` is nonzero (`fptChartSpecInstance_cost_pos`), so the inhabitant is
not the degenerate `totalCost = 0` instance. -/
def fptChartSpecInstance : FptChartSpec where
  dims := fptDimsInstance
  renegar := constRenegarBackend
  params := fun _ _ => ⟨0, 0, 0⟩
  beta := 1
  totalCost := 2 ^ fptDimsInstance.m'
  params_deg_le_two := by norm_num
  params_vars_le := by norm_num [fptDimsInstance]
  params_polys_le := by norm_num [fptDimsInstance]
  total_le := by norm_num [fptChartCount, fptDimsInstance, constRenegarBackend]

/-- **`FptChartSpec` is inhabited**: §2 (and hence §3) is not vacuous. -/
theorem fptChartSpec_inhabited : Nonempty FptChartSpec :=
  ⟨fptChartSpecInstance⟩

/-- The inhabitant's total cost is `2 ^ 2 = 4 > 0`, so it is not the
degenerate `totalCost = 0` specification. -/
theorem fptChartSpecInstance_cost_pos : 0 < fptChartSpecInstance.totalCost := by
  norm_num [fptChartSpecInstance, fptDimsInstance]

/-- **§3 is not vacuous**: instantiated at the inhabitant, the conclusion holds
(with `C = 11 = 8*1+1+2`, `d = 1` given by `theorem2_fpt_exists`). -/
theorem theorem2_fpt_conditional_instance :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      fptChartSpecInstance.totalCost ≤
        C * (fptDimsInstance.ell + 2) ^ (C * (fptDimsInstance.ell + 1) ^ 2) *
          (fptChartSpecInstance.beta + 1) ^ d :=
  theorem2_fpt_conditional fptChartSpecInstance
    (by norm_num [fptChartSpecInstance, fptDimsInstance])
    (by norm_num [fptChartSpecInstance])

/-! ## Axiom audit -/


end Q1Paper
