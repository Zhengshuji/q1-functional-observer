
import Mathlib

/-!
Q1Paper/PaperI/S06_Algorithms/FptCore.lean

The Renegar-free core of the FPT theorem (Paper I).

Two blocks, both unconditional: no Renegar backend, no bit lengths.

§1  Dimension relations among the paper's symbols `n p k d0 ell omega t m'`.
    The relations `ell ≤ k`, `k ≤ d0`, `ω ≤ ell`, `t ≤ 2ℓ`, `m' ≤ 2ℓ` are
    proved elsewhere (they are consequences of the rank–nullity count for the
    observer pencil); here they are carried as *named fields* of
    `FptDimensions`, and the derived arithmetic is proved.

§2  The Grassmannian chart count.  For fixed `m'` the number of `t`-subsets of
    a set with `m'` elements is `Nat.choose m' t`; summing over `t` gives
    `2 ^ m'`, and `m' ≤ 2ℓ` turns this into `≤ 4 ^ ℓ`.

Naming note.  The paper writes ℓ and ω; Lean identifiers here are ASCII, so the
fields are `ell` and `omega`: `D.ell` is ℓ, `D.omega` is ω.

Syntax note.  In this toolchain (`leanprover/lean4:v4.35.0`) a structure field
binder must carry a single identifier, so the eight symbols are introduced one
per line (a shared `n p k ... : ℕ` line is rejected with
"Failed to infer type of binder").  The fields, their types and their order are
exactly those of the paper's list.
-/


namespace Q1Paper

/-! ## §1 Dimension relations -/

/-- The paper's dimension symbols together with the relations that are proved
elsewhere (rank–nullity for the observer pencil).  These are *fields*, not
theorems: nothing in this file proves them.

`d0_le_kappa` records the variant form `κ_obs = r * d0` with `r ≥ 1`, i.e.
`d0 ≤ k * d0` (inhabited only when `1 ≤ k`, as in the paper). -/
structure FptDimensions where
  n : ℕ
  p : ℕ
  k : ℕ
  d0 : ℕ
  ell : ℕ
  omega : ℕ
  t : ℕ
  m' : ℕ
  ell_le_k : ell ≤ k
  k_le_d0 : k ≤ d0
  omega_le_ell : omega ≤ ell
  t_le_two_ell : t ≤ 2 * ell
  m'_le_two_ell : m' ≤ 2 * ell
  d0_le_kappa : d0 ≤ k * d0

/-- Non-vacuity: a concrete inhabitant (`k = d0 = ℓ = ω = 1`, `t = m' = 2`).
The six relations hold simultaneously, so the structure is not an
inconsistent set of fields. -/
example : FptDimensions :=
  ⟨0, 0, 1, 1, 1, 1, 2, 2, le_rfl, le_rfl, le_rfl, by norm_num, by norm_num,
    by norm_num⟩

/-- `ω ≤ 2ℓ`: from `ω ≤ ℓ` and `ℓ ≤ 2ℓ`.  No side condition. -/
theorem fpt_omega_le_two_ell (D : FptDimensions) : D.omega ≤ 2 * D.ell := by
  have h := D.omega_le_ell
  omega

/-- `m' ≤ 2ℓ`: this *is* the field `m'_le_two_ell`. -/
theorem fpt_m'_le_two_ell (D : FptDimensions) : D.m' ≤ 2 * D.ell :=
  D.m'_le_two_ell

/-- `ℓ ≤ κ_obs = k * d0`, from `ℓ ≤ k` and `1 ≤ d0`.  The hypothesis `1 ≤ d0`
is honest: without it (`d0 = 0`) the statement reads `ℓ ≤ 0`.  (It is however
redundant *given the field* `d0_le_kappa`; see
`fpt_ell_le_kappa_of_fields`.) -/
theorem fpt_ell_le_kappa (D : FptDimensions) (hd0 : 1 ≤ D.d0) :
    D.ell ≤ D.k * D.d0 := by
  calc D.ell ≤ D.k := D.ell_le_k
    _ = D.k * 1 := (Nat.mul_one D.k).symm
    _ ≤ D.k * D.d0 := Nat.mul_le_mul_left D.k hd0

/-- `ℓ² ≤ κ_obs²`, monotonicity of squaring applied to `ℓ ≤ κ_obs`. -/
theorem fpt_ell_sq_le_kappa_sq (D : FptDimensions) (hd0 : 1 ≤ D.d0) :
    D.ell ^ 2 ≤ (D.k * D.d0) ^ 2 := by
  have h := fpt_ell_le_kappa D hd0
  calc D.ell ^ 2 = D.ell * D.ell := pow_two D.ell
    _ ≤ (D.k * D.d0) * (D.k * D.d0) := Nat.mul_le_mul h h
    _ = (D.k * D.d0) ^ 2 := (pow_two (D.k * D.d0)).symm

/-- Remark: `1 ≤ d0` is not actually needed, because the structure carries
`d0 ≤ k * d0` (`d0_le_kappa`): the paper's own chain is
`ℓ ≤ k ≤ d0 ≤ k * d0`, where `k` is the number `r` of output rows.  Recorded
so that the FPT core can be quoted with no numerical side condition. -/
theorem fpt_ell_le_kappa_of_fields (D : FptDimensions) :
    D.ell ≤ D.k * D.d0 :=
  le_trans D.ell_le_k (le_trans D.k_le_d0 D.d0_le_kappa)

/-- Hypothesis-free form of `fpt_ell_sq_le_kappa_sq`. -/
theorem fpt_ell_sq_le_kappa_sq_of_fields (D : FptDimensions) :
    D.ell ^ 2 ≤ (D.k * D.d0) ^ 2 := by
  have h := fpt_ell_le_kappa_of_fields D
  calc D.ell ^ 2 = D.ell * D.ell := pow_two D.ell
    _ ≤ (D.k * D.d0) * (D.k * D.d0) := Nat.mul_le_mul h h
    _ = (D.k * D.d0) ^ 2 := (pow_two (D.k * D.d0)).symm

/-! ## §2 Grassmannian chart count -/

/-- The number of `t`-subsets of a set with `m'` elements, summed over all `t`,
is `2 ^ m'`.  This is Mathlib's `Nat.sum_range_choose`. -/
theorem sum_choose_eq_two_pow (m' : ℕ) :
    (∑ t ∈ Finset.range (m' + 1), Nat.choose m' t) = 2 ^ m' :=
  Nat.sum_range_choose m'

/-- The chart count is at most `4 ^ ℓ` when `m' ≤ 2ℓ`, because
`2 ^ m' ≤ 2 ^ (2ℓ) = (2 ^ 2) ^ ℓ = 4 ^ ℓ`. -/
theorem chart_count_le_four_pow {m' ell : ℕ} (h : m' ≤ 2 * ell) :
    (∑ t ∈ Finset.range (m' + 1), Nat.choose m' t) ≤ 4 ^ ell := by
  rw [sum_choose_eq_two_pow]
  calc 2 ^ m' ≤ 2 ^ (2 * ell) := Nat.pow_le_pow_right (by norm_num) h
    _ = (2 ^ 2) ^ ell := pow_mul 2 2 ell
    _ = 4 ^ ell := by norm_num

/-- The FPT chart-count form used by the paper: the chart count for `m'` at most
`2ℓ` is at most `4 ^ ℓ`. -/
theorem fpt_chart_count_le (D : FptDimensions) (hrm : D.m' ≤ 2 * D.ell) :
    (∑ t ∈ Finset.range (D.m' + 1), Nat.choose D.m' t) ≤ 4 ^ D.ell :=
  chart_count_le_four_pow hrm

/-! ## Axiom audit -/


end Q1Paper
