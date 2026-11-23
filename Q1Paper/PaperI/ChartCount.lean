/-
Q1Paper/PaperI/ChartCount.lean

**Chart-count arithmetic for Theorem 1.**

Theorem 1 of the paper combines the chart count
`Nch = (q + 1) * k ^ q`  (with `k ≤ n ≤ L`)
with a per-chart cost, and the final bound has the shape
`C * (L + 1) ^ (d * (q + 1) ^ 2)`.

This file isolates the pure `ℕ` arithmetic needed to pass from the chart count
to that shape.  Nothing here mentions matrices or charts: it is the counting
layer only.

Contents
========
* `chart_count_le`     : `(q+1) * k^q ≤ (L+1)^(2*(q+1))`  (base `L+1`);
* `chart_count_le_pow` : `(q+1) * k^q ≤ L^(2*q+2)`        (base `L`);
* `exp_compose`        : exponent bookkeeping,
  `c2*(q+1)^2 + 2*q + 2 ≤ (c2+2)*(q+1)^2`;
* `beta_le_L_pow`      : `β ≤ 240*q*n^5*L → β ≤ 240*L^7` for `q, n ≤ L`.

Honesty notes
=============
* `chart_count_le` and `chart_count_le_pow` carry `1 ≤ q` for interface
  compatibility with the paper (`q` is the observer order), but **neither proof
  uses it**: both inequalities also hold at `q = 0`, where `k ^ 0 = 1` and the
  right-hand side is at least `(L+1)^2 ≥ 9` (resp. `L^2 ≥ 4`).
* `exp_compose` is unconditional: `2*q + 2 = 2*(q+1)` and `q+1 ≤ (q+1)^2`, so
  the `2*q + 2` term is absorbed by the two extra copies of `(q+1)^2` on the
  right.  It holds at `q = 0` as well.
* `beta_le_L_pow` uses `q ≤ L` and `n ≤ L`: `q * n^5 * L ≤ L * L^5 * L = L^7`.
  The hypothesis `hL : 2 ≤ L` is *not* needed by the proof (the chain also
  holds at `L = 0, 1`); it is kept because the paper assumes it.

No `sorry`, no `admit`, no new axioms.  Check with
`lake env lean Q1Paper/PaperI/ChartCount.lean`.
-/

import Mathlib

namespace Q1Paper

/-- `n ≤ 2 ^ n` for every `n : ℕ`: induction, using `2 ^ m ≥ 1` to double. -/
private theorem le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hpos : 1 ≤ 2 ^ m := by
        have := pow_pos (by norm_num : (0 : ℕ) < 2) m
        omega
      calc m + 1 ≤ 2 ^ m + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add (le_refl (2 ^ m)) hpos
        _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

/-- **Chart count against base `L + 1`.**
`(q+1) * k^q ≤ (L+1)^(2*(q+1))` for `k ≤ L`, `2 ≤ L`.

Route: `k^q ≤ L^q ≤ (L+1)^q ≤ (L+1)^(q+1)` and `q+1 ≤ 2^(q+1) ≤ (L+1)^(q+1)`;
multiply the two `(L+1)^(q+1)` bounds and use `(q+1)+(q+1) = 2*(q+1)`.

The hypothesis `1 ≤ q` is not used (see the file header). -/
theorem chart_count_le {q k L : ℕ} (hq : 1 ≤ q) (hk : k ≤ L) (hL : 2 ≤ L) :
    (q + 1) * k ^ q ≤ (L + 1) ^ (2 * (q + 1)) := by
  have hkq : k ^ q ≤ (L + 1) ^ (q + 1) := by
    calc k ^ q ≤ L ^ q := Nat.pow_le_pow_left hk q
      _ ≤ (L + 1) ^ q := Nat.pow_le_pow_left (Nat.le_succ L) q
      _ ≤ (L + 1) ^ (q + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hq1 : q + 1 ≤ (L + 1) ^ (q + 1) := by
    calc q + 1 ≤ 2 ^ (q + 1) := le_two_pow (q + 1)
      _ ≤ (L + 1) ^ (q + 1) := Nat.pow_le_pow_left (by omega) (q + 1)
  calc (q + 1) * k ^ q ≤ (L + 1) ^ (q + 1) * (L + 1) ^ (q + 1) :=
        Nat.mul_le_mul hq1 hkq
    _ = (L + 1) ^ (2 * (q + 1)) := by
        rw [← pow_add]
        congr 1
        ring

/-- **Chart count against base `L`.**
`(q+1) * k^q ≤ L^(2*q+2)` for `k ≤ L`, `2 ≤ L`.

Route: `k^q ≤ L^q` and `q+1 ≤ 2^(q+1) ≤ 2^(q+2) ≤ L^(q+2)`; multiply,
then `(q+2) + q = 2*q + 2`.

The hypothesis `1 ≤ q` is not used (see the file header). -/
theorem chart_count_le_pow {q k L : ℕ} (hq : 1 ≤ q) (hk : k ≤ L) (hL : 2 ≤ L) :
    (q + 1) * k ^ q ≤ L ^ (2 * q + 2) := by
  have hkq : k ^ q ≤ L ^ q := Nat.pow_le_pow_left hk q
  have hq1 : q + 1 ≤ L ^ (q + 2) := by
    calc q + 1 ≤ 2 ^ (q + 1) := le_two_pow (q + 1)
      _ ≤ 2 ^ (q + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ L ^ (q + 2) := Nat.pow_le_pow_left hL (q + 2)
  calc (q + 1) * k ^ q ≤ L ^ (q + 2) * L ^ q := Nat.mul_le_mul hq1 hkq
    _ = L ^ (2 * q + 2) := by
        rw [← pow_add]
        congr 1
        omega

/-- **Exponent composition.**
`c2*(q+1)^2 + 2*q + 2 ≤ (c2+2)*(q+1)^2`, i.e. the additive `2*q + 2` is
absorbed by two extra copies of `(q+1)^2`.  Unconditional in `c2` and `q`.

Route: `2*q + 2 = 2*(q+1)` and `q+1 ≤ (q+1)^2`; add `c2*(q+1)^2` on both sides
and rewrite `(c2+2)*(q+1)^2 = c2*(q+1)^2 + 2*(q+1)^2`. -/
theorem exp_compose {c2 q : ℕ} :
    c2 * (q + 1) ^ 2 + 2 * q + 2 ≤ (c2 + 2) * (q + 1) ^ 2 := by
  have hsq : q + 1 ≤ (q + 1) ^ 2 := by
    calc q + 1 = (q + 1) * 1 := (Nat.mul_one (q + 1)).symm
      _ ≤ (q + 1) * (q + 1) := Nat.mul_le_mul (le_refl (q + 1)) (by omega)
      _ = (q + 1) ^ 2 := by ring
  calc c2 * (q + 1) ^ 2 + 2 * q + 2
      = c2 * (q + 1) ^ 2 + 2 * (q + 1) := by ring
    _ ≤ c2 * (q + 1) ^ 2 + 2 * (q + 1) ^ 2 :=
        Nat.add_le_add (le_refl (c2 * (q + 1) ^ 2)) (Nat.mul_le_mul (le_refl 2) hsq)
    _ = (c2 + 2) * (q + 1) ^ 2 := by ring

/-- **`β` bound with `L^7`.**
`β ≤ 240*q*n^5*L` and `q ≤ L`, `n ≤ L` give `β ≤ 240*L^7`
(via `q*n^5*L ≤ L*L^5*L = L^7`).

The hypothesis `hL : 2 ≤ L` is not needed by the proof (see the file header). -/
theorem beta_le_L_pow (β n q L : ℕ) (hβ : β ≤ 240 * q * n ^ 5 * L) (hn : n ≤ L) (hq : q ≤ L)
    (hL : 2 ≤ L) : β ≤ 240 * L ^ 7 := by
  have hn5 : n ^ 5 ≤ L ^ 5 := Nat.pow_le_pow_left hn 5
  have h : q * n ^ 5 * L ≤ L ^ 7 := by
    have hq5 : q * n ^ 5 ≤ L * L ^ 5 := Nat.mul_le_mul hq hn5
    calc q * n ^ 5 * L ≤ (L * L ^ 5) * L := Nat.mul_le_mul hq5 (le_refl L)
      _ = L ^ 7 := by ring
  calc β ≤ 240 * q * n ^ 5 * L := hβ
    _ = 240 * (q * n ^ 5 * L) := by ring
    _ ≤ 240 * L ^ 7 := Nat.mul_le_mul (le_refl 240) h


end Q1Paper
