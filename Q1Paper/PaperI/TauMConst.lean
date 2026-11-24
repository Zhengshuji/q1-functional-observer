
import Q1Paper.PaperI.RationalBasis

/-!
Q1Paper/PaperI/TauMConst.lean

The paper constant for the Claim 13 bit bound `tauM`.

`PaperI/RationalBasis.lean` defines

  `tauM M τ = 2 * M.rank * ((n + 1) * τ + (M.rank + 1).size + 1) + 1`

and runs it with `τ = bitLenMat M`.  For the asymptotic statement of Claim 13 one
wants the *unconditional* polynomial bound `tauM M (bitLenMat M) ≤ 123 * n ^ 6 * L`
whenever `bitLenMat M ≤ L`, `3 ≤ n`, `2 ≤ L`.

This file supplies that bound with the paper's constant `123`:

* `tauM_le_of_bounds` — the general form, with the input bit length abstract
  (`τ ≤ L`) and the rank bound `M.rank ≤ n` as an explicit hypothesis;
* `tauM_le_paper_constant` — the specialisation `τ = bitLenMat M`, where the
  hypothesis `bitLenMat M ≤ L` gives `τ ≤ L` and `Matrix.rank_le_width` gives
  `M.rank ≤ n`.

Proof route (the bracket estimate is the whole content):

* `M.rank ≤ n`, so `(M.rank + 1).size ≤ (n + 1).size` (`Nat.size_le_size`) and
  `(n + 1).size ≤ n + 1`, the latter because `n + 1 < 2 ^ (n + 1)`
  (`Nat.size_le.mpr` together with `Nat.lt_two_pow_self`);
* `τ ≤ L`, so `(n + 1) * τ ≤ (n + 1) * L`;
* hence the bracket `(n + 1) * τ + (M.rank + 1).size + 1 ≤ (n + 1) * L + n + 2
  ≤ 4 * n * L` (the last step uses `3 ≤ n` and `2 ≤ L`);
* therefore `tauM ≤ 2 * n * (4 * n * L) + 1 = 8 * n ^ 2 * L + 1 ≤ 123 * n ^ 6 * L`
  (the last step uses `1 ≤ L` and `n ^ 6 = n ^ 2 * n ^ 4`).

No `sorry`, no `admit`, no new axioms.
-/


open Matrix

namespace Q1Paper.PaperI

/-- **Polynomial bound on `tauM`, general form.**  If the input bit length `τ` is
at most `L`, the rank is at most `n`, and `3 ≤ n`, `2 ≤ L`, then the Claim 13
constant is at most `123 * n ^ 6 * L` (the paper's constant).

The bracket `(n + 1) * τ + (rank + 1).size + 1` is at most `4 * n * L`; then
`2 * rank * bracket + 1 ≤ 8 * n ^ 2 * L + 1 ≤ 123 * n ^ 6 * L`. -/
theorem tauM_le_of_bounds {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) {τ L : ℕ}
    (hτ : τ ≤ L) (hrank : M.rank ≤ n) (hn : 3 ≤ n) (hL2 : 2 ≤ L) :
    tauM M τ ≤ 123 * n ^ 6 * L := by
  -- ## the bracket estimate
  have hsize : (M.rank + 1).size ≤ (n + 1).size := Nat.size_le_size (by omega)
  have hsize2 : (n + 1).size ≤ n + 1 :=
    Nat.size_le.mpr (@Nat.lt_two_pow_self (n + 1))
  have hmul : (n + 1) * τ ≤ (n + 1) * L := Nat.mul_le_mul (le_refl _) hτ
  have hstep : (n + 1) * τ + (M.rank + 1).size + 1 ≤ (n + 1) * L + (n + 1) + 1 :=
    Nat.add_le_add (Nat.add_le_add hmul (le_trans hsize hsize2)) (le_refl 1)
  have hB : (n + 1) * τ + (M.rank + 1).size + 1 ≤ 4 * n * L := by
    calc (n + 1) * τ + (M.rank + 1).size + 1
        ≤ (n + 1) * L + (n + 1) + 1 := hstep
      _ = (n + 1) * L + n + 2 := by omega
      _ ≤ 4 * n * L := by nlinarith
  -- ## monotonicity in rank and bracket
  have h2 : 2 * M.rank ≤ 2 * n := Nat.mul_le_mul (le_refl 2) hrank
  have hAB : 2 * M.rank * ((n + 1) * τ + (M.rank + 1).size + 1) ≤ 2 * n * (4 * n * L) :=
    Nat.mul_le_mul h2 hB
  -- ## the numerical core: `8 * n ^ 2 * L + 1 ≤ 123 * n ^ 6 * L`
  have hpos : 0 < n ^ 2 * L := Nat.mul_pos (pow_pos (by omega : 0 < n) 2) (by omega)
  have hpos' : 1 ≤ n ^ 2 * L := Nat.succ_le_of_lt hpos
  have hn4 : 1 ≤ n ^ 4 := Nat.succ_le_of_lt (pow_pos (by omega : 0 < n) 4)
  have h9 : 9 ≤ 123 * n ^ 4 := by nlinarith
  have h4 : 9 * n ^ 2 ≤ 123 * n ^ 4 * n ^ 2 := Nat.mul_le_mul h9 (le_refl (n ^ 2))
  have h5 : 9 * n ^ 2 ≤ 123 * n ^ 6 := by
    calc 9 * n ^ 2 ≤ 123 * n ^ 4 * n ^ 2 := h4
      _ = 123 * n ^ 6 := by ring
  unfold tauM
  calc 2 * M.rank * ((n + 1) * τ + (M.rank + 1).size + 1) + 1
      ≤ 2 * n * (4 * n * L) + 1 := Nat.add_le_add hAB (le_refl 1)
    _ = 8 * n ^ 2 * L + 1 := by ring
    _ ≤ 8 * n ^ 2 * L + n ^ 2 * L := Nat.add_le_add (le_refl _) hpos'
    _ = 9 * n ^ 2 * L := by ring
    _ ≤ 123 * n ^ 6 * L := Nat.mul_le_mul h5 (le_refl L)

/-- **The paper constant with `τ = bitLenMat M`.**  This is the form used in
Claim 13's asymptotic statement: the bound is `O(n ^ 6 * L)` with constant `123`.

`hL : bitLenMat M ≤ L` supplies `τ ≤ L`, and `Matrix.rank_le_width` supplies
`M.rank ≤ n`. -/
theorem tauM_le_paper_constant {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) {L : ℕ}
    (hL : Q1Paper.PaperI.bitLenMat M ≤ L) (hn : 3 ≤ n) (hL2 : 2 ≤ L) :
    Q1Paper.PaperI.tauM M (Q1Paper.PaperI.bitLenMat M) ≤ 123 * n ^ 6 * L :=
  tauM_le_of_bounds M hL (by simpa using Matrix.rank_le_width M) hn hL2

end Q1Paper.PaperI

