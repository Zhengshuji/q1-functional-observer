import Q1Paper.PaperII.MainTheorems

/-!
Q1Paper/PaperII/Complexity.lean

The numerical core of the paper's `O(log(l+2))` counting claim in the interface theorem:
bisection over `N` candidates needs at most `Nat.log2 N + 1` halvings.

The search algorithm itself is *not* formalised; what is formalised here is the arithmetic
fact that makes its count logarithmic.
-/

namespace Q1Paper.PaperII

/-- **A power of two dominates the number.**  `N < 2 ^ (log2 N + 1)`. -/
theorem lt_two_pow_log2_succ (N : ℕ) : N < 2 ^ (N.log2 + 1) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    exact Nat.one_pos.trans_le (Nat.one_le_two_pow)
  · have hk : N.log2 < N.log2 + 1 := Nat.lt_succ_self _
    exact (Nat.log2_lt (n := N) (k := N.log2 + 1) (Nat.pos_iff_ne_zero.mp h)).mp hk

/-- **Halving reaches nothing.**  After `log2 N + 1` halvings an interval of `N` candidates
is empty, i.e. bisection terminates. -/
theorem div_two_pow_log2_succ_eq_zero (N : ℕ) : N / 2 ^ (N.log2 + 1) = 0 :=
  Nat.div_eq_of_lt (lt_two_pow_log2_succ N)

/-- **The count is a logarithm.**  The number of bisection steps on `N` candidates is at most
`log2 N + 1`. -/
theorem bisect_steps_le (N : ℕ) : ∃ k ≤ N.log2 + 1, N / 2 ^ k = 0 :=
  ⟨N.log2 + 1, le_rfl, div_two_pow_log2_succ_eq_zero N⟩

/-- The bound is monotone in `N`, so the count for `min(r, 2ℓ)` is controlled by either
argument. -/
theorem log2_mono_le {m N : ℕ} (h : m ≤ N) : m.log2 ≤ N.log2 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact Nat.zero_le _
  · rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      exact absurd h (by omega)
    · have h2 : 2 ^ m.log2 ≤ m := (Nat.le_log2 (Nat.pos_iff_ne_zero.mp hm)).mp le_rfl
      have h3 : 2 ^ m.log2 ≤ N := le_trans h2 h
      exact (Nat.le_log2 (Nat.pos_iff_ne_zero.mp hN)).mpr h3

end Q1Paper.PaperII
