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


/-- **One bisection step at least halves the interval.**  Splitting `[lo, hi]` at the midpoint
`m = (lo + hi) / 2` leaves two subintervals of length at most `(hi − lo) / 2`. -/
theorem half_width (lo hi : ℕ) (h : lo < hi) :
    ((lo + hi) / 2 - lo ≤ (hi - lo) / 2) ∧
      (hi - ((lo + hi) / 2 + 1) ≤ (hi - lo) / 2) := by
  constructor <;> omega


/-- **Bisection with fuel.**  `bisectGo P k lo hi` performs `k` halvings of the interval
`[lo, hi]`, querying the predicate `P` at the midpoint and keeping the half on which a threshold
must lie. -/
def bisectGo (P : Nat → Bool) : Nat → Nat → Nat → Nat × Nat
  | 0, lo, hi => (lo, hi)
  | k + 1, lo, hi =>
      if lo < hi then
        let m := (lo + hi) / 2
        if P m then bisectGo P k lo m else bisectGo P k (m + 1) hi
      else (lo, hi)

/-- **The interval shrinks by `2 ^ k`.**  After `k` halvings the interval lies inside the
original one and its length is at most `(hi - lo) / 2 ^ k`. -/
theorem bisectGo_spec (P : Nat → Bool) :
    ∀ (k lo hi : Nat), lo ≤ hi →
      lo ≤ (bisectGo P k lo hi).1 ∧ (bisectGo P k lo hi).1 ≤ (bisectGo P k lo hi).2 ∧
        (bisectGo P k lo hi).2 ≤ hi ∧
        (bisectGo P k lo hi).2 - (bisectGo P k lo hi).1 ≤ (hi - lo) / 2 ^ k
  | 0, lo, hi, h => by
    refine ⟨le_rfl, h, le_rfl, ?_⟩
    simp [bisectGo]
  | k + 1, lo, hi, h => by
    rw [bisectGo]
    by_cases hlt : lo < hi
    · rw [if_pos hlt]
      have hw := half_width lo hi hlt
      have hm1 : lo ≤ (lo + hi) / 2 := by omega
      have hm2 : (lo + hi) / 2 + 1 ≤ hi := by omega
      by_cases hp : P ((lo + hi) / 2)
      · rw [if_pos hp]
        obtain ⟨a1, a2, a3, a4⟩ := bisectGo_spec P k lo ((lo + hi) / 2) hm1
        refine ⟨a1, a2, by omega, ?_⟩
        calc (bisectGo P k lo ((lo + hi) / 2)).2 - (bisectGo P k lo ((lo + hi) / 2)).1
            ≤ ((lo + hi) / 2 - lo) / 2 ^ k := a4
          _ ≤ ((hi - lo) / 2) / 2 ^ k := Nat.div_le_div_right hw.1
          _ = (hi - lo) / 2 ^ (k + 1) := by
              rw [Nat.div_div_eq_div_mul, pow_succ]
              ring_nf
      · rw [if_neg hp]
        obtain ⟨a1, a2, a3, a4⟩ := bisectGo_spec P k ((lo + hi) / 2 + 1) hi hm2
        refine ⟨by omega, a2, a3, ?_⟩
        calc (bisectGo P k ((lo + hi) / 2 + 1) hi).2 - (bisectGo P k ((lo + hi) / 2 + 1) hi).1
            ≤ (hi - ((lo + hi) / 2 + 1)) / 2 ^ k := a4
          _ ≤ ((hi - lo) / 2) / 2 ^ k := Nat.div_le_div_right hw.2
          _ = (hi - lo) / 2 ^ (k + 1) := by
              rw [Nat.div_div_eq_div_mul, pow_succ]
              ring_nf
    · rw [if_neg hlt]
      have hle : hi ≤ lo := by omega
      have hEq : hi = lo := le_antisymm hle h
      subst hEq
      exact ⟨le_rfl, le_rfl, le_rfl, by simp⟩


/-- **Bisection collapses the interval within `log2 N + 1` halvings.**  For an interval of `N + 1`
integers (length `N`), that many halvings leave a single point, so the search makes
`log2 N + 1 = O(log(N+2))` queries. -/
theorem bisectGo_collapses (P : Nat → Bool) (lo hi : Nat) (h : lo ≤ hi) :
    (bisectGo P ((hi - lo).log2 + 1) lo hi).1
      = (bisectGo P ((hi - lo).log2 + 1) lo hi).2 := by
  have hs := bisectGo_spec P ((hi - lo).log2 + 1) lo hi h
  have hz : (hi - lo) / 2 ^ ((hi - lo).log2 + 1) = 0 := div_two_pow_log2_succ_eq_zero _
  have hw : (bisectGo P ((hi - lo).log2 + 1) lo hi).2
      - (bisectGo P ((hi - lo).log2 + 1) lo hi).1 = 0 := by
    have h4 := hs.2.2.2
    omega
  omega

end Q1Paper.PaperII
