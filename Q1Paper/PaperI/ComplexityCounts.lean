
import Q1Paper.PaperI.BareissAssemble
import Q1Paper.PaperI.CostCore
import Q1Paper.PaperI.RationalBasis

/-!
Q1Paper/PaperI/ComplexityCounts.lean

**The counting and bit-length layer of the Bareiss complexity analysis.**
Modules 1 and 2 of the complexity layer, plus the denominator bound of module 3.

Contents
========
§1  Counting lemmas (pure arithmetic).

* `bareissUpdateCount k`     : `∑_{j<k} (k-j)²`, the number of tableau entries
  rewritten by `k` Bareiss steps on a `k × k` matrix (step `l` rewrites the
  `(n-1-l)²` entries with `l < i` and `l < j`; after the substitution `j = n-1-l`
  the counts read `k², (k-1)², …, 1`);
* `bareissFieldOpCount k`    : `4 * bareissUpdateCount k`, the number of rational
  field operations, since each update is two products, one difference and one
  quotient;
* `bareissUpdateCount_eq_sum_succ` : the reindexing `bareissUpdateCount k = ∑_{i<k} (i+1)²`;
* `sum_range_succ_sq_mul_six`     : the exact closed form `6 ∑_{i<k} (i+1)² = k(k+1)(2k+1)`;
* `bareissUpdateCount_mul_six` / `bareissUpdateCount_eq_div` : the exact value
  `bareissUpdateCount k = k(k+1)(2k+1)/6`;
* `sum_range_sq_mul_six`          : the companion `6 ∑_{r<k} r² = k(k-1)(2k-1)`;
* `bareiss_update_count_le_cube`  : `bareissUpdateCount k ≤ k³` (each of the `k`
  summands is at most `k²`);
* `bareiss_field_op_count_le`     : `bareissFieldOpCount k ≤ 4 k³`.

§2  Bit-length arithmetic.

* `factorial_bitlen_le`           : `bitLenInt n! ≤ n · n.size` for `1 ≤ n`.
  (The statement is **false at `n = 0`**: `bitLenInt 0! = bitLenInt 1 = 1` while
  `0 * 0.size = 0`; `factorial_bitlen_le_add_one` is the unconditional `+1` form,
  and `factorial_bitlen_zero_case` records the counterexample.)
* `bitLenRat_le_of_den_eq_one`    : an integral rational's bit length is at most
  `max (bits of the numerator) 1`;
* `bareiss_entry_num_bits_le_inputLen` : restates
  `BareissAssemble.tab_entry_bitLen_inputLen`.

§3  The denominator bound.

`tab_entry_num_bitLen` controls only the numerator of a tableau entry.  The
missing half is the denominator:

* `bareiss_entry_den_eq_one` / `bareiss_entry_den_bits_le` : under the
  nonzero-leading-minor hypothesis `hΔ`, the rational tableau of `intToRat A` is
  **integral**, `den = 1`, because every entry is a bordered minor of `A`
  (`tab_entry_eq_bMinor`); the explicit "something" is therefore `1`;
* `tab_one_den_eq_one` / `tab_entry_den_eq_one_of_le_one` : the same without any
  hypothesis for `k ≤ 1` (steps `0` and `1` divide by `1` and by `A 0 0`, and
  neither quotient can leave `ℤ`);
* `bareiss_entry_bitLenRat_le` / `bareiss_entry_bitLenRat_le_factorial` : the full
  bound `bitLenRat (tab (intToRat A) k i j) ≤ n·b + n·n.size + 1` for
  `|A i j| < 2^b`, respectively `≤ max (n·b + bitLenInt n!) 1`;
* `bareiss_entry_bitLenRat_le_inputLen` : the same in terms of `inputLen`;
* `bareiss_bound_le_tauM` / `bareiss_entry_bitLenRat_le_tauM` : the same dominated
  by the Claim 13 scale `tauM` of `RationalBasis`, for nonsingular `A`.

§4  Cost aggregation.

* `fieldOpBitCost_mono` and `ratBitCost_div_le` : the per-operation envelope of
  `CostCore` at a uniform bit length `B`;
* `bareiss_steps_cost_le` : the aggregate `bareissFieldOpCount k` operations are
  cubic in `k`, by §1.

Honesty notes (see the docstrings at each item).
* `factorial_bitlen_le` needs `1 ≤ n`; the `n = 0` instance is a genuine
  counterexample, recorded as `factorial_bitlen_zero_case`.
* The sharp denominator theorem needs the hypothesis `hΔ` that the leading
  principal minors `Δ 1, …, Δ (n-1)` are nonzero, and the region `k ≤ i, j`.  Without
  `hΔ` the *identity* `tab A k i j = bord A k i j` is false (`tableau_eq_bord` is
  where `hΔ` enters, through `mul_div_cancel` by `Δ (k+1)`); the unrestricted
  hypothesis-free statement is discussed in the docstring of
  `tab_entry_den_eq_one_of_le_one`.

Imports the existing bit-length and Bareiss modules; no `sorry`, no `admit`, no
new axioms.  Check with
`lake env lean Q1Paper/PaperI/ComplexityCounts.lean`.
-/


open Matrix
open Q1Paper.PaperI.BareissTableau
open Q1Paper.PaperI.BareissAssemble

namespace Q1Paper.PaperI
namespace ComplexityCounts

/-! ## 1.  Counting lemmas -/

/-- Number of tableau entries rewritten by `k` fraction-free (Bareiss) steps: step
`l` rewrites the entries with `l < i` and `l < j`, i.e. `(n-1-l)²` of them, and
after the substitution `j = n-1-l` the counts read `k², (k-1)², …, 1`. -/
def bareissUpdateCount (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, (k - j) * (k - j)

/-- Number of rational field operations: every update is
`(a_kk a_ij - a_ik a_kj) / d`, i.e. two products, one difference and one quotient. -/
def bareissFieldOpCount (k : ℕ) : ℕ := 4 * bareissUpdateCount k

/-- Reindexing: the summands `k², (k-1)², …, 1²` are `(i+1)²` for `i < k`. -/
theorem bareissUpdateCount_eq_sum_succ (k : ℕ) :
    bareissUpdateCount k = ∑ i ∈ Finset.range k, (i + 1) ^ 2 := by
  unfold bareissUpdateCount
  have h₁ : (∑ j ∈ Finset.range k, (k - j) * (k - j))
      = ∑ j ∈ Finset.range k, ((k - 1 - j) + 1) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj' : j < k := Finset.mem_range.mp hj
    have h : k - 1 - j + 1 = k - j := by omega
    rw [h]
    ring
  rw [h₁, Finset.sum_range_reflect (fun x : ℕ => (x + 1) ^ 2) k]

/-- **The exact closed form of the shifted sum**: `6 ∑_{i<k} (i+1)² = k(k+1)(2k+1)`.

Stated with the factor `6` on the left, so that no division enters the statement. -/
theorem sum_range_succ_sq_mul_six (k : ℕ) :
    6 * (∑ i ∈ Finset.range k, (i + 1) ^ 2) = k * (k + 1) * (2 * k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring

/-- **The exact value of the update count**: `6 · bareissUpdateCount k = k(k+1)(2k+1)`. -/
theorem bareissUpdateCount_mul_six (k : ℕ) :
    6 * bareissUpdateCount k = k * (k + 1) * (2 * k + 1) := by
  rw [bareissUpdateCount_eq_sum_succ, sum_range_succ_sq_mul_six]

/-- **The exact value of the update count, division form**:
`bareissUpdateCount k = k(k+1)(2k+1)/6`. -/
theorem bareissUpdateCount_eq_div (k : ℕ) :
    bareissUpdateCount k = k * (k + 1) * (2 * k + 1) / 6 := by
  rw [← bareissUpdateCount_mul_six k, Nat.mul_div_cancel_left _ (by norm_num : 0 < 6)]

/-- **The companion sum of squares**: `6 ∑_{r<k} r² = k(k-1)(2k-1)` (so
`∑_{r<k} r² = k(k-1)(2k-1)/6`).  Written with truncated subtraction, which is
harmless: at `k = 0` both sides vanish. -/
theorem sum_range_sq_mul_six (k : ℕ) :
    6 * (∑ i ∈ Finset.range k, i ^ 2) = k * (k - 1) * (2 * k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp
      · have h1 : k + 1 - 1 = k := by omega
        have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        rw [h1, h2]
        obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
        have h3 : (a + 1) - 1 = a := by omega
        have h4 : 2 * (a + 1) - 1 = 2 * a + 1 := by omega
        rw [h3, h4]
        ring

/-- **The cubic bound on the update count**: `bareissUpdateCount k ≤ k³`.  Each of
the `k` summands `(k-j)²` is at most `k²`. -/
theorem bareiss_update_count_le_cube (k : ℕ) : bareissUpdateCount k ≤ k ^ 3 := by
  unfold bareissUpdateCount
  calc ∑ j ∈ Finset.range k, (k - j) * (k - j)
      ≤ ∑ _j ∈ Finset.range k, k * k := by
        refine Finset.sum_le_sum ?_
        intro j _
        exact Nat.mul_le_mul (Nat.sub_le k j) (Nat.sub_le k j)
    _ = k * (k * k) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ = k ^ 3 := by ring

/-- **The cubic bound on the field-operation count**: `bareissFieldOpCount k ≤ 4k³`. -/
theorem bareiss_field_op_count_le (k : ℕ) : bareissFieldOpCount k ≤ 4 * k ^ 3 :=
  Nat.mul_le_mul_left 4 (bareiss_update_count_le_cube k)

/-! ## 2.  Bit-length arithmetic -/

/-- `bitLenInt n! ≤ n · n.size` for `1 ≤ n`: `n! ≤ n ^ n < (2 ^ n.size) ^ n =
2 ^ (n · n.size)`, and `Nat.size_le`.

The hypothesis `1 ≤ n` cannot be dropped, see `factorial_bitlen_zero_case`. -/
theorem factorial_bitlen_le {n : ℕ} (hn : 1 ≤ n) :
    bitLenInt (n.factorial) ≤ n * n.size := by
  rw [bitLenInt_natCast, Nat.size_le]
  calc n.factorial ≤ n ^ n := Nat.factorial_le_pow n
    _ < (2 ^ n.size) ^ n := Nat.pow_lt_pow_left (Nat.lt_size_self n) (by omega)
    _ = 2 ^ (n.size * n) := (Nat.pow_mul 2 n.size n).symm
    _ = 2 ^ (n * n.size) := by rw [Nat.mul_comm n.size n]

/-- The unconditional `+1` form of `factorial_bitlen_le` (Claim 21's
`log₂ n! ≤ n log₂ n + 1`), inherited from `BareissBase.bitLenInt_factorial_le`. -/
theorem factorial_bitlen_le_add_one (n : ℕ) :
    bitLenInt (n.factorial) ≤ n * n.size + 1 :=
  bitLenInt_factorial_le n

/-- **`n = 0` is a genuine exception**: `bitLenInt 0! = bitLenInt 1 = 1`, while
`0 * 0.size = 0`.  So `factorial_bitlen_le` must carry `1 ≤ n`. -/
theorem factorial_bitlen_zero_case :
    ¬ (bitLenInt ((0 : ℕ).factorial) ≤ 0 * Nat.size (0 : ℕ)) := by
  decide

/-- **An integral rational's bit length is `max (bits of the numerator) 1`.**
Consequently, once the denominator of a tableau entry is known to be `1`, the
`bitLenRat` bound of the entry costs nothing beyond the numerator bound. -/
theorem bitLenRat_le_of_den_eq_one {q : ℚ} (h : q.den = 1) {X : ℕ}
    (hX : bitLenInt q.num ≤ X) : bitLenRat q ≤ max X 1 := by
  unfold bitLenRat
  rw [h]
  exact max_le_max hX (le_refl 1)

/-- **Restatement of `BareissAssemble.tab_entry_bitLen_inputLen`**: the bordered
minor that indexes the tableau entry `tab (intToRat A.num) k i j` — i.e. the
*numerator* of that entry, by `tab_entry_eq_bMinor` — has at most
`n · inputLen A + bitLenInt n!` bits. -/
theorem bareiss_entry_num_bits_le_inputLen {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) :
    bitLenInt (bMinor A.num (snocIdx (prefMap k) i) (snocIdx (prefMap k) j))
      ≤ n * inputLen A + bitLenInt (n.factorial) :=
  tab_entry_bitLen_inputLen A k i j hi

/-! ## 3.  The denominator bound -/

/-- **The rational tableau of an integer matrix is integral on the nonzero-minor
locus.**  Under `hΔ` every tableau entry is a bordered minor of `A`
(`tab_entry_eq_bMinor`), so its denominator as a rational is `1`: the fraction-free
tableau exhibits no denominator growth at all, and the "missing denominator bound"
of `tab_entry_num_bitLen` is simply `den = 1`.

The hypotheses are the ones `tableau_eq_bord` needs: nonzero leading principal
minors `Δ 1, …, Δ (n-1)`, and the region `k ≤ i, j` where the tableau has resolved
the entry. -/
theorem bareiss_entry_den_eq_one {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ)
    (hΔ : ∀ m, m < n → delta (intToRat A) m ≠ 0)
    (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    (tab (intToRat A) k i j).den = 1 := by
  rw [tab_entry_eq_bMinor A hΔ k i j hi hj, Rat.den_intCast]

/-- **The explicit denominator bound**: the denominator of the rational tableau
entry is at most `1`, i.e. exactly `1`. -/
theorem bareiss_entry_den_bits_le {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ)
    (hΔ : ∀ m, m < n → delta (intToRat A) m ≠ 0)
    (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    (tab (intToRat A) k i j).den ≤ 1 := by
  rw [bareiss_entry_den_eq_one A hΔ k i j hi hj]

/-- **Step `1` is integral with no hypothesis at all.**  The step-`0` formula
`tab (intToRat A) 1 i j = (A 0 0 · A i j - A i 0 · A 0 j) / 1` (and `= A i j` on the
untouched entries) is a quotient of an integer by `1`, hence an integer. -/
theorem tab_one_den_eq_one {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) : (tab (intToRat A) 1 i j).den = 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [tab_one, tab_zero]
  by_cases h : 0 < i.val ∧ 0 < j.val
  · rw [stepMat_apply_of (M := intToRat A) (P := intToRat A) hn h.1 h.2, divAt_zero, div_one]
    have h0 : (⟨0, hn⟩ : Fin n) = (0 : Fin n) := Fin.ext rfl
    rw [h0]
    have hval : (intToRat A) 0 0 * (intToRat A) i j - (intToRat A) i 0 * (intToRat A) 0 j
        = (((A 0 0 * A i j - A i 0 * A 0 j) : ℤ) : ℚ) := by
      simp only [intToRat, Matrix.map_apply]
      push_cast
      ring
    rw [hval, Rat.den_intCast]
  · have hcopy : stepMat (intToRat A) (intToRat A) 0 i j = (intToRat A) i j := by
      unfold stepMat
      rw [dif_pos hn, dif_neg h]
    rw [hcopy]
    simp only [intToRat, Matrix.map_apply]
    exact Rat.den_intCast (A i j)

/-- **The denominator bound for steps `0` and `1`, with no hypothesis.**

Everything the sharp theorem `bareiss_entry_den_eq_one` needs beyond `k ≤ 1` is the
exact-division property `Δ (k+1) ∣ numerator` (that is `bareiss_step_one_dvd`
generalised to every step, which is Desnanot–Jacobi).  For `k ≤ 1` no division by a
pivot is ever performed, so no hypothesis is required.

**Precisely what remains for the unrestricted statement** (`k` arbitrary, no `hΔ`,
no `k ≤ i, j`): one has to redo the induction of `tableau_eq_bord` with the
disjunctive invariant

`(∀ i j, k ≤ i → k ≤ j → tab A k i j = bord A k i j) ∨ (∀ i j, k ≤ i → k ≤ j → tab A k i j = 0)`

— the second case being what actually happens at the first zero pivot `Δ (k+1) = 0`,
where the recurrence divides `0` by `0` and produces `0` instead of the minor.
That invariant does yield `den = 1` at every level (both `bord` of an integer matrix
and `0` are integers), so `den = 1` is expected to hold unconditionally; what is
missing is only this stronger form of the tableau identity, plus a stabilisation
lemma `tab A k i j = tab A (min i j + 1) i j` for entries outside the region
`k ≤ i, j`. -/
theorem tab_entry_den_eq_one_of_le_one {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ)
    {k : ℕ} (hk : k ≤ 1) (i j : Fin n) : (tab (intToRat A) k i j).den = 1 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · rw [hk0, tab_zero]
    simp only [intToRat, Matrix.map_apply]
    exact Rat.den_intCast (A i j)
  · have hk1' : k = 1 := by omega
    rw [hk1']
    exact tab_one_den_eq_one A i j

/-- **The full `bitLenRat` bound for a tableau entry of an integer matrix** with
`|A i j| < 2^b`: at most `n·b + n·n.size + 1` bits (numerator by
`tab_entry_num_bitLen`, denominator `1` by `bareiss_entry_den_eq_one`). -/
theorem bareiss_entry_bitLenRat_le {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ)
    (hΔ : ∀ m, m < n → delta (intToRat A) m ≠ 0)
    {b : ℕ} (hM : ∀ i j, |A i j| < (2 : ℤ) ^ b)
    (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    bitLenRat (tab (intToRat A) k i j) ≤ n * b + n * n.size + 1 := by
  have hnum : bitLenInt (tab (intToRat A) k i j).num ≤ n * b + n * n.size + 1 := by
    have h1 := tab_entry_num_bitLen A hΔ hM k i j hi hj
    have h2 := bitLenInt_factorial_le n
    omega
  have hden : (tab (intToRat A) k i j).den.size ≤ n * b + n * n.size + 1 := by
    rw [bareiss_entry_den_eq_one A hΔ k i j hi hj]
    simp
  exact max_le hnum hden

/-- The same bound with the factorial term left explicit:
`bitLenRat ≤ max (n·b + bitLenInt n!) 1`. -/
theorem bareiss_entry_bitLenRat_le_factorial {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hΔ : ∀ m, m < n → delta (intToRat A) m ≠ 0)
    {b : ℕ} (hM : ∀ i j, |A i j| < (2 : ℤ) ^ b)
    (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    bitLenRat (tab (intToRat A) k i j) ≤ max (n * b + bitLenInt (n.factorial)) 1 :=
  bitLenRat_le_of_den_eq_one (bareiss_entry_den_eq_one A hΔ k i j hi hj)
    (tab_entry_num_bitLen A hΔ hM k i j hi hj)

/-- **The `inputLen` form of the same bound**, for the cleared integer matrix
`A.num` of a rational input `A`. -/
theorem bareiss_entry_bitLenRat_le_inputLen {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hΔ : ∀ m, m < n → delta (intToRat A.num) m ≠ 0)
    (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    bitLenRat (tab (intToRat A.num) k i j) ≤ n * inputLen A + bitLenInt (n.factorial) := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hnum : bitLenInt (tab (intToRat A.num) k i j).num
      ≤ n * inputLen A + bitLenInt (n.factorial) := by
    have h1 := tab_entry_num_bitLen A.num hΔ (b := bitLenMat A)
      (fun a c => mat_abs_num_lt_two_pow_bitLenMat A a c) k i j hi hj
    have h2 : bitLenMat A ≤ inputLen A :=
      bitLenMat_le_inputLen A (by omega)
    have h3 : n * bitLenMat A ≤ n * inputLen A := Nat.mul_le_mul_left n h2
    omega
  have hX : max (n * inputLen A + bitLenInt (n.factorial)) 1
      ≤ n * inputLen A + bitLenInt (n.factorial) := by
    have hin : 1 ≤ inputLen A := by unfold inputLen; omega
    have hpos : 1 ≤ n * inputLen A := Nat.mul_pos (by omega) (by omega)
    omega
  exact le_trans (bitLenRat_le_of_den_eq_one
    (bareiss_entry_den_eq_one A.num hΔ k i j hi hj) hnum) hX

/-- **The Bareiss entry bound is below the Claim 13 Cramer scale `tauM`** of
`RationalBasis`, for a nonsingular integer matrix: `n·b + bitLenInt n! ≤
tauM (intToRat A) b`. -/
theorem bareiss_bound_le_tauM {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ)
    {b : ℕ} (hrank : (intToRat A).rank = n) :
    n * b + bitLenInt (n.factorial) ≤ tauM (intToRat A) b := by
  have h := rank_mul_tau_add_factorial_le_tauM (intToRat A) b
  rwa [hrank] at h

/-- **The `tauM` form of the tableau bit-length bound**: for nonsingular `A`, every
tableau entry has at most `tauM (intToRat A) b` bits. -/
theorem bareiss_entry_bitLenRat_le_tauM {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ)
    (hΔ : ∀ m, m < n → delta (intToRat A) m ≠ 0)
    {b : ℕ} (hM : ∀ i j, |A i j| < (2 : ℤ) ^ b)
    (hrank : (intToRat A).rank = n)
    (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    bitLenRat (tab (intToRat A) k i j) ≤ tauM (intToRat A) b := by
  refine le_trans (bareiss_entry_bitLenRat_le_factorial A hΔ hM k i j hi hj) ?_
  exact max_le (bareiss_bound_le_tauM A hrank) (one_le_tauM (intToRat A) b)

/-! ## 4.  Cost aggregation -/

/-- **The `CostCore` envelope is monotone in both operand bit lengths.** -/
theorem fieldOpBitCost_mono (op : Q1Complexity.FieldOp) {a b a' b' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') :
    Q1Complexity.fieldOpBitCost op a b ≤ Q1Complexity.fieldOpBitCost op a' b' := by
  cases op with
  | add =>
      simp only [Q1Complexity.fieldOpBitCost]
      have h : a + b + 1 ≤ a' + b' + 1 := by omega
      have h2 : (a + b + 1) ^ 2 ≤ (a' + b' + 1) ^ 2 := by
        rw [pow_two, pow_two]
        exact Nat.mul_le_mul h h
      have h3 : 64 * (a + b + 1) ^ 2 ≤ 64 * (a' + b' + 1) ^ 2 := Nat.mul_le_mul_left 64 h2
      omega
  | sub =>
      simp only [Q1Complexity.fieldOpBitCost]
      have h : a + b + 1 ≤ a' + b' + 1 := by omega
      have h2 : (a + b + 1) ^ 2 ≤ (a' + b' + 1) ^ 2 := by
        rw [pow_two, pow_two]
        exact Nat.mul_le_mul h h
      have h3 : 64 * (a + b + 1) ^ 2 ≤ 64 * (a' + b' + 1) ^ 2 := Nat.mul_le_mul_left 64 h2
      omega
  | mul =>
      simp only [Q1Complexity.fieldOpBitCost]
      have hm : a * b ≤ a' * b' := Nat.mul_le_mul ha hb
      have h : a * b + a + b + 1 ≤ a' * b' + a' + b' + 1 := by omega
      have h2 : (a * b + a + b + 1) ^ 2 ≤ (a' * b' + a' + b' + 1) ^ 2 := by
        rw [pow_two, pow_two]
        exact Nat.mul_le_mul h h
      have h3 : 64 * (a * b + a + b + 1) ^ 2 ≤ 64 * (a' * b' + a' + b' + 1) ^ 2 :=
        Nat.mul_le_mul_left 64 h2
      omega
  | div =>
      simp only [Q1Complexity.fieldOpBitCost]
      have hm : a * b ≤ a' * b' := Nat.mul_le_mul ha hb
      have h : a * b + a + b + 1 ≤ a' * b' + a' + b' + 1 := by omega
      have h2 : (a * b + a + b + 1) ^ 2 ≤ (a' * b' + a' + b' + 1) ^ 2 := by
        rw [pow_two, pow_two]
        exact Nat.mul_le_mul h h
      have h3 : 64 * (a * b + a + b + 1) ^ 2 ≤ 64 * (a' * b' + a' + b' + 1) ^ 2 :=
        Nat.mul_le_mul_left 64 h2
      omega
  | inv =>
      simp only [Q1Complexity.fieldOpBitCost]
      have h : a + 1 ≤ a' + 1 := by omega
      have h2 : (a + 1) ^ 2 ≤ (a' + 1) ^ 2 := by
        rw [pow_two, pow_two]
        exact Nat.mul_le_mul h h
      have h3 : 64 * (a + 1) ^ 2 ≤ 64 * (a' + 1) ^ 2 := Nat.mul_le_mul_left 64 h2
      omega

/-- **One division at operand bit length `B` costs at most the envelope at `B`**:
the derived cost `ratBitCost` of `CostCore` is dominated by `fieldOpBitCost`,
monotonically in the two operand bit lengths. -/
theorem ratBitCost_div_le (p q : ℚ) {B : ℕ} (hp : bitLenRat p ≤ B) (hq : bitLenRat q ≤ B) :
    Q1Complexity.ratBitCost Q1Complexity.FieldOp.div p q
      ≤ Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div B B :=
  le_trans (Q1Complexity.ratBitCost_le_fieldOpBitCost Q1Complexity.FieldOp.div p q)
    (fieldOpBitCost_mono Q1Complexity.FieldOp.div hp hq)

/-- **The aggregate cost of `k` Bareiss steps is cubic.**  There are
`bareissFieldOpCount k` field operations, each dominated by the envelope at the
uniform bit length `B`, so the aggregate is at most
`4 · k³ · fieldOpBitCost div B B`. -/
theorem bareiss_steps_cost_le (k B : ℕ) :
    bareissFieldOpCount k * Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div B B
      ≤ 4 * k ^ 3 * Q1Complexity.fieldOpBitCost Q1Complexity.FieldOp.div B B :=
  Nat.mul_le_mul_right _ (bareiss_field_op_count_le k)

end ComplexityCounts
end Q1Paper.PaperI
