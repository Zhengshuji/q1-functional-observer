
import Q1Paper.PaperI.BareissTableau
import Q1Paper.PaperI.BareissBase
import Q1Paper.PaperI.InputLen

/-!
Q1Paper/PaperI/BareissAssemble.lean

**Assembling the Bareiss tableau, and its bit-length corollary.**

`Q1Paper/PaperI/BareissTableau.lean` proves: *any* family `T : ℕ → Matrix (Fin n) (Fin n) K`
obeying the fraction-free recurrence (`T 0 = A`, the step-`0` formula, the step-`l+1`
formula) has `T k i j = bord A k i j` on the region `i, j ≥ k`, provided the leading
principal minors `Δ 0, …, Δ (n-1)` are nonzero.  That file never *builds* such a family: it
is a conditional statement about an abstract `T`.  This file closes that mechanical gap.

§1  Building the tableau.

* `divAt`     : the divisor of a step, `1` for the first step and the previous pivot after;
* `stepMat`   : one fraction-free step with a given pivot index;
* `tabPair`   : the recursion state `(T k, T (k-1))`, with `T (-1) := A`;
* `tab`       : the tableau, `tab A k = (tabPair A k).1`.

§2  The three hypotheses of `tableau_eq_bord`, and the assembled theorems.

* `tab_zero`  : `tab A 0 = A`;
* `tab_step0` : the step-`0` formula (divisor `1`);
* `tab_step`  : the step-`l+1` formula (divisor `T l l l`);
* `tab_eq_bord` : `tab A k i j = bord A k i j` for `k ≤ i`, `k ≤ j`;
* `tab_pivot` : `tab A k k k = Δ (k+1)`;
* `tab_last`  : `tab A (n-1) (n-1) (n-1) = det A`.

§3  The bit-length corollary (integer input).

* `tab_entry_eq_bMinor` : for `A` over `ℤ`, every rational tableau entry of the cast
  `intToRat A` is the cast of the corresponding integer bordered minor (so the tableau is
  integral and consists of minors);
* `tab_entry_bitLen` / `tab_entry_bitLen_size` : hence, when `|A i j| < 2^b`, every tableau
  entry has at most `n * b + bitLenInt (n!)` bits (`n * b + n * n.size + 1` in closed form);
* `tab_entry_num_bitLen` : the same bound for the numerator of the tableau entry itself;
* `tab_last_num_bitLen` : the last entry is `det A`, so its numerator has at most
  `n * b + bitLenInt (n!)` bits;
* `tab_entry_bitLen_bitLenMat` / `tab_entry_bitLen_inputLen` : the same for the cleared
  integer matrix `A.num` of a rational input, in terms of `bitLenMat A` / `inputLen A`.

No `sorry`, no `admit`, no new axioms.  Check with
  `lake env lean Q1Paper/PaperI/BareissAssemble.lean`
-/


open Matrix
open Q1Paper.PaperI.BareissTableau

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Q1Paper.PaperI
namespace BareissAssemble

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

/-! ## 1.  Building the tableau by recursion -/

/-- The divisor of the step whose **new** pivot index is `l`: `1` for `l = 0` (the first
step divides by `Δ 0 = 1`) and `M (l-1) (l-1)` otherwise, where `M` is the tableau of the
previous stage.  Out-of-range `l` yields the junk value `1`, which is never used. -/
noncomputable def divAt (M : Matrix (Fin n) (Fin n) K) (l : ℕ) : K :=
  if h : l = 0 then 1 else if h2 : l - 1 < n then M ⟨l - 1, h2⟩ ⟨l - 1, h2⟩ else 1

/-- The first step divides by `1`. -/
lemma divAt_zero (M : Matrix (Fin n) (Fin n) K) : divAt M 0 = 1 := by
  rw [divAt, dif_pos rfl]

/-- The step with new pivot index `l+1` divides by the diagonal entry `M l l`. -/
lemma divAt_succ (M : Matrix (Fin n) (Fin n) K) {l : ℕ} (hl : l < n) :
    divAt M (l + 1) = M ⟨l, hl⟩ ⟨l, hl⟩ := by
  have h : ¬ (l + 1 = 0) := by omega
  have h2 : (l + 1) - 1 < n := by omega
  rw [divAt, dif_neg h, dif_pos h2]
  have harg : (⟨(l + 1) - 1, h2⟩ : Fin n) = ⟨l, hl⟩ := by
    apply Fin.ext
    show (l + 1) - 1 = l
    exact Nat.add_sub_cancel l 1
  rw [harg]

/-- **One fraction-free (Bareiss) step**, with pivot index `l`.  The entries with
`l < i` and `l < j` are replaced by `(M l l * M i j - M i l * M l j) / divAt P l`;
every other entry is copied from `M` (its value is irrelevant for the theorem below,
which only looks at the region `i, j > l`).  For `l ≥ n` the step is a no-op. -/
noncomputable def stepMat (M P : Matrix (Fin n) (Fin n) K) (l : ℕ) :
    Matrix (Fin n) (Fin n) K :=
  fun i j =>
    if h : l < n then
      if hl : l < i.val ∧ l < j.val then
        (M ⟨l, h⟩ ⟨l, h⟩ * M i j - M i ⟨l, h⟩ * M ⟨l, h⟩ j) / divAt P l
      else M i j
    else M i j

/-- The value of `stepMat` on an entry it actually updates. -/
lemma stepMat_apply_of (M P : Matrix (Fin n) (Fin n) K) {l : ℕ} (hn : l < n)
    {i j : Fin n} (hi : l < i.val) (hj : l < j.val) :
    stepMat M P l i j
      = (M ⟨l, hn⟩ ⟨l, hn⟩ * M i j - M i ⟨l, hn⟩ * M ⟨l, hn⟩ j) / divAt P l := by
  unfold stepMat
  rw [dif_pos hn, dif_pos (show l < i.val ∧ l < j.val from ⟨hi, hj⟩)]

/-- The value of `stepMat` on an entry it leaves alone. -/
lemma stepMat_apply_of_not (M P : Matrix (Fin n) (Fin n) K) {l : ℕ} {i j : Fin n}
    (hi : ¬ l < i.val) : stepMat M P l i j = M i j := by
  unfold stepMat
  by_cases hn : l < n
  · rw [dif_pos hn, dif_neg (show ¬ (l < i.val ∧ l < j.val) from fun h => hi h.1)]
  · rw [dif_neg hn]

/-- The state of the recursion at stage `k`: the tableau `T k` paired with `T (k-1)`,
where `T (-1) := A` (its diagonal entry is consulted only conceptually at `k = 0`, where
the divisor is `1` anyway). -/
noncomputable def tabPair (A : Matrix (Fin n) (Fin n) K) :
    ℕ → Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K
  | 0 => (A, A)
  | k + 1 => (stepMat (tabPair A k).1 (tabPair A k).2 k, (tabPair A k).1)

/-- **The Bareiss tableau of `A`**, by course-of-values recursion: `tab A 0 = A`, and
`tab A (k+1)` is the outcome of the step with pivot index `k` applied to `tab A k`,
divided by `tab A (k-1) (k-1) (k-1)` (and by `1` for `k = 0`). -/
noncomputable def tab (A : Matrix (Fin n) (Fin n) K) (k : ℕ) : Matrix (Fin n) (Fin n) K :=
  (tabPair A k).1

/-- The tableau starts at `A`. -/
lemma tab_zero (A : Matrix (Fin n) (Fin n) K) : tab A 0 = A := rfl

/-- The first step, in definitional form. -/
lemma tab_one (A : Matrix (Fin n) (Fin n) K) : tab A 1 = stepMat (tab A 0) A 0 := rfl

/-- The general step, in definitional form. -/
lemma tab_succ_succ (A : Matrix (Fin n) (Fin n) K) (l : ℕ) :
    tab A (l + 2) = stepMat (tab A (l + 1)) (tab A l) (l + 1) := rfl

/-! ## 2.  The three hypotheses of `tableau_eq_bord` -/

/-- **Step `0`** of the recurrence: the entries with `0 < i` and `0 < j` are
`T 0 0 0 * T 0 i j - T 0 i 0 * T 0 0 j` (divisor `1`). -/
theorem tab_step0 (A : Matrix (Fin n) (Fin n) K) (i j : Fin n)
    (hi : 0 < i.val) (hj : 0 < j.val) :
    tab A 1 i j = tab A 0 0 0 * tab A 0 i j - tab A 0 i 0 * tab A 0 0 j := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h0 : (⟨0, hn⟩ : Fin n) = 0 := Fin.ext rfl
  rw [tab_one A, stepMat_apply_of (M := tab A 0) (P := A) hn hi hj, divAt_zero, div_one, h0]

/-- **Step `l+1`** of the recurrence: for `l + 2 ≤ n` and `i, j > l+1`, the entry is
`(T (l+1) (l+1) (l+1) * T (l+1) i j - T (l+1) i (l+1) * T (l+1) (l+1) j) / T l l l`. -/
theorem tab_step (A : Matrix (Fin n) (Fin n) K) :
    ∀ (l : ℕ), ∀ (hl : l + 2 ≤ n) (i j : Fin n), l + 1 < i.val → l + 1 < j.val →
      tab A (l + 2) i j
        = (tab A (l + 1) ⟨l + 1, by omega⟩ ⟨l + 1, by omega⟩ * tab A (l + 1) i j
            - tab A (l + 1) i ⟨l + 1, by omega⟩ * tab A (l + 1) ⟨l + 1, by omega⟩ j)
          / tab A l ⟨l, by omega⟩ ⟨l, by omega⟩ := by
  intro l hl i j hi hj
  have h1 : l + 1 < n := by omega
  have h0 : l < n := by omega
  rw [tab_succ_succ A l, stepMat_apply_of (M := tab A (l + 1)) (P := tab A l) h1 hi hj,
    divAt_succ (tab A l) h0]

/-! ## 3.  The assembled theorems -/

/-- **The tableau is made of bordered minors**: for `k ≤ i` and `k ≤ j`,
`tab A k i j = bord A k i j`, provided the leading principal minors
`Δ 0, …, Δ (n-1)` are nonzero. -/
theorem tab_eq_bord (A : Matrix (Fin n) (Fin n) K)
    (hΔ : ∀ m, m < n → delta A m ≠ 0) (k : ℕ) (i j : Fin n)
    (hi : k ≤ i.val) (hj : k ≤ j.val) :
    tab A k i j = bord A k i j :=
  tableau_eq_bord A (tab A) (tab_zero A) (tab_step0 A) (tab_step A) hΔ k i j hi hj

/-- **The pivots are the leading principal minors**: `tab A k k k = Δ (k+1)`. -/
theorem tab_pivot (A : Matrix (Fin n) (Fin n) K)
    (hΔ : ∀ m, m < n → delta A m ≠ 0) (k : ℕ) (hk : k < n) :
    tab A k ⟨k, hk⟩ ⟨k, hk⟩ = delta A (k + 1) :=
  pivot_eq_delta A (tab A) (tab_zero A) (tab_step0 A) (tab_step A) hΔ k hk

/-- **The last entry is the determinant**: `tab A (n-1) (n-1) (n-1) = det A`. -/
theorem tab_last (A : Matrix (Fin n) (Fin n) K)
    (hΔ : ∀ m, m < n → delta A m ≠ 0) (hn : 1 ≤ n) :
    tab A (n - 1) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = A.det :=
  last_entry_eq_det A (tab A) (tab_zero A) (tab_step0 A) (tab_step A) hΔ hn

/-! ## 4.  The bit-length corollary -/

/-- The cast of an integer matrix to a rational one. -/
noncomputable def intToRat {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℚ :=
  A.map fun x => (x : ℚ)

/-- The bordered minor of the cast is the cast of the integer bordered minor. -/
theorem bord_intToRat (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (i j : Fin n) :
    bord (intToRat A) k i j
      = ((bMinor A (snocIdx (prefMap k) i) (snocIdx (prefMap k) j) : ℤ) : ℚ) := by
  have hsub : (intToRat A).submatrix (snocIdx (prefMap k) i) (snocIdx (prefMap k) j)
      = (A.submatrix (snocIdx (prefMap k) i) (snocIdx (prefMap k) j)).map
          (fun x => (x : ℚ)) := by
    ext a b
    simp [intToRat, Matrix.submatrix_apply, Matrix.map_apply]
  rw [bord, bMinor, hsub, ← Int.cast_det]

/-- **Every tableau entry is a (bordered) minor, integrally.**  For an integer matrix `A`
with nonzero leading principal minors, every entry of the rational tableau of the cast
`intToRat A` is the cast of an integer bordered minor of `A`: the fraction-free tableau is
integral, and its entries are minors. -/
theorem tab_entry_eq_bMinor (A : Matrix (Fin n) (Fin n) ℤ)
    (hΔ : ∀ m, m < n → delta (intToRat A) m ≠ 0)
    (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    tab (intToRat A) k i j
      = ((bMinor A (snocIdx (prefMap k) i) (snocIdx (prefMap k) j) : ℤ) : ℚ) := by
  rw [tab_eq_bord (intToRat A) hΔ k i j hi hj]
  exact bord_intToRat A k i j

/-- **Bit length of the minor that is the tableau entry.**  If every entry of the integer
matrix `A` satisfies `|A i j| < 2^b`, then the bordered minor that the tableau entry
`tab A k i j` equals has at most `n * b + bitLenInt (n!)` bits. -/
theorem tab_entry_bitLen (A : Matrix (Fin n) (Fin n) ℤ)
    {b : ℕ} (hM : ∀ i j, |A i j| < (2 : ℤ) ^ b)
    (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) :
    bitLenInt (bMinor A (snocIdx (prefMap k) i) (snocIdx (prefMap k) j))
      ≤ n * b + bitLenInt (n.factorial) :=
  bitLenInt_bMinor_le_factorial A _ _ hM (by have := i.isLt; omega)

/-- **Closed form** of the previous bound: `n * b + n * n.size + 1` bits. -/
theorem tab_entry_bitLen_size (A : Matrix (Fin n) (Fin n) ℤ)
    {b : ℕ} (hM : ∀ i j, |A i j| < (2 : ℤ) ^ b)
    (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) :
    bitLenInt (bMinor A (snocIdx (prefMap k) i) (snocIdx (prefMap k) j))
      ≤ n * b + n * n.size + 1 :=
  bitLenInt_bMinor_le_size A _ _ hM (by have := i.isLt; omega)

/-- **The bound for the tableau entry itself.**  With nonzero leading principal minors and
`|A i j| < 2^b`, the numerator of the rational tableau entry `tab (intToRat A) k i j` has at
most `n * b + bitLenInt (n!)` bits. -/
theorem tab_entry_num_bitLen (A : Matrix (Fin n) (Fin n) ℤ)
    (hΔ : ∀ m, m < n → delta (intToRat A) m ≠ 0)
    {b : ℕ} (hM : ∀ i j, |A i j| < (2 : ℤ) ^ b)
    (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    bitLenInt (tab (intToRat A) k i j).num ≤ n * b + bitLenInt (n.factorial) := by
  rw [tab_entry_eq_bMinor A hΔ k i j hi hj, Rat.num_intCast]
  exact tab_entry_bitLen A hM k i j hi

/-- **The last entry is the determinant, with its bit length.**  For `1 ≤ n`, the numerator
of the last tableau entry of the cast is `det A`, so it has at most
`n * b + bitLenInt (n!)` bits. -/
theorem tab_last_num_bitLen (A : Matrix (Fin n) (Fin n) ℤ)
    (hΔ : ∀ m, m < n → delta (intToRat A) m ≠ 0)
    {b : ℕ} (hM : ∀ i j, |A i j| < (2 : ℤ) ^ b) (hn : 1 ≤ n) :
    bitLenInt (tab (intToRat A) (n - 1) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩).num
      ≤ n * b + bitLenInt (n.factorial) := by
  have hq : tab (intToRat A) (n - 1) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩
      = ((A.det : ℤ) : ℚ) := by
    rw [tab_last (intToRat A) hΔ hn]
    simp only [intToRat, ← Int.cast_det]
  rw [hq, Rat.num_intCast]
  exact bitLenInt_det_le A hM

/-- **The bound in terms of `bitLenMat`**, for the cleared integer matrix `A.num` of a
rational input `A`. -/
theorem tab_entry_bitLen_bitLenMat (A : Matrix (Fin n) (Fin n) ℚ)
    {b : ℕ} (hb : bitLenMat A ≤ b) (k : ℕ) (i j : Fin n) (hi : k ≤ i.val) :
    bitLenInt (bMinor A.num (snocIdx (prefMap k) i) (snocIdx (prefMap k) j))
      ≤ n * b + bitLenInt (n.factorial) := by
  refine tab_entry_bitLen A.num (fun i j => ?_) k i j hi
  have h2 : (2 : ℤ) ^ bitLenMat A ≤ (2 : ℤ) ^ b :=
    pow_le_pow_right₀ (by norm_num) hb
  exact lt_of_lt_of_le (mat_abs_num_lt_two_pow_bitLenMat A i j) h2

/-- **The bound in terms of `inputLen`**, for the cleared integer matrix `A.num`. -/
theorem tab_entry_bitLen_inputLen (A : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) (i j : Fin n)
    (hi : k ≤ i.val) :
    bitLenInt (bMinor A.num (snocIdx (prefMap k) i) (snocIdx (prefMap k) j))
      ≤ n * inputLen A + bitLenInt (n.factorial) := by
  refine tab_entry_bitLen_bitLenMat A ?_ k i j hi
  exact bitLenMat_le_inputLen A (by have := NeZero.ne n; omega)

end BareissAssemble
end Q1Paper.PaperI
