/-
Q1Paper/PaperI/BareissTableau.lean

**The Bareiss tableau consists of bordered minors** — the Desnanot–Jacobi induction.

`Q1Paper/PaperI/BareissBase.lean` proves the `k = 0, 1` instances only, and
`Q1Paper/PaperI/DesnanotJacobi.lean` proves the bordered Desnanot–Jacobi identity
(`dj_block`, `desnanot_jacobi_prefix`) unconditionally.  This file runs the induction that
turns that identity into the statement "every fraction-free (Bareiss) tableau entry is a
bordered minor of the original matrix".

Setting.  `A : Matrix (Fin n) (Fin n) K` over a field `K`, `n ≥ 1`.  Let
`Δ k = det A({0,…,k-1},{0,…,k-1})` (`delta`) be the leading principal minor of order `k`,
and let `bord A k i j = det A({0,…,k-1} ∪ {i}, {0,…,k-1} ∪ {j})` (`bord`) be the bordered
minor of order `k+1`, both index sets taken in increasing order.  (Both are defined by
`prefMap` / `snocIdx` below; `delta` and `bord` are total functions, with junk values for
`k > n` that are never used.)

Main results:

* `bord_dj` — the bordered Desnanot–Jacobi identity in the form the Bareiss step needs:
    `bord A (k+1) i j * Δ k = Δ (k+1) * bord A k i j - bord A k k j * bord A k i k`
  for `k < n` and **arbitrary** `i j : Fin n` (no hypothesis at all);

* `bord_self` — the pivot: `bord A k k k = Δ (k+1)`;

* `tableau_eq_bord` — **the induction**.  For a family `T : ℕ → Matrix (Fin n) (Fin n) K`
  satisfying the Bareiss recurrence
    `T 0 = A`,
    `T 1 i j = T 0 0 0 * T 0 i j - T 0 i 0 * T 0 0 j`  (step `0`, divisor `1`),
    `T (l+2) i j = (T (l+1) (l+1) (l+1) * T (l+1) i j
                    - T (l+1) i (l+1) * T (l+1) (l+1) j) / T l l l`  (step `l+1`),
  and with `Δ 0, …, Δ (n-1)` all nonzero, every entry of the tableau is the
  corresponding bordered minor:
    `T k i j = bord A k i j`  for `k ≤ i` and `k ≤ j`;

* `pivot_eq_delta` — the pivots are the leading principal minors: `T k k k = Δ (k+1)`;

* `last_entry_eq_det` — in particular `T (n-1) (n-1) (n-1) = det A`.

Proof route.  Induction on `k` (strong induction, since the step needs the claim at `k-1`
to identify the previous pivot with `Δ k`).  The step applies `bord_dj` at level `k` to the
two extra indices `(i, k)` and `(j, k)`:
    `bord A (k+1) i j * Δ k = Δ (k+1) * bord A k i j - bord A k k j * bord A k i k`,
uses the induction hypothesis to replace `Δ (k+1)`, `bord A k i j`, `bord A k k j`,
`bord A k i k` by `T k k k`, `T k i j`, `T k k j`, `T k i k`, and the induction hypothesis at
`k-1` (plus `bord_self`) to identify the divisor `T (k-1) (k-1) (k-1)` with `Δ k`.  The
numerator is then `bord A (k+1) i j * Δ k`, and division by `Δ k ≠ 0` finishes.

No `sorry`, no `admit`, no new axioms.  Check with
  `lake env lean Q1Paper/PaperI/BareissTableau.lean`
-/

import Q1Paper.PaperI.DesnanotJacobi

open Matrix

namespace Q1Paper.PaperI
namespace BareissTableau

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

/-! ## 1.  Index maps: the prefix embedding and "append one index" -/

/-- `prefMap k : Fin k → Fin n` is the increasing embedding of `{0, …, k-1}` into
`{0, …, n-1}`.  It is junk (`0`) outside the range `k ≤ n`, which is never used below. -/
def prefMap (k : ℕ) : Fin k → Fin n :=
  fun t => if h : t.val < n then ⟨t.val, h⟩ else 0

/-- The value of `prefMap` on an index in range. -/
lemma prefMap_apply {k : ℕ} (t : Fin k) (h : t.val < n) :
    prefMap (n := n) k t = ⟨t.val, h⟩ := by
  unfold prefMap
  rw [dif_pos h]

/-- `snocIdx f a : Fin (k+1) → Fin n` agrees with `f` on `{0, …, k-1}` and equals `a` at `k`. -/
def snocIdx {k : ℕ} (f : Fin k → Fin n) (a : Fin n) : Fin (k + 1) → Fin n :=
  fun t => if h : t.val < k then f ⟨t.val, h⟩ else a

lemma snocIdx_lt {k : ℕ} (f : Fin k → Fin n) (a : Fin n) (t : Fin (k + 1))
    (h : t.val < k) : snocIdx f a t = f ⟨t.val, h⟩ := by
  unfold snocIdx
  rw [dif_pos h]

lemma snocIdx_ge {k : ℕ} (f : Fin k → Fin n) (a : Fin n) (t : Fin (k + 1))
    (h : ¬ t.val < k) : snocIdx f a t = a := by
  unfold snocIdx
  rw [dif_neg h]

/-- Appending the index `k` to the prefix embedding of length `k` gives the prefix
embedding of length `k+1`. -/
lemma snocIdx_prefMap (k : ℕ) (hk : k < n) :
    snocIdx (prefMap k) (⟨k, hk⟩ : Fin n) = prefMap (n := n) (k + 1) := by
  funext t
  by_cases h : t.val < k
  · rw [snocIdx_lt _ _ _ h, prefMap_apply _ (by omega), prefMap_apply _ (by omega)]
  · rw [snocIdx_ge _ _ _ h, prefMap_apply _ (by omega)]
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

/-! ## 2.  The leading principal minor `Δ k` and the bordered minor -/

/-- The **leading principal minor of order `k`**: `Δ k = det A({0,…,k-1},{0,…,k-1})`.
(`Δ 0 = 1`, `Δ n = det A`.) -/
noncomputable def delta (A : Matrix (Fin n) (Fin n) K) (k : ℕ) : K :=
  (A.submatrix (prefMap k) (prefMap k)).det

/-- The **bordered minor of order `k+1`**: rows `{0,…,k-1} ∪ {i}`, columns
`{0,…,k-1} ∪ {j}`, both index sets in increasing order.  For `k = 0` this is `A i j`. -/
noncomputable def bord (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (i j : Fin n) : K :=
  (A.submatrix (snocIdx (prefMap k) i) (snocIdx (prefMap k) j)).det

/-- `Δ 0 = 1`. -/
lemma delta_zero (A : Matrix (Fin n) (Fin n) K) : delta A 0 = 1 := by
  have h : A.submatrix (prefMap 0) (prefMap 0) = (1 : Matrix (Fin 0) (Fin 0) K) :=
    Subsingleton.elim _ _
  rw [delta, h, Matrix.det_one]

/-- `Δ n = det A`. -/
lemma delta_full (A : Matrix (Fin n) (Fin n) K) : delta A n = A.det := by
  have h : prefMap (n := n) n = id := by
    funext t
    exact prefMap_apply t t.isLt
  rw [delta, h, Matrix.submatrix_id_id]

/-- The order-`1` bordered minor is the entry itself. -/
lemma bord_zero (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) : bord A 0 i j = A i j := by
  have hi : snocIdx (prefMap 0) i = (fun _ : Fin 1 => i) := by
    funext t
    exact snocIdx_ge _ _ _ (by omega)
  have hj : snocIdx (prefMap 0) j = (fun _ : Fin 1 => j) := by
    funext t
    exact snocIdx_ge _ _ _ (by omega)
  rw [bord, hi, hj]
  have hdet := Matrix.det_fin_one (A.submatrix (fun _ : Fin 1 => i) (fun _ : Fin 1 => j))
  rw [hdet]
  rfl

/-- **The pivot is the next leading principal minor**: `bord A k k k = Δ (k+1)`. -/
lemma bord_self (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : k < n) :
    bord A k (⟨k, hk⟩ : Fin n) (⟨k, hk⟩ : Fin n) = delta A (k + 1) := by
  rw [bord, delta, snocIdx_prefMap k hk]

/-! ## 3.  Transport of `Fin k ⊕ Fin m` determinants to the `Fin (k+m)` shape -/

/-- `Sum.elim f (fun _ => a)` composed with `finSumFinEquiv.symm` is `snocIdx f a`. -/
lemma elim_comp_symm_one {k : ℕ} (f : Fin k → Fin n) (a : Fin n) (t : Fin (k + 1)) :
    Sum.elim f (fun _ : Fin 1 => a) (finSumFinEquiv.symm t) = snocIdx f a t := by
  by_cases h : t.val < k
  · have hc : finSumFinEquiv.symm t = (Sum.inl (⟨t.val, h⟩ : Fin k) : Fin k ⊕ Fin 1) := by
      rw [Equiv.symm_apply_eq]
      exact Fin.ext (by simp)
    rw [hc, snocIdx_lt _ _ _ h]
    rfl
  · have hk : t.val = k := by have := t.isLt; omega
    have hc : finSumFinEquiv.symm t = (Sum.inr (0 : Fin 1) : Fin k ⊕ Fin 1) := by
      rw [Equiv.symm_apply_eq]
      exact Fin.ext (by rw [hk]; simp)
    rw [hc, snocIdx_ge _ _ _ h]
    rfl

/-- The two-extra-indices version: `Sum.elim f (Fin.cases p q)` composed with
`finSumFinEquiv.symm` is `snocIdx (snocIdx f p) q`. -/
lemma elim_comp_symm_two {k : ℕ} (f : Fin k → Fin n) (p q : Fin n) (t : Fin (k + 2)) :
    Sum.elim f (Fin.cases p (fun _ : Fin 1 => q)) (finSumFinEquiv.symm t)
      = snocIdx (snocIdx f p) q t := by
  by_cases h : t.val < k
  · have h2 : t.val < k + 1 := by omega
    have hc : finSumFinEquiv.symm t
        = (Sum.inl (⟨t.val, h⟩ : Fin k) : Fin k ⊕ Fin 2) := by
      rw [Equiv.symm_apply_eq]
      exact Fin.ext (by simp)
    rw [hc, snocIdx_lt (f := snocIdx f p) (a := q) (k := k + 1) (t := t) h2,
      snocIdx_lt (f := f) (a := p) (k := k) (t := ⟨t.val, h2⟩) h]
    rfl
  · rcases (by omega : t.val = k ∨ t.val = k + 1) with hk | hk
    · have h2 : t.val < k + 1 := by omega
      have hc : finSumFinEquiv.symm t = (Sum.inr (0 : Fin 2) : Fin k ⊕ Fin 2) := by
        rw [Equiv.symm_apply_eq]
        exact Fin.ext (by rw [hk]; simp)
      rw [hc, snocIdx_lt (f := snocIdx f p) (a := q) (k := k + 1) (t := t) h2,
        snocIdx_ge (f := f) (a := p) (k := k) (t := ⟨t.val, h2⟩) (by omega)]
      show Fin.cases p (fun _ : Fin 1 => q) (0 : Fin 2) = p
      exact Fin.cases_zero
    · have hc : finSumFinEquiv.symm t = (Sum.inr (1 : Fin 2) : Fin k ⊕ Fin 2) := by
        rw [Equiv.symm_apply_eq]
        exact Fin.ext (by rw [hk]; simp)
      rw [hc, snocIdx_ge (f := snocIdx f p) (a := q) (k := k + 1) (t := t) (by omega)]
      show Fin.cases p (fun _ : Fin 1 => q) (1 : Fin 2) = q
      rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, Fin.cases_succ]

/-- A bordered minor written with `Fin k ⊕ Fin 1` indices is the `bord` minor. -/
lemma det_elim_one (A : Matrix (Fin n) (Fin n) K) {k : ℕ} (p q : Fin n) :
    (A.submatrix (Sum.elim (prefMap k) (fun _ : Fin 1 => p))
        (Sum.elim (prefMap k) (fun _ : Fin 1 => q))).det = bord A k p q := by
  have hkey := det_submatrix_equiv_self
    (finSumFinEquiv.symm : Fin (k + 1) ≃ Fin k ⊕ Fin 1)
    (A.submatrix (Sum.elim (prefMap k) (fun _ : Fin 1 => p))
      (Sum.elim (prefMap k) (fun _ : Fin 1 => q)))
  rw [← hkey, bord]
  congr 1
  ext x y
  simp only [Matrix.submatrix_apply]
  rw [elim_comp_symm_one (f := prefMap k) (a := p) x,
    elim_comp_symm_one (f := prefMap k) (a := q) y]

/-- A bordered minor written with `Fin k ⊕ Fin 2` indices (two extra indices `k` and `p`)
is the `bord` minor. -/
lemma det_elim_two (A : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k < n) (p q : Fin n) :
    (A.submatrix (Sum.elim (prefMap k) (Fin.cases (⟨k, hk⟩ : Fin n) (fun _ : Fin 1 => p)))
        (Sum.elim (prefMap k) (Fin.cases (⟨k, hk⟩ : Fin n) (fun _ : Fin 1 => q)))).det
      = bord A (k + 1) p q := by
  have hkey := det_submatrix_equiv_self
    (finSumFinEquiv.symm : Fin (k + 2) ≃ Fin k ⊕ Fin 2)
    (A.submatrix (Sum.elim (prefMap k) (Fin.cases (⟨k, hk⟩ : Fin n) (fun _ : Fin 1 => p)))
      (Sum.elim (prefMap k) (Fin.cases (⟨k, hk⟩ : Fin n) (fun _ : Fin 1 => q))))
  rw [← hkey, bord]
  congr 1
  ext x y
  simp only [Matrix.submatrix_apply]
  rw [elim_comp_symm_two (f := prefMap k) (p := (⟨k, hk⟩ : Fin n)) (q := p) x,
    elim_comp_symm_two (f := prefMap k) (p := (⟨k, hk⟩ : Fin n)) (q := q) y,
    snocIdx_prefMap k hk]

/-- `bBorder` of the prefix blocks is the `bord` minor. -/
lemma bBorder_eq_bord (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (rowAt colAt : Fin 2 → Fin n)
    (u v : Fin 2) :
    bBorder k (A.submatrix (prefMap k) (prefMap k)) (A.submatrix (prefMap k) colAt)
      (A.submatrix rowAt (prefMap k)) (A.submatrix rowAt colAt) u v
      = bord A k (rowAt u) (colAt v) := by
  rw [bBorder, bord]
  have hblk : fromBlocks (A.submatrix (prefMap k) (prefMap k))
      ((A.submatrix (prefMap k) colAt).submatrix id (fun _ : Fin 1 => v))
      ((A.submatrix rowAt (prefMap k)).submatrix (fun _ : Fin 1 => u) id)
      ((A.submatrix rowAt colAt).submatrix (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))
      = A.submatrix (Sum.elim (prefMap k) (fun _ : Fin 1 => rowAt u))
          (Sum.elim (prefMap k) (fun _ : Fin 1 => colAt v)) := by
    ext x y
    rcases x with a | a <;> rcases y with b | b <;> simp [Matrix.submatrix_apply]
  rw [hblk]
  exact det_elim_one A (rowAt u) (colAt v)

/-- **Bordered Desnanot–Jacobi in the form of the Bareiss step.**  For `k < n` and
arbitrary `i j : Fin n`:

`bord A (k+1) i j * Δ k = Δ (k+1) * bord A k i j - bord A k k j * bord A k i k`.

This is `dj_block` at the `k`-partition of `A`, with the two extra indices `k` and the
target indices `i`, `j`. -/
theorem bord_dj (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : k < n) (i j : Fin n) :
    bord A (k + 1) i j * delta A k
      = delta A (k + 1) * bord A k i j
        - bord A k (⟨k, hk⟩ : Fin n) j * bord A k i (⟨k, hk⟩ : Fin n) := by
  set rowAt : Fin 2 → Fin n := Fin.cases (⟨k, hk⟩ : Fin n) (fun _ : Fin 1 => i) with hrow
  set colAt : Fin 2 → Fin n := Fin.cases (⟨k, hk⟩ : Fin n) (fun _ : Fin 1 => j) with hcol
  have hblk : fromBlocks (A.submatrix (prefMap k) (prefMap k)) (A.submatrix (prefMap k) colAt)
      (A.submatrix rowAt (prefMap k)) (A.submatrix rowAt colAt)
      = A.submatrix (Sum.elim (prefMap k) rowAt) (Sum.elim (prefMap k) colAt) := by
    ext x y
    rcases x with a | a <;> rcases y with b | b <;> rfl
  have hL : (fromBlocks (A.submatrix (prefMap k) (prefMap k)) (A.submatrix (prefMap k) colAt)
      (A.submatrix rowAt (prefMap k)) (A.submatrix rowAt colAt)).det = bord A (k + 1) i j := by
    rw [hblk, hrow, hcol]
    exact det_elim_two A hk i j
  have h00 : rowAt 0 = (⟨k, hk⟩ : Fin n) := rfl
  have h10 : rowAt 1 = i := rfl
  have c00 : colAt 0 = (⟨k, hk⟩ : Fin n) := rfl
  have c10 : colAt 1 = j := rfl
  have key := dj_block k (A.submatrix (prefMap k) (prefMap k)) (A.submatrix (prefMap k) colAt)
    (A.submatrix rowAt (prefMap k)) (A.submatrix rowAt colAt)
  rw [hL, bBorder_eq_bord A k rowAt colAt 0 0, bBorder_eq_bord A k rowAt colAt 1 1,
    bBorder_eq_bord A k rowAt colAt 0 1, bBorder_eq_bord A k rowAt colAt 1 0] at key
  rw [h00, h10, c00, c10] at key
  rw [← bord_self A k hk]
  simpa [delta] using key

/-! ## 4.  The induction: every tableau entry is a bordered minor -/

/-- **The Bareiss tableau consists of bordered minors.**  Let `T` be the fraction-free
tableau, given by the recurrence

* `T 0 = A`;
* `T 1 i j = T 0 0 0 * T 0 i j - T 0 i 0 * T 0 0 j` (step `0`, divisor `1`);
* `T (l+2) i j = (T (l+1) (l+1) (l+1) * T (l+1) i j
                  - T (l+1) i (l+1) * T (l+1) (l+1) j) / T l l l` (step `l+1`),

each step being applied for `i, j >` the pivot index (entries with `i` or `j` at most the
pivot are left unchanged, which is irrelevant below since only indices `≥ k` are compared);

and assume that every leading principal minor `Δ 0, …, Δ (n-1)` is nonzero (`Δ 0 = 1` is
automatic and `Δ n = det A` is *not* required); then for every `k`,
every entry of the `k`-th tableau with `i, j ≥ k` is the bordered minor
`det A({0,…,k-1} ∪ {i}, {0,…,k-1} ∪ {j})`. -/
theorem tableau_eq_bord (A : Matrix (Fin n) (Fin n) K) (T : ℕ → Matrix (Fin n) (Fin n) K)
    (hT0 : T 0 = A)
    (hstep0 : ∀ (i j : Fin n), 0 < i.val → 0 < j.val →
        T 1 i j = T 0 0 0 * T 0 i j - T 0 i 0 * T 0 0 j)
    (hstep : ∀ (l : ℕ), ∀ (hl : l + 2 ≤ n) (i j : Fin n), l + 1 < i.val → l + 1 < j.val →
        T (l + 2) i j
          = (T (l + 1) ⟨l + 1, by omega⟩ ⟨l + 1, by omega⟩ * T (l + 1) i j
              - T (l + 1) i ⟨l + 1, by omega⟩ * T (l + 1) ⟨l + 1, by omega⟩ j)
            / T l ⟨l, by omega⟩ ⟨l, by omega⟩)
    (hΔ : ∀ (m : ℕ), m < n → delta A m ≠ 0) :
    ∀ (k : ℕ) (i j : Fin n), k ≤ i.val → k ≤ j.val → T k i j = bord A k i j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i j hi hj
    rcases k with _ | k
    · rw [hT0, bord_zero]
    rcases k with _ | k
    · -- target level `1` (step `0`, divisor `1`)
      rw [hstep0 i j (by omega) (by omega)]
      have h0n : 0 < n := by have := i.isLt; omega
      have hz : (⟨0, h0n⟩ : Fin n) = (0 : Fin n) := Fin.ext (by simp)
      have H0 : ∀ (i' j' : Fin n), T 0 i' j' = bord A 0 i' j' :=
        fun i' j' => ih 0 (by omega) i' j' (by omega) (by omega)
      have hnum : T 0 (0 : Fin n) (0 : Fin n) * T 0 i j - T 0 i (0 : Fin n) * T 0 (0 : Fin n) j
          = bord A 1 i j * delta A 0 := by
        rw [H0 (0 : Fin n) (0 : Fin n), H0 i j, H0 i (0 : Fin n), H0 (0 : Fin n) j]
        have hdj : bord A 1 i j * delta A 0
            = delta A 1 * bord A 0 i j
              - bord A 0 (0 : Fin n) j * bord A 0 i (0 : Fin n) := by
          have h := bord_dj A 0 h0n i j
          rw [hz] at h
          exact h
        rw [hdj, ← bord_self A 0 h0n, hz]
        ring
      rw [hnum, delta_zero, mul_one]
    · -- target level `k+2` (step `k+1`)
      have hk2 : k + 2 ≤ n := by have := i.isLt; omega
      have hkn : k < n := by omega
      have hk1 : k + 1 < n := by omega
      have IH : ∀ (l : ℕ), l < k + 2 → ∀ (i' j' : Fin n), l ≤ i'.val → l ≤ j'.val →
          T l i' j' = bord A l i' j' := fun l hl => ih l hl
      have hdiv : T k ⟨k, hkn⟩ ⟨k, hkn⟩ = delta A (k + 1) := by
        rw [IH k (by omega) ⟨k, hkn⟩ ⟨k, hkn⟩ le_rfl le_rfl, bord_self A k hkn]
      have hnum : T (k + 1) ⟨k + 1, hk1⟩ ⟨k + 1, hk1⟩ * T (k + 1) i j
            - T (k + 1) i ⟨k + 1, hk1⟩ * T (k + 1) ⟨k + 1, hk1⟩ j
          = bord A (k + 2) i j * delta A (k + 1) := by
        have hdj := bord_dj A (k + 1) hk1 i j
        rw [IH (k + 1) (by omega) ⟨k + 1, hk1⟩ ⟨k + 1, hk1⟩ le_rfl le_rfl,
          IH (k + 1) (by omega) i j (by omega) (by omega),
          IH (k + 1) (by omega) i ⟨k + 1, hk1⟩ (by omega) le_rfl,
          IH (k + 1) (by omega) ⟨k + 1, hk1⟩ j le_rfl (by omega)]
        rw [hdj, ← bord_self A (k + 1) hk1]
        ring
      have hrec : T (k + 2) i j
          = (T (k + 1) ⟨k + 1, hk1⟩ ⟨k + 1, hk1⟩ * T (k + 1) i j
              - T (k + 1) i ⟨k + 1, hk1⟩ * T (k + 1) ⟨k + 1, hk1⟩ j)
            / T k ⟨k, hkn⟩ ⟨k, hkn⟩ :=
        hstep k hk2 i j (by omega) (by omega)
      rw [hrec, hnum, hdiv, mul_div_cancel_right₀ _ (hΔ (k + 1) hk1)]

/-- **(2) The pivots are the leading principal minors**: `T k k k = Δ (k+1)`. -/
theorem pivot_eq_delta (A : Matrix (Fin n) (Fin n) K) (T : ℕ → Matrix (Fin n) (Fin n) K)
    (hT0 : T 0 = A)
    (hstep0 : ∀ (i j : Fin n), 0 < i.val → 0 < j.val →
        T 1 i j = T 0 0 0 * T 0 i j - T 0 i 0 * T 0 0 j)
    (hstep : ∀ (l : ℕ), ∀ (hl : l + 2 ≤ n) (i j : Fin n), l + 1 < i.val → l + 1 < j.val →
        T (l + 2) i j
          = (T (l + 1) ⟨l + 1, by omega⟩ ⟨l + 1, by omega⟩ * T (l + 1) i j
              - T (l + 1) i ⟨l + 1, by omega⟩ * T (l + 1) ⟨l + 1, by omega⟩ j)
            / T l ⟨l, by omega⟩ ⟨l, by omega⟩)
    (hΔ : ∀ (m : ℕ), m < n → delta A m ≠ 0) (k : ℕ) (hk : k < n) :
    T k (⟨k, hk⟩ : Fin n) (⟨k, hk⟩ : Fin n) = delta A (k + 1) := by
  rw [tableau_eq_bord A T hT0 hstep0 hstep hΔ k ⟨k, hk⟩ ⟨k, hk⟩ le_rfl le_rfl,
    bord_self A k hk]

/-- **(3) In particular the last entry is `det A`**: `T (n-1) (n-1) (n-1) = det A`. -/
theorem last_entry_eq_det (A : Matrix (Fin n) (Fin n) K) (T : ℕ → Matrix (Fin n) (Fin n) K)
    (hT0 : T 0 = A)
    (hstep0 : ∀ (i j : Fin n), 0 < i.val → 0 < j.val →
        T 1 i j = T 0 0 0 * T 0 i j - T 0 i 0 * T 0 0 j)
    (hstep : ∀ (l : ℕ), ∀ (hl : l + 2 ≤ n) (i j : Fin n), l + 1 < i.val → l + 1 < j.val →
        T (l + 2) i j
          = (T (l + 1) ⟨l + 1, by omega⟩ ⟨l + 1, by omega⟩ * T (l + 1) i j
              - T (l + 1) i ⟨l + 1, by omega⟩ * T (l + 1) ⟨l + 1, by omega⟩ j)
            / T l ⟨l, by omega⟩ ⟨l, by omega⟩)
    (hΔ : ∀ (m : ℕ), m < n → delta A m ≠ 0) (hn : 1 ≤ n) :
    T (n - 1) (⟨n - 1, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) = A.det := by
  have hk : n - 1 < n := by omega
  rw [pivot_eq_delta A T hT0 hstep0 hstep hΔ (n - 1) hk, Nat.sub_add_cancel hn]
  exact delta_full A

end BareissTableau
end Q1Paper.PaperI
