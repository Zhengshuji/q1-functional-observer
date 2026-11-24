
import Q1Paper.PaperI.BitLenAdd

/-!
Q1Paper/PaperI/InputLen.lean

Scratch module: the input bit-length bound `bitLenMat A ≤ inputLen A` for a
rational matrix, together with the two ingredients it needs.

Contents:
* `nat_size_prod_le` : `Nat.size` is subadditive over a nonempty finite product,
  `(s.prod f).size ≤ s.sum (fun x => (f x).size)`;
* `mat_den_size_le_sum` : for a matrix with at least one row and one column, the
  common denominator is bounded by the sum of the entry bit lengths,
  `A.den.size ≤ ∑ i, ∑ j, bitLenRat (A i j)`;
* `inputLen A` : the input size `m + n + ∑ i, ∑ j, bitLenRat (A i j)`;
* `mat_den_le_den_mul_prod_erase` (auxiliary) : the sharp form of
  `A.den ∣ ∏ i, ∏ j, (A i j).den`, namely the common denominator is at most the
  `(i,j)`-entry denominator times the product of the *remaining* entry
  denominators;
* `mat_bitLenInt_num_le_sum` (auxiliary) : every cleared entry is bounded by the
  sum of the entry bit lengths,
  `bitLenInt (A.num i j) ≤ ∑ p : Fin m × Fin n, bitLenRat (A p.1 p.2)`;
* `bitLenMat_le_inputLen` : `bitLenMat A ≤ inputLen A` for `0 < m + n`.

The three nonemptiness hypotheses are not cosmetic: `Nat.size 1 = 1`, so the
empty product (`s = ∅`, i.e. `Fin 0` rows or columns) breaks the sharp
inequalities by exactly one bit, and the empty matrix `m = n = 0` is a genuine
counterexample to `bitLenMat A ≤ inputLen A` (`1 ≤ 0`).

Imports `Q1Paper.PaperI.BitLenAdd`.  No `sorry`, no new axioms.
Check with `lake env lean Q1Paper/PaperI/InputLen.lean`.
-/


open Matrix

namespace Q1Paper.PaperI

/-! ## 1.  Bit size of a nonempty product -/

/-- `Nat.size` is subadditive over a nonempty finite product: the bit size of a
product is at most the sum of the bit sizes of the factors.

The nonemptiness hypothesis is needed: for `s = ∅` the left side is `1.size = 1`
while the right side is `0`. -/
theorem nat_size_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hs : s.Nonempty) :
    (s.prod f).size ≤ s.sum (fun x => (f x).size) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro hs
    exact absurd hs Finset.not_nonempty_empty
  · intro a t ha ih ht
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    rcases Finset.eq_empty_or_nonempty t with rfl | ht'
    · simp
    · exact (nat_size_mul_le (f a) (t.prod f)).trans (Nat.add_le_add_left (ih ht') _)

/-! ## 2.  The matrix denominator is bounded by the entry bit-length sum -/

/-- For a matrix with at least one row and one column, the common denominator has
at most as many bits as the sum of the input bit lengths of its entries. -/
theorem mat_den_size_le_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (hm : 0 < m) (hn : 0 < n) :
    A.den.size ≤ ∑ i, ∑ j, bitLenRat (A i j) := by
  classical
  have hu_m : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hu_n : ∀ i : Fin m, (Finset.univ : Finset (Fin n)).Nonempty :=
    fun _ => ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hPpos : 0 < ∏ i : Fin m, ∏ j : Fin n, (A i j).den :=
    Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ => Rat.den_pos (A i j)))
  -- the matrix denominator divides the product of the entry denominators
  have hdvd : A.den ∣ ∏ i : Fin m, ∏ j : Fin n, (A i j).den := by
    rw [Matrix.den_dvd_iff]
    intro i j
    exact (Finset.dvd_prod_of_mem (fun j => (A i j).den) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, (A i j).den) (Finset.mem_univ i))
  -- size of the double product, row by row and entry by entry
  have hprod : (∏ i : Fin m, ∏ j : Fin n, (A i j).den).size
      ≤ ∑ i : Fin m, ((∏ j : Fin n, (A i j).den)).size :=
    nat_size_prod_le _ (fun i => ∏ j : Fin n, (A i j).den) hu_m
  have hinner : ∑ i : Fin m, ((∏ j : Fin n, (A i j).den)).size
      ≤ ∑ i : Fin m, ∑ j : Fin n, ((A i j).den).size :=
    Finset.sum_le_sum (fun i _ =>
      nat_size_prod_le _ (fun j => (A i j).den) (hu_n i))
  have hentry : ∑ i : Fin m, ∑ j : Fin n, ((A i j).den).size
      ≤ ∑ i : Fin m, ∑ j : Fin n, bitLenRat (A i j) :=
    Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_sum (fun j _ => nat_size_den_le_bitLenRat (A i j)))
  exact ((Nat.size_le_size (Nat.le_of_dvd hPpos hdvd)).trans hprod).trans
    (hinner.trans hentry)

/-! ## 3.  The input length -/

/-- Input size of a rational matrix: the matrix shape plus the sum of the bit
lengths of the entries. -/
def inputLen {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  m + n + ∑ i, ∑ j, bitLenRat (A i j)

/-! ## 4.  Every cleared entry is bounded by the entry bit-length sum -/

/-- Sharp form of the divisibility `A.den ∣ ∏ i, ∏ j, (A i j).den`: the common
denominator is at most the `(i,j)`-entry denominator times the product of the
entry denominators of the remaining positions.

This refinement is what keeps `A.den.size` out of the estimate of `A.num i j`:
the leading factor `(A i j).den` is exactly the one cancelled against the
denominator of the entry, so only the *other* entry denominators have to be paid
for.  The cruder bound `A.den ≤ ∏ i, ∏ j, (A i j).den` would charge the `(i,j)`
denominator twice, which is not enough for e.g. `!![1 / 2 ^ 100, 0; 0, 0]`. -/
theorem mat_den_le_den_mul_prod_erase {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) :
    A.den ≤ (A i j).den * ∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den := by
  classical
  have hpos : 0 < ∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den :=
    Finset.prod_pos (fun q _ => Rat.den_pos _)
  have hdvd : A.den ∣ (A i j).den * ∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den := by
    rw [Finset.mul_prod_erase (Finset.univ : Finset (Fin m × Fin n))
      (fun q : Fin m × Fin n => (A q.1 q.2).den) (Finset.mem_univ (i, j))]
    rw [Matrix.den_dvd_iff]
    intro a b
    exact Finset.dvd_prod_of_mem (fun q : Fin m × Fin n => (A q.1 q.2).den)
      (Finset.mem_univ (a, b))
  exact Nat.le_of_dvd (Nat.mul_pos (Rat.den_pos _) hpos) hdvd

/-- Every entry of the cleared matrix is bounded by the sum of the entry bit
lengths of the whole matrix. -/
theorem mat_bitLenInt_num_le_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) :
    bitLenInt (A.num i j) ≤ ∑ p : Fin m × Fin n, bitLenRat (A p.1 p.2) := by
  classical
  -- cleared numerator identity, in `Nat` form
  have hnat : (A.num i j).natAbs * (A i j).den = A.den * (A i j).num.natAbs := by
    have h := congr_arg Int.natAbs (mat_num_mul_den_eq A i j)
    simpa [Int.natAbs_mul] using h
  -- the matrix denominator does not need the `(i,j)`-entry denominator twice
  have hDP : A.den ≤ (A i j).den * ∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den :=
    mat_den_le_den_mul_prod_erase A i j
  -- cancel the entry denominator
  have hcancel : (A.num i j).natAbs
      ≤ (∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den) * (A i j).num.natAbs := by
    refine Nat.le_of_mul_le_mul_right ?_ (Rat.den_pos (A i j))
    calc (A.num i j).natAbs * (A i j).den = A.den * (A i j).num.natAbs := hnat
      _ ≤ ((A i j).den * ∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den)
            * (A i j).num.natAbs := Nat.mul_le_mul_right _ hDP
      _ = ((∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den) * (A i j).num.natAbs)
            * (A i j).den := by ring
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin m × Fin n))
    (fun p : Fin m × Fin n => bitLenRat (A p.1 p.2)) (Finset.mem_univ (i, j))
  by_cases hne : (Finset.univ.erase (i, j) : Finset (Fin m × Fin n)).Nonempty
  · -- there are other entries: their denominators pay for the matrix denominator
    have hprod : (∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den).size
        ≤ ∑ q ∈ (Finset.univ.erase (i, j)), bitLenRat (A q.1 q.2) := by
      refine (nat_size_prod_le _ (fun q : Fin m × Fin n => (A q.1 q.2).den) hne).trans ?_
      exact Finset.sum_le_sum (fun q _ => nat_size_den_le_bitLenRat (A q.1 q.2))
    have hsize : (A.num i j).natAbs.size
        ≤ (∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den).size
          + (A i j).num.natAbs.size := by
      rw [Nat.size_le]
      calc (A.num i j).natAbs
          ≤ (∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den) * (A i j).num.natAbs := hcancel
        _ < 2 ^ (∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den).size
              * 2 ^ (A i j).num.natAbs.size :=
            Nat.mul_lt_mul_of_le_of_lt (le_of_lt (Nat.lt_size_self _))
              (Nat.lt_size_self _) (by positivity)
        _ = 2 ^ ((∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den).size
              + (A i j).num.natAbs.size) := (Nat.pow_add _ _ _).symm
    have hnum : (A i j).num.natAbs.size ≤ bitLenRat (A i j) :=
      bitLenInt_num_le_bitLenRat (A i j)
    calc bitLenInt (A.num i j) = (A.num i j).natAbs.size := rfl
      _ ≤ (∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den).size
            + (A i j).num.natAbs.size := hsize
      _ ≤ (∑ q ∈ (Finset.univ.erase (i, j)), bitLenRat (A q.1 q.2)) + bitLenRat (A i j) :=
          Nat.add_le_add hprod hnum
      _ = ∑ p : Fin m × Fin n, bitLenRat (A p.1 p.2) := hsum
  · -- there are no other entries (a `1 × 1` matrix): the entry denominator alone
    -- already cancels the matrix denominator
    have hemp : (Finset.univ.erase (i, j) : Finset (Fin m × Fin n)) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hprod1 : (∏ q ∈ (Finset.univ.erase (i, j)), (A q.1 q.2).den) = 1 := by
      rw [hemp]
      simp
    have hle : (A.num i j).natAbs ≤ (A i j).num.natAbs := by
      have h := hcancel
      rw [hprod1] at h
      simpa using h
    have hsize : (A.num i j).natAbs.size ≤ bitLenRat (A i j) :=
      (Nat.size_le_size hle).trans (bitLenInt_num_le_bitLenRat (A i j))
    have hsum0 : (∑ q ∈ (Finset.univ.erase (i, j)), bitLenRat (A q.1 q.2)) = 0 := by
      rw [hemp]
      simp
    have hS : (∑ p : Fin m × Fin n, bitLenRat (A p.1 p.2)) = bitLenRat (A i j) := by
      rw [← hsum, hsum0]
      simp
    calc bitLenInt (A.num i j) = (A.num i j).natAbs.size := rfl
      _ ≤ bitLenRat (A i j) := hsize
      _ = ∑ p : Fin m × Fin n, bitLenRat (A p.1 p.2) := hS.symm

/-! ## 5.  The matrix bit length is bounded by the input length -/

/-- The bit length of a rational matrix is at most its input size.

The hypothesis `0 < m + n` is necessary: for the empty matrix `m = n = 0` the
common denominator is `1`, so `bitLenMat A = 1` while `inputLen A = 0`. -/
theorem bitLenMat_le_inputLen {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (hmn : 0 < m + n) :
    bitLenMat A ≤ inputLen A := by
  classical
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · obtain rfl | hn := Nat.eq_zero_or_pos n
    · omega
    · -- no rows: the matrix denominator is `1`, there are no entries
      have hden1 : A.den = 1 := by
        have h : A.den ∣ 1 := by
          rw [Matrix.den_dvd_iff]
          intro i
          exact absurd i.isLt (Nat.not_lt_zero _)
        exact Nat.dvd_one.mp h
      have hden : A.den.size = 1 := by
        rw [hden1]
        decide
      have hsup : (Finset.univ.sup (fun p : Fin 0 × Fin n => bitLenInt (A.num p.1 p.2))) = 0 := by
        refine le_antisymm ?_ (Nat.zero_le _)
        refine Finset.sup_le ?_
        intro p _
        exact absurd p.1.isLt (Nat.not_lt_zero _)
      have hble : bitLenMat A ≤ 1 := by
        unfold bitLenMat
        rw [hden, hsup]
        simp
      have hin : n ≤ inputLen A := by
        unfold inputLen
        omega
      omega
  · obtain rfl | hn := Nat.eq_zero_or_pos n
    · -- no columns: the matrix denominator is `1`, there are no entries
      have hden1 : A.den = 1 := by
        have h : A.den ∣ 1 := by
          rw [Matrix.den_dvd_iff]
          intro i j
          exact absurd j.isLt (Nat.not_lt_zero _)
        exact Nat.dvd_one.mp h
      have hden : A.den.size = 1 := by
        rw [hden1]
        decide
      have hsup : (Finset.univ.sup (fun p : Fin m × Fin 0 => bitLenInt (A.num p.1 p.2))) = 0 := by
        refine le_antisymm ?_ (Nat.zero_le _)
        refine Finset.sup_le ?_
        intro p _
        exact absurd p.2.isLt (Nat.not_lt_zero _)
      have hble : bitLenMat A ≤ 1 := by
        unfold bitLenMat
        rw [hden, hsup]
        simp
      have hin : m ≤ inputLen A := by
        unfold inputLen
        omega
      omega
    · -- the genuine case: at least one row and one column
      have hsum_eq : (∑ p : Fin m × Fin n, bitLenRat (A p.1 p.2)) = ∑ i, ∑ j, bitLenRat (A i j) :=
        Fintype.sum_prod_type (fun p : Fin m × Fin n => bitLenRat (A p.1 p.2))
      have hden := mat_den_size_le_sum A hm hn
      unfold bitLenMat inputLen
      refine max_le ?_ ?_
      · omega
      · refine Finset.sup_le ?_
        intro p _
        have h := mat_bitLenInt_num_le_sum A p.1 p.2
        omega

end Q1Paper.PaperI
