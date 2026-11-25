
import Q1Paper.PaperI.S04_Rationality.Claim15_Arithmetic
import Q1Paper.PaperI.S04_Rationality.BitLenMatMul
import Q1Paper.PaperI.S04_Rationality.InputLen
import Q1Paper.PaperI.S05_Complexity.ComplexityCounts
import Q1Paper.PaperI.S02_Subspace.Claim14_Bases
/-!
Q1Paper/PaperI/S04_Rationality/Claim15.lean

Claim 15 of Paper I, **first milestone**: the three *composed* objects, with a
single explicit polynomial bound in terms of `inputLen`.

The paper's Claim 15 lists the objects whose entries have `poly(L)` bit length;
the composed ones are the products
  `h0 = L0 * N`,  `g0 = L0 * (A * N)`,  `H = X * B`.
Here only these three products are treated (no `X`, `G`, `D`, no `ZᵀZ`, no
Claim 15 (ii)/(iii)).  Everything is built from the toolkit:

* `bitLenMat_mul_le`             (`BitLenMatMul.lean`): `bitLenMat (X * B) ≤ bitLenMat X + bitLenMat B + k.size + 1`;
* `bitLenMat_chain_inputLen_le`  (`BitLenMatMul.lean`): the two-fold chain `L0 * (A * P)`;
* `bitLenMat_le_inputLen`        (`InputLen.lean`): `bitLenMat ≤ inputLen`;
* `bitLenRat_le_bitLenMat`       (`RationalBasis.lean`): entries are dominated by `bitLenMat`.

Design note.  The quantities that compose are `bitLenMat`/`inputLen` of the
*factors*.  For the kernel basis `N` the natural hypothesis is not
`inputLen N ≤ L` (that is false for a computed `N`), but an entrywise bound
`∀ i j, bitLenRat (N i j) ≤ t`; `inputLen_le_of_entry_bound` below converts such
an entrywise bound into `inputLen N ≤ n + k + n * k * t`, which is exactly what
`exists_chart_bases`/`exists_rational_bases_bounded` deliver (`t = tauM P (bitLenMat P)`).
So `N` is fed into the composition through that conversion; see
`bitLenMat_L0_mul_N_of_entries` and `bitLenMat_L0_mul_A_mul_N_of_entries`.

No `sorry`, no `admit`, no new axioms.
-/


open Matrix
open scoped BigOperators

namespace Q1Paper.Claim15

open Q1Paper.PaperI
open Q1Paper.PaperI.Chart14

/-! ## 0.  Two elementary conversions -/

/-- Every entry is dominated by `bitLenMat` (restated from `RationalBasis.lean`). -/
theorem bitLenRat_le_bitLenMat' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    bitLenRat (A i j) ≤ bitLenMat A :=
  bitLenRat_le_bitLenMat A i j

/-- The number of columns is at most the input length. -/
theorem cols_le_inputLen {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : n ≤ inputLen A := by
  unfold inputLen
  omega

/-- The number of rows is at most the input length. -/
theorem rows_le_inputLen {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : m ≤ inputLen A := by
  unfold inputLen
  omega

/-- **An entrywise bound gives an `inputLen` bound.**  `inputLen A = m + n + ∑ᵢⱼ bitLenRat (A i j)`,
and the double sum has `m * n` terms of size at most `t`. -/
theorem inputLen_le_of_entry_bound {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) {t : ℕ}
    (h : ∀ i j, bitLenRat (M i j) ≤ t) : inputLen M ≤ m + n + m * n * t := by
  have hsum : ∑ i : Fin m, ∑ j : Fin n, bitLenRat (M i j) ≤ m * n * t := by
    have hi : ∀ i : Fin m, ∑ j : Fin n, bitLenRat (M i j) ≤ n * t := by
      intro i
      calc ∑ j : Fin n, bitLenRat (M i j) ≤ ∑ _j : Fin n, t := Finset.sum_le_sum (fun j _ => h i j)
        _ = n * t := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    calc ∑ i : Fin m, ∑ j : Fin n, bitLenRat (M i j) ≤ ∑ _i : Fin m, n * t :=
          Finset.sum_le_sum (fun i _ => hi i)
      _ = m * (n * t) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      _ = m * n * t := by ring
  unfold inputLen
  omega

/-! ## 1.  The generic product `H = X * B` -/

/-- **`H = X * B`.**  If both factors have `inputLen ≤ L`, the product has
`bitLenMat ≤ 2 L + k.size + 1`, where `k` is the inner dimension.  This is
`bitLenMat_mul_le` composed with `bitLenMat_le_inputLen` for the two factors. -/
theorem bitLenMat_mul_le_inputLen {a k b : ℕ} (X : Matrix (Fin a) (Fin k) ℚ)
    (B : Matrix (Fin k) (Fin b) ℚ) (hX : 0 < a + k) (hB : 0 < k + b) {L : ℕ}
    (hXL : inputLen X ≤ L) (hBL : inputLen B ≤ L) :
    bitLenMat (X * B) ≤ 2 * L + k.size + 1 := by
  have h1 := bitLenMat_mul_le X B
  have h2 : bitLenMat X ≤ L := le_trans (bitLenMat_le_inputLen X hX) hXL
  have h3 : bitLenMat B ≤ L := le_trans (bitLenMat_le_inputLen B hB) hBL
  omega

/-- Entry form of `bitLenMat_mul_le_inputLen`: every entry of `H = X * B` is at
most `2 L + k.size + 1`. -/
theorem bitLenRat_mul_le_inputLen {a k b : ℕ} (X : Matrix (Fin a) (Fin k) ℚ)
    (B : Matrix (Fin k) (Fin b) ℚ) (hX : 0 < a + k) (hB : 0 < k + b) {L : ℕ}
    (hXL : inputLen X ≤ L) (hBL : inputLen B ≤ L) (i : Fin a) (j : Fin b) :
    bitLenRat ((X * B) i j) ≤ 2 * L + k.size + 1 :=
  le_trans (bitLenRat_le_bitLenMat (X * B) i j) (bitLenMat_mul_le_inputLen X B hX hB hXL hBL)

/-- **`H = X * B` with an entrywise hypothesis on `X`** (the shape in which the
chart bases of Claim 14 come): `inputLen X` is replaced by
`a + k + a * k * t`. -/
theorem bitLenMat_mul_of_entries {a k b : ℕ} (X : Matrix (Fin a) (Fin k) ℚ)
    (B : Matrix (Fin k) (Fin b) ℚ) {L t : ℕ} (hXe : ∀ i j, bitLenRat (X i j) ≤ t)
    (hB : 0 < k + b) (hBL : inputLen B ≤ L) (hX : 0 < a + k) :
    bitLenMat (X * B) ≤ 2 * (L + (a + k + a * k * t)) + k.size + 1 := by
  have hXi : inputLen X ≤ a + k + a * k * t := inputLen_le_of_entry_bound X hXe
  have h := bitLenMat_mul_le_inputLen X B hX hB (L := L + (a + k + a * k * t))
    (by omega) (by omega)
  omega

/-! ## 2.  `h0 = L0 * N` -/

/-- **`h0 = L0 * N`.**  `L0 : Fin r0 × Fin n` is the prescribed block, `N`
the kernel basis of the stack `P`.  With `inputLen L0 ≤ L` and
`inputLen N ≤ L`, the product has bit length at most `2 L + n.size + 1`. -/
theorem bitLenMat_L0_mul_N {n k r0 : ℕ} (L0 : Matrix (Fin r0) (Fin n) ℚ)
    (N : Matrix (Fin n) (Fin k) ℚ) {L : ℕ} (hL0 : inputLen L0 ≤ L) (hN : inputLen N ≤ L)
    (hr0 : 0 < r0 + n) (hNpos : 0 < n + k) :
    bitLenMat (L0 * N) ≤ 2 * L + n.size + 1 :=
  bitLenMat_mul_le_inputLen L0 N hr0 hNpos hL0 hN

/-- Entry form of the `h0` bound. -/
theorem bitLenRat_L0_mul_N {n k r0 : ℕ} (L0 : Matrix (Fin r0) (Fin n) ℚ)
    (N : Matrix (Fin n) (Fin k) ℚ) {L : ℕ} (hL0 : inputLen L0 ≤ L) (hN : inputLen N ≤ L)
    (hr0 : 0 < r0 + n) (hNpos : 0 < n + k) (i : Fin r0) (j : Fin k) :
    bitLenRat ((L0 * N) i j) ≤ 2 * L + n.size + 1 :=
  le_trans (bitLenRat_le_bitLenMat (L0 * N) i j)
    (bitLenMat_L0_mul_N L0 N hL0 hN hr0 hNpos)

/-- **`h0` with the kernel-basis hypothesis of Claim 13/14.**  The hypothesis on
`N` is the one `exists_chart_bases` produces: an entrywise BOUND, not
`inputLen N ≤ L`.  Composing `inputLen_le_of_entry_bound` with `h0`'s bound gives
`2 (L + (n + k + n k t)) + n.size + 1`, a polynomial in `L` once `t` is. -/
theorem bitLenMat_L0_mul_N_of_entries {n k r0 : ℕ} (L0 : Matrix (Fin r0) (Fin n) ℚ)
    (N : Matrix (Fin n) (Fin k) ℚ) {L t : ℕ} (hL0 : inputLen L0 ≤ L)
    (hN : ∀ i j, bitLenRat (N i j) ≤ t) (hr0 : 0 < r0 + n) (hNpos : 0 < n + k) :
    bitLenMat (L0 * N) ≤ 2 * (L + (n + k + n * k * t)) + n.size + 1 := by
  have hNi : inputLen N ≤ n + k + n * k * t := inputLen_le_of_entry_bound N hN
  have h := bitLenMat_L0_mul_N L0 N (L := L + (n + k + n * k * t))
    (by omega) (by omega) hr0 hNpos
  omega

/-! ## 3.  `g0 = L0 * (A * N)` -/

/-- **`g0 = L0 * (A * N)`.**  This is exactly `bitLenMat_chain_inputLen_le` with
`P := N`: the three positivity hypotheses `0 < n + k`, `0 < n`, `0 < r0` are the
ones that lemma requires. -/
theorem bitLenMat_L0_mul_A_mul_N {n k r0 : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (L0 : Matrix (Fin r0) (Fin n) ℚ) (N : Matrix (Fin n) (Fin k) ℚ) {L : ℕ}
    (_hL0 : inputLen L0 ≤ L) (_hA : inputLen A ≤ L) (_hN : inputLen N ≤ L)
    (hn : 0 < n) (hNpos : 0 < n + k) (hr0 : 0 < r0) :
    bitLenMat (L0 * (A * N)) ≤ inputLen L0 + inputLen A + inputLen N + 2 * (n.size + 1) :=
  bitLenMat_chain_inputLen_le N A L0 hNpos hn hr0

/-- **`g0`, numeric form.**  Using `inputLen ≤ L` for the three factors and
`n ≤ inputLen A ≤ L`, the chain bound is at most `3 L + 2 (n + 1) ≤ 5 L + 2`. -/
theorem bitLenMat_L0_mul_A_mul_N_le {n k r0 : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (L0 : Matrix (Fin r0) (Fin n) ℚ) (N : Matrix (Fin n) (Fin k) ℚ) {L : ℕ}
    (hL0 : inputLen L0 ≤ L) (hA : inputLen A ≤ L) (hN : inputLen N ≤ L)
    (hn : 0 < n) (hNpos : 0 < n + k) (hr0 : 0 < r0) :
    bitLenMat (L0 * (A * N)) ≤ 5 * L + 2 := by
  have h := bitLenMat_L0_mul_A_mul_N A L0 N hL0 hA hN hn hNpos hr0
  have hnL : n ≤ L := le_trans (cols_le_inputLen A) hA
  have hsize : n.size ≤ L := le_trans (nat_size_le_self n) hnL
  omega

/-- Entry form of the `g0` bound. -/
theorem bitLenRat_L0_mul_A_mul_N {n k r0 : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (L0 : Matrix (Fin r0) (Fin n) ℚ) (N : Matrix (Fin n) (Fin k) ℚ) {L : ℕ}
    (hL0 : inputLen L0 ≤ L) (hA : inputLen A ≤ L) (hN : inputLen N ≤ L)
    (hn : 0 < n) (hNpos : 0 < n + k) (hr0 : 0 < r0) (i : Fin r0) (j : Fin k) :
    bitLenRat ((L0 * (A * N)) i j) ≤ 5 * L + 2 :=
  le_trans (bitLenRat_le_bitLenMat (L0 * (A * N)) i j)
    (bitLenMat_L0_mul_A_mul_N_le A L0 N hL0 hA hN hn hNpos hr0)

/-- **`g0` with the kernel-basis hypothesis of Claim 13/14** (entrywise bound on
`N`, as produced by `exists_chart_bases`). -/
theorem bitLenMat_L0_mul_A_mul_N_of_entries {n k r0 : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (L0 : Matrix (Fin r0) (Fin n) ℚ) (N : Matrix (Fin n) (Fin k) ℚ) {L t : ℕ}
    (hL0 : inputLen L0 ≤ L) (hA : inputLen A ≤ L) (hN : ∀ i j, bitLenRat (N i j) ≤ t)
    (hn : 0 < n) (hNpos : 0 < n + k) (hr0 : 0 < r0) :
    bitLenMat (L0 * (A * N)) ≤ L + L + (n + k + n * k * t) + 2 * (n.size + 1) := by
  have h := bitLenMat_chain_inputLen_le N A L0 hNpos hn hr0
  have hNi : inputLen N ≤ n + k + n * k * t := inputLen_le_of_entry_bound N hN
  omega

end Q1Paper.Claim15

/-! ## 4.  Axiom audit (must be `[propext, Classical.choice, Quot.sound]`) -/

