
import Q1Paper.PaperI.InputLen
import Q1Paper.PaperI.MinorRank
import Q1Paper.PaperI.Claim12

/-!
Q1Paper/PaperI/RationalBasis.lean

Scratch module for Claim 13 (`lem:rationalbasis`) of Paper I: rational bases and
annihilators with an explicit bit-length bound.

The claim (existence + explicit bit bound; the "computed in polynomially many bit
operations" part is deliberately *not* formalised):

Let `M : Matrix (Fin m) (Fin n) ℚ` with `bitLenMat M ≤ tau`, put `r = M.rank` and
`tauM = 2 * r * ((n + 1) * tau + (r + 1).size + 1) + 1`.  Then there exist

* `N`, whose columns are a basis of `ker M` (`M * N = 0`, `N.rank = n - r`, and
  `ker M` is the range of `N`),
* `R : Matrix (Fin r) (Fin n) ℚ` whose rows are a basis of the row space of `M`
  (`R.rank = r` and `rowSpace R = rowSpace M`),
* `D : Matrix (Fin (n - r)) (Fin n) ℚ` with `ker D = row M`,

all of whose entries satisfy `bitLenRat ≤ tauM`.  This is
`exists_rational_bases_bounded` below; the three components are also proved
separately (`exists_kernel_basis_bounded`, `exists_row_basis_bounded`,
`exists_annihilator_bounded`) with the same bound.

Contents (this file):
* bit-length toolbox: the rational-per-integer ratio bound (`bitLenRat_div_int_le`),
  the factorial bound, the minor bound `bitLenInt (minor) ≤ ω * tau + bitLenInt ω!`,
  the entry bound `bitLenRat (A i j) ≤ bitLenMat A`, and the arithmetic showing
  `r * tau + bitLenInt r! ≤ tauM`;
* the row space `rowSpace` and the row basis `R` (the `r` rows of `M` selected by
  a maximal minor);
* the kernel basis `N` by Cramer's rule (`Matrix.cramer`): for every column `j`
  outside the pivot set the column of `N` has a `1` at `j` and, on the pivot
  coordinates, the Cramer solution `-(cramer B w)/det B`.  Its entries are thus
  ratios of two `r × r` minors of the cleared integer matrix `M.num`, and the
  transpose of the two minors' `bitLenInt` bounds (Leibniz) gives `bitLenRat ≤ tauM`;
* the annihilator `D = Nᵀ`, whose kernel is the row space by rank count.

No `sorry`, no `admit`, no new axioms (only `propext`, `Classical.choice`,
`Quot.sound`).
-/


open Matrix

namespace Q1Paper.PaperI

/-! ## 1.  Bit-length toolbox -/

/-- **Ratio of two integers.**  The bit length of `a / b` (as a rational number)
is bounded by the maximum of the bit lengths of `a` and `b`.

Both the reduced numerator and the reduced denominator of `a / b` divide,
respectively, `a` and `b`: cross-multiplying `a / b = q.num / q.den` gives
`q.num * b = a * q.den`, and `q.num`, `q.den` are coprime. -/
theorem bitLenRat_div_int_le (a b : ℤ) (hb : b ≠ 0) :
    bitLenRat ((a : ℚ) / (b : ℚ)) ≤ max (bitLenInt a) (bitLenInt b) := by
  classical
  set q : ℚ := (a : ℚ) / (b : ℚ) with hq
  have hqb : q * (b : ℚ) = (a : ℚ) := by
    rw [hq]
    field_simp
  -- the integer identity behind the reduction
  have hkey : q.num * b = a * (q.den : ℤ) := by
    have h1 : ((q.num : ℚ) * (b : ℚ)) = ((a : ℚ) * (q.den : ℚ)) := by
      have h2 : (q.num : ℚ) = q * (q.den : ℚ) := (Rat.mul_den_eq_num q).symm
      calc (q.num : ℚ) * (b : ℚ) = (q * (q.den : ℚ)) * (b : ℚ) := by rw [h2]
        _ = (q * (b : ℚ)) * (q.den : ℚ) := by ring
        _ = (a : ℚ) * (q.den : ℚ) := by rw [hqb]
    exact_mod_cast h1
  have hnat : q.num.natAbs * b.natAbs = a.natAbs * q.den := by
    have := congr_arg Int.natAbs hkey
    simpa [Int.natAbs_mul] using this
  have hcop : q.num.natAbs.Coprime q.den := q.reduced
  -- the reduced denominator divides `b`
  have hdvd_den : q.den ∣ b.natAbs := by
    refine hcop.symm.dvd_of_dvd_mul_left ?_
    exact ⟨a.natAbs, by rw [hnat, Nat.mul_comm]⟩
  -- the reduced numerator divides `a`
  have hdvd_num : q.num.natAbs ∣ a.natAbs := by
    refine hcop.dvd_of_dvd_mul_left ?_
    exact ⟨b.natAbs, by rw [hnat, Nat.mul_comm]⟩
  have hnum_le : bitLenInt q.num ≤ bitLenInt a := by
    rcases eq_or_ne a 0 with ha | ha
    · have hq0 : q = 0 := by rw [hq, ha]; simp
      rw [hq0, ha]
      simp [bitLenInt]
    · have hle : q.num.natAbs ≤ a.natAbs :=
        Nat.le_of_dvd (Int.natAbs_pos.mpr ha) hdvd_num
      exact Nat.size_le_size hle
  have hden_le : q.den.size ≤ bitLenInt b :=
    Nat.size_le_size (Nat.le_of_dvd (Int.natAbs_pos.mpr hb) hdvd_den)
  refine max_le ?_ ?_
  · exact le_trans hnum_le (le_max_left _ _)
  · exact le_trans hden_le (le_max_right _ _)

/-- **Factorial bound.**  For `k ≥ 1`, `k!` has at most `k * (number of bits of k)`
bits.  Proof by induction: `(k+1)! = k! * (k+1)`, and `k.size ≤ (k+1).size`. -/
theorem bitLenInt_factorial_le_rat {k : ℕ} (hk : 1 ≤ k) :
    bitLenInt (k.factorial) ≤ k * k.size := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
      have hfac : ((k + 1).factorial : ℤ) = ((k.factorial : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      calc bitLenInt ((k + 1).factorial)
          = bitLenInt (((k.factorial : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ)) := by rw [hfac]
        _ ≤ bitLenInt ((k.factorial : ℕ) : ℤ) + bitLenInt ((k + 1 : ℕ) : ℤ) := bitLenInt_mul _ _
        _ = bitLenInt (k.factorial) + (k + 1).size := by simp only [bitLenInt_natCast]
        _ ≤ k * k.size + (k + 1).size := Nat.add_le_add_right ih _
        _ ≤ k * (k + 1).size + (k + 1).size :=
            Nat.add_le_add_right (Nat.mul_le_mul_left k (Nat.size_le_size (Nat.le_succ k))) _
        _ = (k + 1) * (k + 1).size := by rw [Nat.succ_mul]

/-- **Minor bound.**  Every `ω × ω` minor of an integer matrix whose entries have
bit length at most `tau` has bit length at most `ω * tau + bitLenInt ω!`
(Leibniz). -/
theorem bitLenInt_det_submatrix_le {m n ω : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) {tau : ℕ}
    (hA : ∀ i j, bitLenInt (A i j) ≤ tau) (ρ : Fin ω → Fin m) (κ : Fin ω → Fin n) :
    bitLenInt (A.submatrix ρ κ).det ≤ ω * tau + bitLenInt (ω.factorial) := by
  refine bitLenInt_det_le (A.submatrix ρ κ) ?_
  intro i j
  have hlt : |A.submatrix ρ κ i j| < (2 : ℤ) ^ bitLenInt (A.submatrix ρ κ i j) := bitLenInt_abs_lt _
  have hle : (2 : ℤ) ^ bitLenInt (A.submatrix ρ κ i j) ≤ (2 : ℤ) ^ tau := by
    have h : 2 ^ bitLenInt (A.submatrix ρ κ i j) ≤ 2 ^ tau :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (hA (ρ i) (κ j))
    exact_mod_cast h
  exact lt_of_lt_of_le hlt hle

/-- Every entry of `M` has bit length at most the matrix bit length of `M`. -/
theorem bitLenRat_le_bitLenMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    bitLenRat (A i j) ≤ bitLenMat A := by
  have hk : 0 < A.den / (A i j).den :=
    Nat.div_pos (Nat.le_of_dvd (mat_den_pos A) (mat_den_dvd A i j)) (Rat.den_pos (A i j))
  have hnum : bitLenInt (A i j).num ≤ bitLenInt (A.num i j) := by
    have h := congr_arg Int.natAbs (mat_num_eq_div_den_mul_num A i j)
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at h
    have hle : (A i j).num.natAbs ≤ (A.num i j).natAbs := by
      rw [h]
      calc (A i j).num.natAbs = 1 * (A i j).num.natAbs := (one_mul _).symm
        _ ≤ (A.den / (A i j).den) * (A i j).num.natAbs :=
            Nat.mul_le_mul_right _ hk
    exact Nat.size_le_size hle
  refine max_le ?_ ?_
  · exact le_trans hnum (mat_bitLenInt_num_le_bitLenMat A i j)
  · exact le_trans (mat_den_size_entry_le A i j) (mat_den_size_le_bitLenMat A)

/-- `bitLenInt 1 = 1`. -/
theorem bitLenInt_one : bitLenInt (1 : ℤ) = 1 := by decide

/-- `bitLenRat 1 = 1`. -/
theorem bitLenRat_one : bitLenRat (1 : ℚ) = 1 := by decide

/-- The Claim 13 bit bound. -/
noncomputable def tauM {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ) (tau : ℕ) : ℕ :=
  2 * MM.rank * ((n + 1) * tau + (MM.rank + 1).size + 1) + 1

theorem one_le_tauM {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ) (tau : ℕ) : 1 ≤ tauM MM tau := by
  unfold tauM
  omega

/-- The constant is large enough for the Cramer entries, whose bit length is at
most `r * tau + bitLenInt r!`. -/
theorem rank_mul_tau_add_factorial_le_tauM {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ) (tau : ℕ) :
    MM.rank * tau + bitLenInt (MM.rank.factorial) ≤ tauM MM tau := by
  rcases Nat.eq_zero_or_pos MM.rank with hzero | hpos
  · have hlhs : MM.rank * tau + bitLenInt (MM.rank.factorial) = 1 := by
      rw [show MM.rank = 0 from hzero]
      simp [bitLenInt_one]
    rw [hlhs]
    exact one_le_tauM MM tau
  · have hfac := bitLenInt_factorial_le_rat hpos
    have hsz : MM.rank.size ≤ (MM.rank + 1).size := Nat.size_le_size (Nat.le_succ _)
    have hB1 : MM.rank * tau ≤ MM.rank * ((n + 1) * tau + (MM.rank + 1).size + 1) := by
      refine Nat.mul_le_mul_left _ ?_
      have h : tau ≤ (n + 1) * tau := Nat.le_mul_of_pos_left tau (by omega)
      omega
    have hB2 : bitLenInt (MM.rank.factorial)
        ≤ MM.rank * ((n + 1) * tau + (MM.rank + 1).size + 1) := by
      refine le_trans hfac (le_trans (Nat.mul_le_mul_left _ hsz) (Nat.mul_le_mul_left _ ?_))
      omega
    unfold tauM
    calc MM.rank * tau + bitLenInt (MM.rank.factorial)
        ≤ MM.rank * ((n + 1) * tau + (MM.rank + 1).size + 1)
          + MM.rank * ((n + 1) * tau + (MM.rank + 1).size + 1) := Nat.add_le_add hB1 hB2
      _ = 2 * MM.rank * ((n + 1) * tau + (MM.rank + 1).size + 1) := by ring
      _ ≤ 2 * MM.rank * ((n + 1) * tau + (MM.rank + 1).size + 1) + 1 := Nat.le_succ _

/-! ## 2.  The row space and the row basis `R` -/

/-- The row space of a rational matrix, as a submodule of `ℚ^n`. -/
def rowSpace {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ) : Submodule ℚ (Fin n → ℚ) :=
  Submodule.span ℚ (Set.range MM.row)

/-- A nonzero `r × r` minor at `(ρ, κ)` makes the `r` selected rows linearly
independent: the selected row matrix has rank `r`. -/
theorem rank_submatrix_selected {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ)
    (ρ : Fin MM.rank → Fin m) (κ : Fin MM.rank → Fin n)
    (hdet : (MM.submatrix ρ κ).det ≠ 0) :
    (MM.submatrix ρ id).rank = MM.rank := by
  have hle : MM.rank ≤ (MM.submatrix ρ id).rank := by
    refine rank_le_of_det_maximalMinor_ne_zero (MM.submatrix ρ id) id κ ?_
    simpa using hdet
  have hheight : (MM.submatrix ρ id).rank ≤ MM.rank := Matrix.rank_le_height _
  omega

/-- The selected rows span the whole row space. -/
theorem rowSpace_submatrix_selected {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ)
    (ρ : Fin MM.rank → Fin m) (κ : Fin MM.rank → Fin n)
    (hdet : (MM.submatrix ρ κ).det ≠ 0) :
    rowSpace (MM.submatrix ρ id) = rowSpace MM := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · unfold rowSpace
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨ρ i, rfl⟩
  · unfold rowSpace
    rw [← Matrix.rank_eq_finrank_span_row (MM.submatrix ρ id),
      ← Matrix.rank_eq_finrank_span_row MM, rank_submatrix_selected MM ρ κ hdet]

/-- Every row of `M` is a combination of the selected rows. -/
theorem exists_row_coefficients {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ)
    (ρ : Fin MM.rank → Fin m) (κ : Fin MM.rank → Fin n)
    (hdet : (MM.submatrix ρ κ).det ≠ 0) :
    ∃ Cc : Matrix (Fin m) (Fin MM.rank) ℚ, MM = Cc * MM.submatrix ρ id := by
  classical
  have hspan : rowSpace (MM.submatrix ρ id) = rowSpace MM :=
    rowSpace_submatrix_selected MM ρ κ hdet
  have hex : ∀ a : Fin m, ∃ c : Fin MM.rank → ℚ,
      ∑ i, c i • (MM.submatrix ρ id).row i = MM.row a := by
    intro a
    have hmem : MM.row a ∈ rowSpace (MM.submatrix ρ id) := by
      rw [hspan]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
  refine ⟨fun a i => (Classical.choose (hex a)) i, ?_⟩
  ext a j
  have h := congrFun (Classical.choose_spec (hex a)) j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row, Matrix.mul_apply,
    Matrix.submatrix_apply, id_eq] at h ⊢
  exact h.symm

/-- For positive rank, the input bit length `tau` is below the Claim 13 constant. -/
theorem tau_le_tauM {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ) {tau : ℕ} (hpos : 1 ≤ MM.rank) :
    tau ≤ tauM MM tau := by
  have h1 : tau ≤ (n + 1) * tau := Nat.le_mul_of_pos_left tau (by omega)
  have h3 : (n + 1) * tau + (MM.rank + 1).size + 1
      ≤ 2 * MM.rank * ((n + 1) * tau + (MM.rank + 1).size + 1) := by
    calc (n + 1) * tau + (MM.rank + 1).size + 1
        = 1 * ((n + 1) * tau + (MM.rank + 1).size + 1) := (one_mul _).symm
      _ ≤ (2 * MM.rank) * ((n + 1) * tau + (MM.rank + 1).size + 1) :=
          Nat.mul_le_mul_right _ (by omega)
  unfold tauM
  omega

/-- **Row basis with bit bound.**  The `r` rows of `M` selected by a maximal
minor form a basis of the row space of `M`; their entries are entries of `M`
itself, hence have bit length at most `bitLenMat M ≤ tau ≤ tauM`. -/
theorem exists_row_basis_bounded {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ) {tau : ℕ}
    (hM : bitLenMat MM ≤ tau) :
    ∃ R : Matrix (Fin MM.rank) (Fin n) ℚ,
      R.rank = MM.rank ∧ rowSpace R = rowSpace MM ∧
        ∀ i j, bitLenRat (R i j) ≤ tauM MM tau := by
  classical
  obtain ⟨ρ, κ, -, -, hdet⟩ := exists_det_submatrix_ne_zero_of_rank MM rfl
  refine ⟨MM.submatrix ρ id, rank_submatrix_selected MM ρ κ hdet,
    rowSpace_submatrix_selected MM ρ κ hdet, ?_⟩
  intro i j
  rcases Nat.eq_zero_or_pos MM.rank with hz | hp
  · exact absurd i.isLt (by omega)
  · exact le_trans (le_trans (bitLenRat_le_bitLenMat MM (ρ i) j) hM) (tau_le_tauM MM hp)

/-! ## 3.  The kernel basis `N` by Cramer's rule -/

/-- **Cramer's rule in division form.**  If `B.det ≠ 0`, the vector with
components `-(cramer B w k) / B.det` solves `B *ᵥ s = -w`. -/
theorem mulVec_cramer_div {r : ℕ} (B : Matrix (Fin r) (Fin r) ℚ) (w : Fin r → ℚ)
    (hd : B.det ≠ 0) :
    B *ᵥ (fun k => -(cramer B w k / B.det)) = -w := by
  have hvec : (fun k => -(cramer B w k / B.det)) = (-(B.det)⁻¹) • (cramer B w) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [hvec, Matrix.mulVec_smul, mulVec_cramer, smul_smul]
  have hcoef : -((B.det)⁻¹) * B.det = -1 := by field_simp
  rw [hcoef, neg_one_smul]

/-- **Kernel basis with bit bound.**  Every entry of the constructed `N` is a
ratio of two `r × r` minors of the cleared integer matrix `M.num`, hence has
`bitLenRat ≤ tauM`. -/
theorem exists_kernel_basis_bounded {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ) {tau : ℕ}
    (hM : bitLenMat MM ≤ tau) :
    ∃ N : Matrix (Fin n) (Fin (n - MM.rank)) ℚ,
      MM * N = 0 ∧ N.rank = n - MM.rank ∧ ∀ i j, bitLenRat (N i j) ≤ tauM MM tau := by
  classical
  obtain ⟨ρ, κ, hρ, hκ, hdet⟩ := exists_det_submatrix_ne_zero_of_rank MM rfl
  -- ### (0) the entry bound on the cleared integer matrix
  have hA : ∀ i j, bitLenInt (MM.num i j) ≤ tau := fun i j =>
    le_trans (mat_bitLenInt_num_le_bitLenMat MM i j) hM
  have hAq : MM.num.map (Int.castRingHom ℚ) = (MM.den : ℚ) • MM := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    exact mat_num_eq_den_mul MM i j
  have hdenq : ((MM.den : ℚ)) ≠ 0 := by
    have h := mat_den_pos MM
    exact_mod_cast h.ne'
  -- ### (1) the ratio formula for the determinants of rational submatrices
  have hdet_formula : ∀ (κ' : Fin MM.rank → Fin n),
      (MM.submatrix ρ κ').det
        = (((MM.num.submatrix ρ κ').det : ℚ) / (MM.den : ℚ) ^ MM.rank) := by
    intro κ'
    have h1 : ((MM.num.submatrix ρ κ').det : ℚ)
        = ((MM.num.map (Int.castRingHom ℚ)).submatrix ρ κ').det := by
      simpa [Matrix.submatrix_map] using
        RingHom.map_det (Int.castRingHom ℚ) (MM.num.submatrix ρ κ')
    have hsub : (MM.num.map (Int.castRingHom ℚ)).submatrix ρ κ'
        = (MM.den : ℚ) • (MM.submatrix ρ κ') := by
      rw [hAq]
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.smul_apply]
    have h2 : (MM.den : ℚ) ^ MM.rank * (MM.submatrix ρ κ').det
        = ((MM.num.submatrix ρ κ').det : ℚ) := by
      rw [show (MM.den : ℚ) ^ MM.rank
            = (MM.den : ℚ) ^ Fintype.card (Fin MM.rank) from by simp]
      rw [← Matrix.det_smul, ← hsub, ← h1]
    rw [eq_div_iff (pow_ne_zero _ hdenq), mul_comm]
    exact h2
  -- ### (2) the Cramer matrices
  let Jt := {j : Fin n // j ∉ Set.range κ}
  set Cm : Matrix (Fin MM.rank) Jt ℚ :=
    fun k j => -((cramer (MM.submatrix ρ κ) (fun k' => MM (ρ k') (j : Fin n))) k
      / (MM.submatrix ρ κ).det) with hCm
  set E : Matrix (Fin n) (Fin MM.rank) ℚ :=
    (1 : Matrix (Fin n) (Fin n) ℚ).submatrix id κ with hE
  set Pm : Matrix (Fin n) Jt ℚ :=
    (1 : Matrix (Fin n) (Fin n) ℚ).submatrix id (fun j : Jt => (j : Fin n)) with hPm
  set N0 : Matrix (Fin n) Jt ℚ := E * Cm + Pm with hN0
  obtain ⟨Cc, hCc⟩ := exists_row_coefficients MM ρ κ hdet
  -- the replaced-column map
  have hUpd : ∀ (k : Fin MM.rank) (j : Jt),
      (MM.submatrix ρ κ).updateCol k (fun k' => MM (ρ k') (j : Fin n))
        = MM.submatrix ρ (fun b => if b = k then (j : Fin n) else κ b) := by
    intro k j
    ext a b
    rw [Matrix.updateCol_apply]
    by_cases hb : b = k <;> simp [hb]
  -- Cramer: the selected rows annihilate `Cm`, leaving the pivot column
  have hBCm : (MM.submatrix ρ κ) * Cm
      = -(MM.submatrix ρ (fun j : Jt => (j : Fin n))) := by
    ext k j
    have h := congrFun
      (mulVec_cramer_div (MM.submatrix ρ κ) (fun k' => MM (ρ k') (j : Fin n)) hdet) k
    rw [Matrix.mulVec_apply_eq_sum] at h
    rw [Matrix.mul_apply, hCm]
    simp only [Matrix.submatrix_apply, Matrix.neg_apply, Pi.neg_apply]
    simpa using h
  -- the two column-selection identities
  have hWE : (MM.submatrix ρ id) * E = MM.submatrix ρ κ := by
    rw [hE]
    have h := Matrix.mul_submatrix_one (Equiv.refl (Fin n)) κ (MM.submatrix ρ id)
    simpa using h
  have hWPm : (MM.submatrix ρ id) * Pm = MM.submatrix ρ (fun j : Jt => (j : Fin n)) := by
    rw [hPm]
    have h := Matrix.mul_submatrix_one (Equiv.refl (Fin n))
      (fun j : Jt => (j : Fin n)) (MM.submatrix ρ id)
    simpa using h
  -- ### (3) hence `MM * N0 = 0`
  have hmul : ∀ (Y : Matrix (Fin n) Jt ℚ),
      MM * Y = Cc * ((MM.submatrix ρ id) * Y) := by
    intro Y
    conv_lhs => rw [hCc]
    rw [Matrix.mul_assoc]
  have hMN0 : MM * N0 = 0 := by
    calc MM * N0 = MM * (E * Cm) + MM * Pm := by rw [hN0, Matrix.mul_add]
      _ = Cc * ((MM.submatrix ρ id) * (E * Cm))
            + Cc * ((MM.submatrix ρ id) * Pm) := by rw [hmul (E * Cm), hmul Pm]
      _ = Cc * ((MM.submatrix ρ κ) * Cm)
            + Cc * (MM.submatrix ρ (fun j : Jt => (j : Fin n))) := by
            rw [← Matrix.mul_assoc (MM.submatrix ρ id) E Cm, hWE, hWPm]
      _ = Cc * (-(MM.submatrix ρ (fun j : Jt => (j : Fin n))))
            + Cc * (MM.submatrix ρ (fun j : Jt => (j : Fin n))) := by rw [hBCm]
      _ = 0 := by rw [← Matrix.mul_add, neg_add_cancel, Matrix.mul_zero]
  -- ### (4) the entrywise structure of `N0`
  have hEC : ∀ (i : Fin n) (j : Jt), (E * Cm) i j
      = if h : ∃ k, κ k = i then Cm h.choose j else 0 := by
    intro i j
    have hterm : ∀ k : Fin MM.rank, E i k * Cm k j = if κ k = i then Cm k j else 0 := by
      intro k
      rw [hE]
      simp only [Matrix.submatrix_apply, id_eq, Matrix.one_apply]
      by_cases h : i = κ k
      · rw [if_pos h, if_pos h.symm, one_mul]
      · rw [if_neg h, if_neg (fun hh => h hh.symm), zero_mul]
    rw [Matrix.mul_apply]
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    by_cases h : ∃ k, κ k = i
    · rw [dif_pos h]
      refine (Finset.sum_eq_single h.choose ?_ ?_).trans (if_pos h.choose_spec)
      · intro b _ hb
        exact if_neg (fun hh => hb (hκ (hh.trans h.choose_spec.symm)))
      · intro hnot
        exact absurd (Finset.mem_univ h.choose) hnot
    · rw [dif_neg h]
      exact Finset.sum_eq_zero (fun k _ => if_neg (fun hh => h ⟨k, hh⟩))
  have hentry : ∀ (i : Fin n) (j : Jt), N0 i j
      = if h : ∃ k, κ k = i then Cm h.choose j else (if i = (j : Fin n) then 1 else 0) := by
    intro i j
    have hadd : N0 i j = (E * Cm) i j + Pm i j := by rw [hN0, Matrix.add_apply]
    have hPmval : Pm i j = if i = (j : Fin n) then 1 else 0 := by
      rw [hPm]
      simp only [Matrix.submatrix_apply, id_eq, Matrix.one_apply]
    rw [hadd, hEC, hPmval]
    by_cases h : ∃ k, κ k = i
    · have hPm0 : (if i = (j : Fin n) then (1 : ℚ) else 0) = 0 := by
        rw [if_neg]
        intro hh
        obtain ⟨k0, hk0⟩ := h
        exact j.2 ⟨k0, by rw [hk0, hh]⟩
      simp only [hPm0, add_zero, dif_pos h]
    · simp only [dif_neg h, zero_add]
  -- ### (5) the Cramer entries are ratios of two minors
  have hCm_bound : ∀ (k : Fin MM.rank) (j : Jt), bitLenRat (Cm k j) ≤ tauM MM tau := by
    intro k j
    have hD : bitLenInt (MM.num.submatrix ρ (fun b => if b = k then (j : Fin n) else κ b)).det
        ≤ MM.rank * tau + bitLenInt (MM.rank.factorial) :=
      bitLenInt_det_submatrix_le MM.num hA ρ _
    have hBz : bitLenInt (MM.num.submatrix ρ κ).det
        ≤ MM.rank * tau + bitLenInt (MM.rank.factorial) :=
      bitLenInt_det_submatrix_le MM.num hA ρ κ
    have hBz_ne : (MM.num.submatrix ρ κ).det ≠ 0 := by
      intro h0
      apply hdet
      rw [hdet_formula κ, h0]
      simp
    have hval : Cm k j
        = (((-(MM.num.submatrix ρ (fun b => if b = k then (j : Fin n) else κ b)).det : ℤ) : ℚ)
            / (((MM.num.submatrix ρ κ).det : ℤ) : ℚ)) := by
      rw [hCm]
      simp only
      rw [cramer_apply, hUpd k j,
        hdet_formula (fun b => if b = k then (j : Fin n) else κ b), hdet_formula κ]
      field_simp
      push_cast
      ring
    rw [hval]
    refine le_trans (bitLenRat_div_int_le _ _ hBz_ne) (max_le ?_ ?_)
    · rw [bitLenInt_neg]
      exact le_trans hD (rank_mul_tau_add_factorial_le_tauM MM tau)
    · exact le_trans hBz (rank_mul_tau_add_factorial_le_tauM MM tau)
  have hbound0 : ∀ (i : Fin n) (j : Jt), bitLenRat (N0 i j) ≤ tauM MM tau := by
    intro i j
    rw [hentry]
    by_cases h : ∃ k, κ k = i
    · rw [dif_pos h]
      exact hCm_bound h.choose j
    · rw [dif_neg h]
      by_cases hi : i = (j : Fin n)
      · rw [if_pos hi, bitLenRat_one]
        exact one_le_tauM MM tau
      · rw [if_neg hi, bitLenRat_zero]
        exact one_le_tauM MM tau
  -- ### (6) the columns of `N0` are linearly independent
  have hLI : LinearIndependent ℚ N0.col := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j0
    have hval := congrFun hg (j0 : Fin n)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
      Pi.zero_apply] at hval
    have hterm : ∀ j : Jt, g j * N0 (j0 : Fin n) j = if j = j0 then g j else 0 := by
      intro j
      rw [hentry (j0 : Fin n) j,
        dif_neg (show ¬∃ k, κ k = ((j0 : Jt) : Fin n) from fun hh => j0.2 hh)]
      by_cases hj : ((j0 : Fin n)) = ((j : Fin n))
      · rw [if_pos hj, if_pos (Subtype.ext hj.symm)]
        ring
      · rw [if_neg hj, if_neg (fun h : j = j0 => hj (by rw [h]))]
        ring
    have hsum : ∑ j, g j * N0 (j0 : Fin n) j = g j0 := by
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_eq_single j0]
      · rw [if_pos rfl]
      · intro b _ hb
        rw [if_neg hb]
      · intro h
        exact absurd (Finset.mem_univ j0) h
    rw [hsum] at hval
    exact hval
  have hrank0 : N0.rank = Fintype.card Jt := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hLI]
  -- ### (7) the cardinality of the complement
  have hcard : Fintype.card Jt = n - MM.rank := by
    have hrange : Fintype.card {i : Fin n // i ∈ Set.range κ} = MM.rank := by
      have h : Fintype.card (Fin MM.rank)
          = Fintype.card {i : Fin n // i ∈ Set.range κ} :=
        Fintype.card_congr (Equiv.ofBijective
          (fun k : Fin MM.rank => (⟨κ k, ⟨k, rfl⟩⟩ : {i : Fin n // i ∈ Set.range κ}))
          ⟨by
            intro a b hab
            exact hκ (Subtype.ext_iff.mp hab), by
            rintro ⟨i, hi⟩
            obtain ⟨k, hk⟩ := hi
            exact ⟨k, Subtype.ext hk⟩⟩)
      simpa using h.symm
    have hcompl : Fintype.card Jt
        = n - Fintype.card {i : Fin n // i ∈ Set.range κ} := by
      have h := Fintype.card_subtype_compl (fun i : Fin n => i ∈ Set.range κ)
      simpa [Jt] using h
    omega
  -- ### (8) reindex the columns by `Fin (n - r)`
  let ee : Jt ≃ Fin (n - MM.rank) := Fintype.equivFinOfCardEq hcard
  refine ⟨N0.submatrix id (fun t => ee.symm t), ?_, ?_, ?_⟩
  · ext a t
    have h := congrFun (congrFun hMN0 a) (ee.symm t)
    simpa [Matrix.mul_apply] using h
  · have hspan2 : Submodule.span ℚ
          (Set.range (N0.submatrix id (fun t => ee.symm t)).col)
        = Submodule.span ℚ (Set.range N0.col) := by
      apply le_antisymm
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨t, rfl⟩
        exact Submodule.subset_span ⟨ee.symm t, rfl⟩
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨j, rfl⟩
        refine Submodule.subset_span ⟨ee j, funext fun i => ?_⟩
        simp [Matrix.col_apply]
    calc (N0.submatrix id (fun t => ee.symm t)).rank
        = Module.finrank ℚ ↥(Submodule.span ℚ
            (Set.range (N0.submatrix id (fun t => ee.symm t)).col)) :=
          Matrix.rank_eq_finrank_span_cols _
      _ = Module.finrank ℚ ↥(Submodule.span ℚ (Set.range N0.col)) := by rw [hspan2]
      _ = N0.rank := (Matrix.rank_eq_finrank_span_cols N0).symm
      _ = Fintype.card Jt := hrank0
      _ = n - MM.rank := hcard
  · intro i t
    exact hbound0 i (ee.symm t)

/-! ## 4.  The annihilator `D = Nᵀ` and the combined claim -/

/-- **The columns of a kernel basis span the kernel.**  If `M * N = 0` and
`N.rank = n - r`, then the range of `N` is exactly `ker M` (both have dimension
`n - r`). -/
theorem ker_eq_range_of_kernel_basis {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ)
    (N : Matrix (Fin n) (Fin (n - MM.rank)) ℚ)
    (hMN : MM * N = 0) (hrank : N.rank = n - MM.rank) :
    LinearMap.ker MM.mulVecLin = LinearMap.range N.mulVecLin := by
  have hle : LinearMap.range N.mulVecLin ≤ LinearMap.ker MM.mulVecLin := by
    rintro _ ⟨w, rfl⟩
    show MM.mulVecLin (N.mulVecLin w) = 0
    rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hMN, Matrix.mulVecLin_zero,
      LinearMap.zero_apply]
  refine Eq.symm (Submodule.eq_of_le_of_finrank_eq hle ?_)
  have hleft : Module.finrank ℚ ↥(LinearMap.range N.mulVecLin) = n - MM.rank := by
    rw [show Module.finrank ℚ ↥(LinearMap.range N.mulVecLin) = N.rank from rfl, hrank]
  have hright : Module.finrank ℚ ↥(LinearMap.ker MM.mulVecLin) = n - MM.rank := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (f := MM.mulVecLin)
    have hdom : Module.finrank ℚ (Fin n → ℚ) = n := by simp
    have hran : Module.finrank ℚ ↥(LinearMap.range MM.mulVecLin) = MM.rank := rfl
    have hle2 : MM.rank ≤ n := Matrix.rank_le_width MM
    omega
  rw [hleft, hright]

/-- **Annihilator with bit bound.**  Transposing a kernel basis of `M` produces a
matrix whose kernel is exactly the row space of `M`: `row M ⊆ ker Nᵀ` because
`M N = 0`, and both spaces have dimension `r`. -/
theorem exists_annihilator_bounded {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ) {tau : ℕ}
    (hM : bitLenMat MM ≤ tau) :
    ∃ D : Matrix (Fin (n - MM.rank)) (Fin n) ℚ,
      LinearMap.ker D.mulVecLin = rowSpace MM ∧
        ∀ i j, bitLenRat (D i j) ≤ tauM MM tau := by
  classical
  obtain ⟨N, hMN, hrank, hbound⟩ := exists_kernel_basis_bounded MM hM
  refine ⟨Nᵀ, ?_, ?_⟩
  · -- `row M ≤ ker Nᵀ`
    have hrow : rowSpace MM ≤ LinearMap.ker Nᵀ.mulVecLin := by
      unfold rowSpace
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
      ext t
      rw [Matrix.mulVec_apply_eq_sum]
      simp only [Matrix.transpose_apply, Matrix.row, Pi.zero_apply]
      have h := congrFun (congrFun hMN a) t
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [← h]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    have hrowfin : Module.finrank ℚ ↥(rowSpace MM) = MM.rank := by
      unfold rowSpace
      rw [← Matrix.rank_eq_finrank_span_row MM]
    -- both spaces have dimension `r`
    have hfin : Module.finrank ℚ ↥(LinearMap.ker Nᵀ.mulVecLin) = MM.rank := by
      have hrn := LinearMap.finrank_range_add_finrank_ker (f := Nᵀ.mulVecLin)
      have hdom : Module.finrank ℚ (Fin n → ℚ) = n := by simp
      have hran : Module.finrank ℚ ↥(LinearMap.range Nᵀ.mulVecLin) = n - MM.rank := by
        rw [show Module.finrank ℚ ↥(LinearMap.range Nᵀ.mulVecLin) = Nᵀ.rank from rfl,
          Matrix.rank_transpose, hrank]
      have hle : MM.rank ≤ n := Matrix.rank_le_width MM
      omega
    refine Eq.symm (Submodule.eq_of_le_of_finrank_eq hrow ?_)
    rw [hrowfin, hfin]
  · intro i j
    exact hbound j i

/-- **Claim 13 (`lem:rationalbasis`), existence and bit bound.**  For a rational
matrix `M` with `bitLenMat M ≤ tau` and `r = M.rank` there are

* `N`, whose columns are a basis of `ker M` (`M * N = 0`, `N.rank = n - r`),
* `R`, whose rows are a basis of `row M` (`R.rank = r`, `rowSpace R = rowSpace M`),
* `D`, with `ker D = row M`,

all of whose entries have `bitLenRat ≤ 2 * r * ((n + 1) * tau + (r + 1).size + 1) + 1`. -/
theorem exists_rational_bases_bounded {m n : ℕ} (MM : Matrix (Fin m) (Fin n) ℚ) {tau : ℕ}
    (hM : bitLenMat MM ≤ tau) :
    ∃ (N : Matrix (Fin n) (Fin (n - MM.rank)) ℚ)
      (R : Matrix (Fin MM.rank) (Fin n) ℚ)
      (D : Matrix (Fin (n - MM.rank)) (Fin n) ℚ),
      MM * N = 0 ∧ LinearMap.ker MM.mulVecLin = LinearMap.range N.mulVecLin ∧
        N.rank = n - MM.rank ∧
        R.rank = MM.rank ∧ rowSpace R = rowSpace MM ∧
        LinearMap.ker D.mulVecLin = rowSpace MM ∧
        (∀ i j, bitLenRat (N i j) ≤ tauM MM tau) ∧
        (∀ i j, bitLenRat (R i j) ≤ tauM MM tau) ∧
        (∀ i j, bitLenRat (D i j) ≤ tauM MM tau) := by
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_kernel_basis_bounded MM hM
  obtain ⟨R, hR1, hR2, hR3⟩ := exists_row_basis_bounded MM hM
  obtain ⟨D, hD1, hD2⟩ := exists_annihilator_bounded MM hM
  exact ⟨N, R, D, hN1, ker_eq_range_of_kernel_basis MM N hN1 hN2, hN2, hR1, hR2, hD1,
    hN3, hR3, hD2⟩

end Q1Paper.PaperI
