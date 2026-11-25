
import Q1Paper.PaperI.S04_Rationality.BitLen

/-!
Q1Paper/PaperI/S04_Rationality/BitLenAdd.lean

Second bit-length module for Claim 13.  It extends `Q1Paper.PaperI.BitLen` by

* the additive growth of the rational bit length
  `bitLenRat (q₁ + q₂) ≤ 1 + bitLenRat q₁ + bitLenRat q₂` (`bitLenRat_add`),
  whose two structural ingredients are stated separately:
  `rat_add_num_natAbs_le` (the reduced numerator of a sum is dominated, in
  absolute value, by the naive numerator `q₁.num * q₂.den + q₂.num * q₁.den`) and
  `rat_add_den_le` (the reduced denominator is at most `q₁.den * q₂.den`);

* the Leibniz determinant bound `abs_det_le_factorial_mul_pow`:
  `|M.det| ≤ ω! * B ^ ω` for `M : Matrix (Fin ω) (Fin ω) ℤ` with `|M i j| ≤ B`;

* the resulting bit-length estimate `bitLenInt_det_le`:
  if `|M i j| < 2 ^ b` for all `i j`, then
  `bitLenInt M.det ≤ ω * b + bitLenInt ω!`;

* the corollary `bitLenInt_det_num_le_bitLenMat` for the cleared integer matrix
  `A.num` of a rational matrix `A`, with `b = bitLenMat A`, which instantiates
  `mat_abs_num_lt_two_pow_bitLenMat`.

Self-contained: a single `import Q1Paper.PaperI.S04_Rationality.BitLen`, no `sorry`, no new
axioms.  Check with `lake env lean Q1Paper/PaperI/BitLenAdd.lean`.
-/


open Matrix

namespace Q1Paper.PaperI

/-! ## 5.  Additive growth of the rational bit length -/

/-- Integer bit length of a natural number: `bitLenInt (n : ℤ) = n.size`. -/
theorem bitLenInt_natCast (n : ℕ) : bitLenInt (n : ℤ) = n.size := by
  simp [bitLenInt]

/-- **Numerator bound for a sum.**  The numerator of `q₁ + q₂`, in its reduced
form, is dominated in absolute value by the naive numerator
`q₁.num * q₂.den + q₂.num * q₁.den`: reduction only divides the numerator by
`gcd (q₁.num * q₂.den + q₂.num * q₁.den) (q₁.den * q₂.den)`.

Both the value and the sign are irrelevant for the bit length, so the statement
is phrased for `Int.natAbs`. -/
theorem rat_add_num_natAbs_le (q₁ q₂ : ℚ) :
    (q₁ + q₂).num.natAbs ≤ (q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ)).natAbs := by
  rw [Rat.num_add]
  set N : ℤ := q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ) with hN
  set D : ℕ := q₁.den * q₂.den with hD
  set g : ℕ := N.natAbs.gcd D with hg
  have hDpos : 0 < D := by
    rw [hD]
    exact Nat.mul_pos q₁.den_pos q₂.den_pos
  have hgpos : 0 < g := by
    rw [hg]
    exact Nat.gcd_pos_of_pos_right N.natAbs hDpos
  -- the gcd divides the naive numerator, so the division is exact
  have hgdvd : (g : ℤ) ∣ N := by
    rw [hg]
    exact Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_left N.natAbs D)
  have hcancel : N / (g : ℤ) * (g : ℤ) = N := Int.ediv_mul_cancel hgdvd
  have hnat : N.natAbs = g * (N / (g : ℤ)).natAbs := by
    conv_lhs => rw [← hcancel]
    rw [Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_comm]
  calc (N / (g : ℤ)).natAbs = 1 * (N / (g : ℤ)).natAbs := (one_mul _).symm
    _ ≤ g * (N / (g : ℤ)).natAbs := Nat.mul_le_mul_right _ hgpos
    _ = N.natAbs := hnat.symm

/-- **Denominator bound for a sum.**  The reduced denominator of `q₁ + q₂` is at
most the product of the denominators, since `(q₁ + q₂).den ∣ q₁.den * q₂.den`. -/
theorem rat_add_den_le (q₁ q₂ : ℚ) : (q₁ + q₂).den ≤ q₁.den * q₂.den := by
  rw [Rat.den_add]
  exact Nat.div_le_self _ _

/-- **Additive growth of the rational bit length**, with one extra bit for the
carry: `bitLenRat (q₁ + q₂) ≤ 1 + bitLenRat q₁ + bitLenRat q₂`.

The extra `1` is exactly the `1` of `bitLenInt_add`; the denominator needs no
extra bit, but the numerator and denominator estimates are combined by `max`. -/
theorem bitLenRat_add (q₁ q₂ : ℚ) :
    bitLenRat (q₁ + q₂) ≤ 1 + bitLenRat q₁ + bitLenRat q₂ := by
  have hnum : bitLenInt (q₁ + q₂).num ≤ 1 + bitLenRat q₁ + bitLenRat q₂ := by
    have h1 : bitLenInt (q₁ + q₂).num
        ≤ bitLenInt (q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ)) := by
      calc bitLenInt (q₁ + q₂).num = ((q₁ + q₂).num.natAbs).size := rfl
        _ ≤ ((q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ)).natAbs).size :=
            Nat.size_le_size (rat_add_num_natAbs_le q₁ q₂)
        _ = bitLenInt (q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ)) := rfl
    have h2 : bitLenInt (q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ))
        ≤ 1 + (bitLenRat q₁ + bitLenRat q₂) := by
      have hmax : max (bitLenInt (q₁.num * (q₂.den : ℤ)))
          (bitLenInt (q₂.num * (q₁.den : ℤ))) ≤ bitLenRat q₁ + bitLenRat q₂ := by
        refine max_le ?_ ?_
        · calc bitLenInt (q₁.num * (q₂.den : ℤ))
              ≤ bitLenInt q₁.num + bitLenInt (q₂.den : ℤ) := bitLenInt_mul _ _
            _ = bitLenInt q₁.num + q₂.den.size := by rw [bitLenInt_natCast]
            _ ≤ bitLenRat q₁ + bitLenRat q₂ :=
                Nat.add_le_add (bitLenInt_num_le_bitLenRat q₁) (nat_size_den_le_bitLenRat q₂)
        · calc bitLenInt (q₂.num * (q₁.den : ℤ))
              ≤ bitLenInt q₂.num + bitLenInt (q₁.den : ℤ) := bitLenInt_mul _ _
            _ = bitLenInt q₂.num + q₁.den.size := by rw [bitLenInt_natCast]
            _ ≤ bitLenRat q₂ + bitLenRat q₁ :=
                Nat.add_le_add (bitLenInt_num_le_bitLenRat q₂) (nat_size_den_le_bitLenRat q₁)
            _ = bitLenRat q₁ + bitLenRat q₂ := Nat.add_comm _ _
      calc bitLenInt (q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ))
          ≤ 1 + max (bitLenInt (q₁.num * (q₂.den : ℤ)))
              (bitLenInt (q₂.num * (q₁.den : ℤ))) := bitLenInt_add _ _
        _ ≤ 1 + (bitLenRat q₁ + bitLenRat q₂) := Nat.add_le_add_left hmax 1
    omega
  have hden : (q₁ + q₂).den.size ≤ 1 + bitLenRat q₁ + bitLenRat q₂ := by
    have h1 : (q₁ + q₂).den.size ≤ (q₁.den * q₂.den).size :=
      Nat.size_le_size (rat_add_den_le q₁ q₂)
    have h2 : (q₁.den * q₂.den).size ≤ q₁.den.size + q₂.den.size := nat_size_mul_le _ _
    have h3 : q₁.den.size + q₂.den.size ≤ bitLenRat q₁ + bitLenRat q₂ :=
      Nat.add_le_add (nat_size_den_le_bitLenRat q₁) (nat_size_den_le_bitLenRat q₂)
    omega
  show max (bitLenInt (q₁ + q₂).num) (q₁ + q₂).den.size ≤ 1 + bitLenRat q₁ + bitLenRat q₂
  exact max_le hnum hden

/-! ## 6.  The Leibniz determinant bound -/

/-- Units of `ℤ` have absolute value one, so multiplying by `±1` does not change
an absolute value.  This handles the sign factor `sign σ` in `det_apply'`. -/
theorem abs_intUnits_mul (u : ℤˣ) (x : ℤ) : |(u : ℤ) * x| = |x| := by
  have h : (u : ℤ) = 1 ∨ (u : ℤ) = -1 := by
    rcases Int.units_eq_one_or u with h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (by rw [h]; rfl)
  rcases h with h | h <;> rw [h] <;> simp

/-- **Leibniz determinant bound.**  If every entry of `M : Matrix (Fin ω) (Fin ω) ℤ`
is bounded by `B` in absolute value, then
`|M.det| ≤ ω! * B ^ ω`.

The proof expands `det M = ∑ σ, sign σ * ∏ i, M (σ i) i`, bounds every product by
`B ^ ω` (there are `ω` factors), and uses that there are `ω!` permutations.
No hypothesis on the sign of `B` is needed. -/
theorem abs_det_le_factorial_mul_pow {ω : ℕ} (M : Matrix (Fin ω) (Fin ω) ℤ) {B : ℤ}
    (hM : ∀ i j, |M i j| ≤ B) : |M.det| ≤ (ω.factorial : ℤ) * B ^ ω := by
  classical
  -- the Leibniz summand `sign σ * ∏ i, M (σ i) i` is bounded by `B ^ ω`
  have hterm : ∀ σ : Equiv.Perm (Fin ω),
      |((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ∏ i, M (σ i) i| ≤ B ^ ω := by
    intro σ
    rw [abs_intUnits_mul]
    calc |∏ i, M (σ i) i| = ∏ i, |M (σ i) i| := Finset.abs_prod _ _
      _ ≤ ∏ _i : Fin ω, B :=
          Finset.prod_le_prod₀ (f := fun i => |M (σ i) i|) (g := fun _ => B)
            (fun i _ => abs_nonneg _) (fun i _ => hM (σ i) i)
      _ = B ^ ω := by simp
  -- bound the Leibniz sum
  have hsum : |∑ σ : Equiv.Perm (Fin ω), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ∏ i, M (σ i) i|
      ≤ (ω.factorial : ℤ) * B ^ ω := by
    calc |∑ σ : Equiv.Perm (Fin ω), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ∏ i, M (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin ω),
            |((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ∏ i, M (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin ω), B ^ ω := Finset.sum_le_sum (fun σ _ => hterm σ)
      _ = (ω.factorial : ℤ) * B ^ ω := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
          exact nsmul_eq_mul _ _
  -- `det_apply'` produces the same summand with an extra `Int.cast`, harmless on `ℤ`
  rw [Matrix.det_apply']
  simpa only [Int.cast_id] using hsum

/-! ## 7.  Bit length of a determinant -/

/-- **Bit length of a determinant.**  If `|M i j| < 2 ^ b` for all entries, then
`bitLenInt M.det ≤ ω * b + bitLenInt ω!`.

Indeed `|M.det| ≤ ω! * 2 ^ (b * ω) < 2 ^ (bitLenInt ω! + b * ω)`, since
`ω! < 2 ^ bitLenInt ω!`. -/
theorem bitLenInt_det_le {ω : ℕ} (M : Matrix (Fin ω) (Fin ω) ℤ) {b : ℕ}
    (hM : ∀ i j, |M i j| < (2 : ℤ) ^ b) :
    bitLenInt M.det ≤ ω * b + bitLenInt (ω.factorial) := by
  -- Leibniz, with `B = 2 ^ b`
  have hdet : |M.det| ≤ (ω.factorial : ℤ) * (2 : ℤ) ^ (b * ω) := by
    have h := abs_det_le_factorial_mul_pow M (B := (2 : ℤ) ^ b) (fun i j => le_of_lt (hM i j))
    rwa [← pow_mul] at h
  -- the factorial is below `2 ^ bitLenInt ω!`
  have hfac : (ω.factorial : ℤ) < (2 : ℤ) ^ bitLenInt (ω.factorial) := by
    have h := bitLenInt_abs_lt (ω.factorial : ℤ)
    rwa [abs_of_nonneg (by positivity)] at h
  have hexp : bitLenInt (ω.factorial) + b * ω = ω * b + bitLenInt (ω.factorial) := by
    rw [Nat.mul_comm b ω, Nat.add_comm]
  have hlt : |M.det| < (2 : ℤ) ^ (ω * b + bitLenInt (ω.factorial)) := by
    calc |M.det| ≤ (ω.factorial : ℤ) * (2 : ℤ) ^ (b * ω) := hdet
      _ < (2 : ℤ) ^ bitLenInt (ω.factorial) * (2 : ℤ) ^ (b * ω) :=
          mul_lt_mul_of_pos_right hfac (by positivity)
      _ = (2 : ℤ) ^ (bitLenInt (ω.factorial) + b * ω) := (pow_add _ _ _).symm
      _ = (2 : ℤ) ^ (ω * b + bitLenInt (ω.factorial)) := by rw [hexp]
  rw [bitLenInt_le_iff]
  have h1 : ((M.det.natAbs : ℕ) : ℤ) < ((2 ^ (ω * b + bitLenInt (ω.factorial)) : ℕ) : ℤ) := by
    rw [← Int.abs_eq_natAbs]
    push_cast
    exact hlt
  exact_mod_cast h1

/-- **Bit length of a determinant of a cleared rational matrix.**  For
`A : Matrix (Fin ω) (Fin ω) ℚ` the integer matrix `A.num` has entries
`|A.num i j| < 2 ^ bitLenMat A`, hence
`bitLenInt A.num.det ≤ ω * bitLenMat A + bitLenInt ω!`. -/
theorem bitLenInt_det_num_le_bitLenMat {ω : ℕ} (A : Matrix (Fin ω) (Fin ω) ℚ) :
    bitLenInt A.num.det ≤ ω * bitLenMat A + bitLenInt (ω.factorial) :=
  bitLenInt_det_le A.num (fun i j => mat_abs_num_lt_two_pow_bitLenMat A i j)

end Q1Paper.PaperI
