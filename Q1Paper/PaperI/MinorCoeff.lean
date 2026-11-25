
import Q1Paper.PaperI.Claim16_Gcd
import Q1Paper.PaperI.Claim15_Arithmetic
/-!
Q1Paper/PaperI/MinorCoeff.lean

**Claim 15 (ii) of Paper I: the bit length of the COEFFICIENTS of the maximal minors
of the pencil `P(λ) = λX − G`.**

The paper's object is `pencilMinors X G : (Fin ω ↪ Fin q) → ℚ[λ]`
(`Q1Paper.pencil` composed with `Q1Paper.minors`, see `PaperI/Claim16_Gcd.lean`,
`G3Coeff.lean`, `G3LeftInverse.lean`); here the arithmetic is done on the **integer**
pencil, which is where `bitLenInt` lives, and §7 transfers the result back.

## The route: column multilinearity (NOT Cauchy–Binet)

Every entry of `λX − G` is linear in `λ`, so `det (λX_I − G_I)` is a sum of
`C(ω,d)` **mixed-column determinants**: for `S ⊆ Fin ω` with `|S| = d` the matrix
`M_{I,S}` has column `j` taken from `X` when `j ∈ S` and from `G` otherwise, and

  `[λ^d] det (λX_I − G_I) = (−1)^{ω−d} · ∑_{|S| = d} det M_{I,S}`.

Each `det M_{I,S}` is bounded by Leibniz (`bitLenInt_det_le`, i.e. `ω! · 2^{ω b}`),
and there are `Nat.choose ω d` of them.  Hence the coefficient needs the extra
`bitLenInt (Nat.choose ω d)` bits:

  `bitLenInt (coeff d) ≤ ω*b + bitLenInt (Nat.choose ω d) + bitLenInt (ω!)`.

The proof below obtains exactly this without ever formalising the subset sum: expand
`det` by Leibniz, bound each of the `ω!` permutation products by
`abs_coeff_prod_linear_le` (a sum of `C(ω,d)` monomials of magnitude `≤ B^ω`), and
add up.

**The naive bound `ω*b + bitLenInt (ω!)` is FALSE.**  Exact integer search (throwaway
script, not part of this file): with `ω = 3`, `b = 3` (entries in `[-7,7]`) some
coefficient has absolute value `4116 > 2^12 = 4096`, which is exactly the naive
limit `2^(3*3 + bitLen 6)`; the correct bound there is `3*3 + bitLen 3 + bitLen 6 = 14`
bits (`< 16384`).  With `ω = 4, b = 3` the search reaches `134456 > 2^17` against the
naive `2^17`; the correct bound is `12 + 3 + 5 = 20` bits.  So the `C(ω,d)` slot cannot
be dropped.

## Contents (no `sorry`, no `admit`, no new axioms)

* `pencilZ`, `pencilMinorZ`      : the integer pencil and its maximal minors;
* `abs_coeff_prod_linear_le`     : `|coeff d (∏ i, (a_i λ − b_i))| ≤ C(ω,d) · B^ω`
  for `|a_i|, |b_i| ≤ B` (induction on the index set; Pascal's rule supplies the count,
  so there is no `Finset.powersetCard` bookkeeping);
* `abs_coeff_det_le`             : Leibniz + triangle inequality,
  `|coeff d (det M)| ≤ ω! · (C(ω,d) · B^ω)`;
* `bitLenInt_le_of_abs_le`       : the pure `Nat`/`ℤ` step turning that magnitude bound
  into `ω*b + bitLenInt C(ω,d) + bitLenInt ω!` bits;
* `pencilMinor_coeff_bitLen_le`  : **the theorem**, for every `d` (see below);
* `pencilMinor_coeff_bitLen_le_one` : the same with the slack `+ 1`;
* `pencilMinor_coeff_bitLen_le'`    : the uniform corollary
  `≤ ω*b + ω + ω*ω.size + 1`;
* `pencilMinors_eq_map`, `pencilMinors_coeff_eq`, `pencilMinors_coeff_bitLen_le` :
  transfer to the paper's `ℚ`-pencil;
* `pencilMinor_coeff_bitLen_le_22`  : the paper's constant form `22 n³L`.

Check with
  `lake env lean Q1Paper/PaperI/MinorCoeff.lean`
-/


open Matrix Polynomial

open scoped BigOperators

namespace Q1Paper.MinorCoeff

open Q1Paper.PaperI

/-! ## 1.  The integer pencil `λX − G` and its maximal minors -/

/-- The integer pencil `λ X − G`, entrywise `C (X i j) * X − C (G i j)`.

This is the integer model of the paper's `Q1Paper.pencil` (which requires a field);
§7 identifies its image in `ℚ[λ]` with `Q1Paper.pencilMinors`. -/
noncomputable def pencilZ {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℤ) :
    Matrix (Fin q) (Fin ω) ℤ[X] :=
  fun i j => Polynomial.C (X i j) * Polynomial.X - Polynomial.C (G i j)

/-- The maximal `ω × ω` minor of the integer pencil cut out by the row embedding `e`
(all `ω` columns are used, in their natural order — this is `Q1Paper.minors`). -/
noncomputable def pencilMinorZ {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℤ)
    (e : Fin ω ↪ Fin q) : ℤ[X] :=
  ((pencilZ X G).submatrix (e : Fin ω → Fin q) id).det

/-! ## 2.  Toolbox -/

/-- `bitLenInt z ≤ b` gives the strict magnitude bound `|z| < 2^b`
(this is `Q1Paper.Claim15_Arithmetic.abs_lt_two_pow_of_bitLenInt_le_mc`). -/
theorem abs_lt_two_pow_of_bitLenInt_le_mc {z : ℤ} {b : ℕ} (h : bitLenInt z ≤ b) :
    |z| < (2 : ℤ) ^ b := by
  have h' : z.natAbs < 2 ^ b := bitLenInt_le_iff.mp h
  have h'' : ((z.natAbs : ℕ) : ℤ) < ((2 ^ b : ℕ) : ℤ) := by exact_mod_cast h'
  rw [← Int.abs_eq_natAbs] at h''
  push_cast at h''
  exact h''

/-- Converse bridge: `|z| < 2^K` gives `bitLenInt z ≤ K`. -/
theorem bitLenInt_le_of_abs_lt {z : ℤ} {K : ℕ} (h : |z| < (2 : ℤ) ^ K) :
    bitLenInt z ≤ K := by
  rw [bitLenInt_le_iff]
  have h2 : ((z.natAbs : ℕ) : ℤ) < ((2 ^ K : ℕ) : ℤ) := by
    rw [← Int.abs_eq_natAbs]
    push_cast
    exact h
  exact_mod_cast h2

/-- Coefficients are additive, in `Finset`-sum form. -/
theorem coeff_finsetSum {ι : Type*} (s : Finset ι) (g : ι → ℤ[X]) (d : ℕ) :
    (Finset.sum s g).coeff d = Finset.sum s (fun i => (g i).coeff d) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, Polynomial.coeff_add, ih]

/-! ## 3.  The coefficient of a product of linear forms -/

/-- **Product bound.**  For `|a i|, |b i| ≤ B` on `s`, the coefficient of `λ^d` in
`∏ i ∈ s, (a i · λ − b i)` is a sum of `Nat.choose s.card d` monomials, each of
magnitude at most `B ^ s.card`; hence

  `|coeff d| ≤ Nat.choose s.card d * B ^ s.card`.

Induction on `s`; Pascal's rule `Nat.choose_succ_succ'` supplies the binomial count,
so no `Finset.powersetCard` bookkeeping is needed. -/
theorem abs_coeff_prod_linear_le {ι : Type*} (a b : ι → ℤ) {B : ℤ} (hB : 0 ≤ B) :
    ∀ (s : Finset ι) (d : ℕ), (∀ i ∈ s, |a i| ≤ B) → (∀ i ∈ s, |b i| ≤ B) →
      |(Finset.prod s fun i => Polynomial.C (a i) * Polynomial.X - Polynomial.C (b i)).coeff d|
        ≤ (Nat.choose s.card d : ℤ) * B ^ s.card := by
  classical
  intro s
  induction s using Finset.induction with
  | empty =>
      intro d _ _
      rcases d with _ | k
      · simp
      · simp [Nat.choose_eq_zero_of_lt (Nat.succ_pos k), Polynomial.coeff_one]
  | insert x s hx ih =>
      intro d ha hb
      have hax : |a x| ≤ B := ha x (Finset.mem_insert_self x s)
      have hbx : |b x| ≤ B := hb x (Finset.mem_insert_self x s)
      have ha' : ∀ i ∈ s, |a i| ≤ B := fun i hi => ha i (Finset.mem_insert_of_mem hi)
      have hb' : ∀ i ∈ s, |b i| ≤ B := fun i hi => hb i (Finset.mem_insert_of_mem hi)
      set P : ℤ[X] := Finset.prod s
        (fun i => Polynomial.C (a i) * Polynomial.X - Polynomial.C (b i)) with hP
      rw [Finset.prod_insert hx, Finset.card_insert_of_notMem hx]
      have hcoef : ((Polynomial.C (a x) * Polynomial.X - Polynomial.C (b x)) * P).coeff d
          = a x * (Polynomial.X * P).coeff d - b x * P.coeff d := by
        rw [sub_mul, mul_assoc, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_C_mul]
      rcases d with _ | k
      · -- `d = 0`: only the constant parts survive
        rw [hcoef, Polynomial.coeff_X_mul_zero, mul_zero, zero_sub]
        have h1 : |P.coeff 0| ≤ B ^ s.card := by
          have h := ih 0 ha' hb'
          simpa [Nat.choose_zero_right] using h
        rw [Nat.choose_zero_right, Nat.cast_one, one_mul, pow_succ]
        calc |-(b x * P.coeff 0)| = |b x| * |P.coeff 0| := by rw [abs_neg, abs_mul]
          _ ≤ B * B ^ s.card := mul_le_mul hbx h1 (abs_nonneg _) hB
          _ = B ^ s.card * B := by ring
      · -- `d = k + 1`: Pascal's rule
        rw [hcoef, Polynomial.coeff_X_mul]
        have h1 : |P.coeff k| ≤ (Nat.choose s.card k : ℤ) * B ^ s.card := ih k ha' hb'
        have h2 : |P.coeff (k + 1)| ≤ (Nat.choose s.card (k + 1) : ℤ) * B ^ s.card :=
          ih (k + 1) ha' hb'
        have htri : |a x * P.coeff k - b x * P.coeff (k + 1)|
            ≤ |a x| * |P.coeff k| + |b x| * |P.coeff (k + 1)| := by
          rw [← abs_mul, ← abs_mul]
          have h := Int.natAbs_add_le (a x * P.coeff k) (-(b x * P.coeff (k + 1)))
          rw [Int.natAbs_neg] at h
          calc |a x * P.coeff k - b x * P.coeff (k + 1)|
              = ((((a x * P.coeff k) + -(b x * P.coeff (k + 1))).natAbs : ℕ) : ℤ) := by
                rw [sub_eq_add_neg, Int.abs_eq_natAbs]
            _ ≤ ((((a x * P.coeff k).natAbs + (b x * P.coeff (k + 1)).natAbs : ℕ)) : ℤ) := by
                exact_mod_cast h
            _ = |a x * P.coeff k| + |b x * P.coeff (k + 1)| := by
                rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
                push_cast
                ring
        have hstep : |a x| * |P.coeff k| + |b x| * |P.coeff (k + 1)|
            ≤ B * ((Nat.choose s.card k : ℤ) * B ^ s.card)
              + B * ((Nat.choose s.card (k + 1) : ℤ) * B ^ s.card) :=
          add_le_add (mul_le_mul hax h1 (abs_nonneg _) hB)
            (mul_le_mul hbx h2 (abs_nonneg _) hB)
        have heq : B * ((Nat.choose s.card k : ℤ) * B ^ s.card)
            + B * ((Nat.choose s.card (k + 1) : ℤ) * B ^ s.card)
            = ((Nat.choose (s.card + 1) (k + 1) : ℕ) : ℤ) * B ^ (s.card + 1) := by
          rw [Nat.choose_succ_succ', Nat.cast_add, pow_succ]
          ring
        exact le_trans htri (le_trans hstep (le_of_eq heq))

/-! ## 4.  The coefficient of a determinant of linear forms -/

/-- **Determinant bound.**  If every entry of `M` is of the form `a λ − b` with
`|a|, |b| ≤ B`, then

  `|coeff d M.det| ≤ ω! · (Nat.choose ω d · B^ω)`

(Leibniz over the `ω!` permutations, the product bound of §3 for each permutation term,
and the triangle inequality). -/
theorem abs_coeff_det_le {ω : ℕ} (M : Matrix (Fin ω) (Fin ω) ℤ[X])
    (a b : Fin ω → Fin ω → ℤ)
    (hM : ∀ i j, M i j = Polynomial.C (a i j) * Polynomial.X - Polynomial.C (b i j))
    {B : ℤ} (ha : ∀ i j, |a i j| ≤ B) (hb : ∀ i j, |b i j| ≤ B) (hB : 0 ≤ B) (d : ℕ) :
    |M.det.coeff d| ≤ (ω.factorial : ℤ) * ((Nat.choose ω d : ℤ) * B ^ ω) := by
  classical
  set term : Equiv.Perm (Fin ω) → ℤ[X] :=
    fun σ => ((((Equiv.Perm.sign σ : ℤˣ)) : ℤ[X])) * ∏ i, M (σ i) i with hterm
  have hdet : M.det = ∑ σ : Equiv.Perm (Fin ω), term σ := by
    rw [hterm]
    exact Matrix.det_apply' M
  have hterm_bound : ∀ σ : Equiv.Perm (Fin ω),
      |(term σ).coeff d| ≤ (Nat.choose ω d : ℤ) * B ^ ω := by
    intro σ
    have hcast : ((((Equiv.Perm.sign σ : ℤˣ)) : ℤ[X]))
        = Polynomial.C ((((Equiv.Perm.sign σ : ℤˣ)) : ℤ)) := by simp
    have hprod : (∏ i, M (σ i) i)
        = ∏ i, (Polynomial.C (a (σ i) i) * Polynomial.X - Polynomial.C (b (σ i) i)) :=
      Finset.prod_congr rfl fun i _ => hM (σ i) i
    rw [hterm]
    simp only
    rw [hcast, Polynomial.coeff_C_mul, hprod, abs_intUnits_mul]
    simpa using
      abs_coeff_prod_linear_le (fun i => a (σ i) i) (fun i => b (σ i) i) hB Finset.univ d
        (fun i _ => ha (σ i) i) (fun i _ => hb (σ i) i)
  rw [hdet, coeff_finsetSum]
  calc |∑ σ : Equiv.Perm (Fin ω), (term σ).coeff d|
      ≤ ∑ σ : Equiv.Perm (Fin ω), |(term σ).coeff d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin ω), (Nat.choose ω d : ℤ) * B ^ ω :=
        Finset.sum_le_sum fun σ _ => hterm_bound σ
    _ = (ω.factorial : ℤ) * ((Nat.choose ω d : ℤ) * B ^ ω) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
        exact nsmul_eq_mul _ _

/-! ## 5.  From a magnitude bound to a `bitLenInt` bound -/

/-- **The pure arithmetic step.**  If `|z| ≤ F · (N · 2^{bω})` then

  `bitLenInt z ≤ ω*b + bitLenInt N + bitLenInt F`,

the strict inequalities `N < 2^{bitLenInt N}` and `F < 2^{bitLenInt F}` absorbing both
factors exactly (this is where the sharpness comes from: no bit is spent on the
summation count). -/
theorem bitLenInt_le_of_abs_le {z : ℤ} {N F b ω : ℕ}
    (h : |z| ≤ (F : ℤ) * ((N : ℤ) * (2 : ℤ) ^ (b * ω))) :
    bitLenInt z ≤ ω * b + bitLenInt (N : ℤ) + bitLenInt (F : ℤ) := by
  have hP : (0 : ℤ) < (2 : ℤ) ^ (b * ω) := by positivity
  have hc : (0 : ℤ) ≤ (N : ℤ) * (2 : ℤ) ^ (b * ω) := by positivity
  have hFle : (F : ℤ) ≤ ((2 ^ F.size : ℕ) : ℤ) := by
    exact_mod_cast le_of_lt (Nat.lt_size_self F)
  have hNlt : (N : ℤ) < ((2 ^ N.size : ℕ) : ℤ) := by
    exact_mod_cast Nat.lt_size_self N
  have hstep1 : (F : ℤ) * ((N : ℤ) * (2 : ℤ) ^ (b * ω))
      ≤ ((2 ^ F.size : ℕ) : ℤ) * ((N : ℤ) * (2 : ℤ) ^ (b * ω)) :=
    mul_le_mul_of_nonneg_right hFle hc
  have hNP : (N : ℤ) * (2 : ℤ) ^ (b * ω)
      < ((2 ^ N.size : ℕ) : ℤ) * (2 : ℤ) ^ (b * ω) :=
    mul_lt_mul_of_pos_right hNlt hP
  have hstep2 : ((2 ^ F.size : ℕ) : ℤ) * ((N : ℤ) * (2 : ℤ) ^ (b * ω))
      < ((2 ^ F.size : ℕ) : ℤ) * (((2 ^ N.size : ℕ) : ℤ) * (2 : ℤ) ^ (b * ω)) :=
    mul_lt_mul_of_pos_left hNP (by positivity)
  have hexp : ((2 ^ F.size : ℕ) : ℤ) * (((2 ^ N.size : ℕ) : ℤ) * (2 : ℤ) ^ (b * ω))
      = (2 : ℤ) ^ (ω * b + N.size + F.size) := by
    push_cast
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have hlt : |z| < (2 : ℤ) ^ (ω * b + N.size + F.size) := by
    calc |z| ≤ (F : ℤ) * ((N : ℤ) * (2 : ℤ) ^ (b * ω)) := h
      _ ≤ ((2 ^ F.size : ℕ) : ℤ) * ((N : ℤ) * (2 : ℤ) ^ (b * ω)) := hstep1
      _ < ((2 ^ F.size : ℕ) : ℤ) * (((2 ^ N.size : ℕ) : ℤ) * (2 : ℤ) ^ (b * ω)) := hstep2
      _ = (2 : ℤ) ^ (ω * b + N.size + F.size) := hexp
  rw [bitLenInt_natCast, bitLenInt_natCast]
  exact bitLenInt_le_of_abs_lt hlt

/-! ## 6.  The main theorem: coefficients of the maximal minors of `λX − G` -/

/-- **Claim 15 (ii): the coefficients of the maximal minors of the pencil.**
For integer `X G` whose entries all have bit length at most `b`, every coefficient of
every maximal `ω × ω` minor of `λX − G` has at most

  `ω*b + bitLenInt (Nat.choose ω d) + bitLenInt (ω!)`

bits.  No hypothesis on `d` is needed: for `d > ω` the coefficient vanishes *and*
`Nat.choose ω d = 0`, so both sides degenerate (the sharp statement is thus
`∀ d`, of which the paper's `∀ d ≤ ω` is the case of interest).  The `Nat.choose ω d`
slot is the number of mixed-column determinants in the coefficient and cannot be
removed — see the counterexample in the file header. -/
theorem pencilMinor_coeff_bitLen_le {q ω b : ℕ} (X G : Matrix (Fin q) (Fin ω) ℤ)
    (hX : ∀ i j, bitLenInt (X i j) ≤ b) (hG : ∀ i j, bitLenInt (G i j) ≤ b)
    (e : Fin ω ↪ Fin q) (d : ℕ) :
    bitLenInt ((pencilMinorZ X G e).coeff d)
      ≤ ω * b + bitLenInt (Nat.choose ω d) + bitLenInt (ω.factorial) := by
  have hB : (0 : ℤ) ≤ (2 : ℤ) ^ b := by positivity
  have ha : ∀ i j, |X (e i) j| ≤ (2 : ℤ) ^ b :=
    fun i j => le_of_lt (abs_lt_two_pow_of_bitLenInt_le_mc (hX (e i) j))
  have hb : ∀ i j, |G (e i) j| ≤ (2 : ℤ) ^ b :=
    fun i j => le_of_lt (abs_lt_two_pow_of_bitLenInt_le_mc (hG (e i) j))
  have hmain := abs_coeff_det_le ((pencilZ X G).submatrix (e : Fin ω → Fin q) id)
    (fun i j => X (e i) j) (fun i j => G (e i) j)
    (fun i j => by simp [Matrix.submatrix_apply, pencilZ]) ha hb hB d
  rw [← pow_mul] at hmain
  exact bitLenInt_le_of_abs_le hmain

/-- The same statement with one bit of slack. -/
theorem pencilMinor_coeff_bitLen_le_one {q ω b : ℕ} (X G : Matrix (Fin q) (Fin ω) ℤ)
    (hX : ∀ i j, bitLenInt (X i j) ≤ b) (hG : ∀ i j, bitLenInt (G i j) ≤ b)
    (e : Fin ω ↪ Fin q) (d : ℕ) :
    bitLenInt ((pencilMinorZ X G e).coeff d)
      ≤ ω * b + bitLenInt (Nat.choose ω d) + bitLenInt (ω.factorial) + 1 := by
  have h := pencilMinor_coeff_bitLen_le X G hX hG e d
  omega

/-- **Uniform corollary**: for `1 ≤ ω`, the `Nat.choose ω d` slot is at most `ω` bits
(`Nat.choose_lt_two_pow`) and `bitLenInt ω! ≤ ω * ω.size + 1`
(`bitLenInt_factorial_le`), hence (for every `d`)

  `bitLenInt (coeff d) ≤ ω*b + ω + ω * ω.size + 1`. -/
theorem pencilMinor_coeff_bitLen_le' {q ω b : ℕ} (X G : Matrix (Fin q) (Fin ω) ℤ)
    (hX : ∀ i j, bitLenInt (X i j) ≤ b) (hG : ∀ i j, bitLenInt (G i j) ≤ b)
    (e : Fin ω ↪ Fin q) (hω : 1 ≤ ω) (d : ℕ) :
    bitLenInt ((pencilMinorZ X G e).coeff d) ≤ ω * b + ω + ω * ω.size + 1 := by
  have h := pencilMinor_coeff_bitLen_le X G hX hG e d
  have hN : bitLenInt (Nat.choose ω d) ≤ ω := by
    rw [bitLenInt_natCast, Nat.size_le]
    exact Nat.choose_lt_two_pow ω d hω
  have hF : bitLenInt (ω.factorial) ≤ ω * ω.size + 1 := bitLenInt_factorial_le ω
  omega

/-! ## 7.  Transfer to the paper's `ℚ`-pencil -/

/-- The integer pencil, mapped to `ℚ[λ]`, is the paper's pencil `Q1Paper.pencil`. -/
theorem pencilZ_map {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℤ) :
    (pencilZ X G).map (Polynomial.map (algebraMap ℤ ℚ))
      = Q1Paper.pencil (X.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ)) := by
  funext i j
  rw [Matrix.map_apply, Q1Paper.pencil_apply, pencilZ]
  simp

/-- The maximal minor of the paper's `ℚ`-pencil is the image of the integer minor. -/
theorem pencilMinors_eq_map {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℤ)
    (e : Fin ω ↪ Fin q) :
    Q1Paper.pencilMinors (X.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ)) e
      = (pencilMinorZ X G e).map (algebraMap ℤ ℚ) := by
  have hmat : (((pencilZ X G).submatrix (e : Fin ω → Fin q) id).map
        (Polynomial.map (algebraMap ℤ ℚ)))
      = (Q1Paper.pencil (X.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ))).submatrix
          (e : Fin ω → Fin q) id := by
    funext i j
    rw [Matrix.map_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
      Q1Paper.pencil_apply, pencilZ]
    simp
  have h := RingHom.map_det (Polynomial.mapRingHom (algebraMap ℤ ℚ))
    ((pencilZ X G).submatrix (e : Fin ω → Fin q) id)
  rw [show (Polynomial.mapRingHom (algebraMap ℤ ℚ)).mapMatrix
        ((pencilZ X G).submatrix (e : Fin ω → Fin q) id)
      = ((pencilZ X G).submatrix (e : Fin ω → Fin q) id).map
          (Polynomial.map (algebraMap ℤ ℚ)) from rfl, hmat] at h
  simp only [Q1Paper.pencilMinors, Q1Paper.minors, pencilMinorZ]
  exact h.symm

/-- The coefficients of the paper's `ℚ`-minor are the images of the integer ones. -/
theorem pencilMinors_coeff_eq {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℤ)
    (e : Fin ω ↪ Fin q) (d : ℕ) :
    (Q1Paper.pencilMinors (X.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ)) e).coeff d
      = (((pencilMinorZ X G e).coeff d : ℤ) : ℚ) := by
  rw [pencilMinors_eq_map, Polynomial.coeff_map]
  rfl

/-- **The paper's statement.**  For the `ℚ`-pencil `λX − G` built from integer data,
every coefficient of every maximal minor is the image of an integer whose bit length is
at most `ω*b + bitLenInt (Nat.choose ω d) + bitLenInt (ω!)`. -/
theorem pencilMinors_coeff_bitLen_le {q ω b : ℕ} (X G : Matrix (Fin q) (Fin ω) ℤ)
    (hX : ∀ i j, bitLenInt (X i j) ≤ b) (hG : ∀ i j, bitLenInt (G i j) ≤ b)
    (e : Fin ω ↪ Fin q) (d : ℕ) :
    ∃ c : ℤ,
      (Q1Paper.pencilMinors (X.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ)) e).coeff d
        = (c : ℚ) ∧
      bitLenInt c ≤ ω * b + bitLenInt (Nat.choose ω d) + bitLenInt (ω.factorial) :=
  ⟨(pencilMinorZ X G e).coeff d, pencilMinors_coeff_eq X G e d,
    pencilMinor_coeff_bitLen_le X G hX hG e d⟩

/-! ## 8.  The paper's constant form `22 n³L` -/

/-- `n ≤ n ^ 3` for `1 ≤ n`. -/
theorem le_cube {n : ℕ} (hn : 1 ≤ n) : n ≤ n ^ 3 := by
  calc n = n * 1 := by ring
    _ ≤ n * n := by simpa using Nat.mul_le_mul_left n hn
    _ = n ^ 2 := by ring
    _ ≤ n ^ 2 * n := by simpa using Nat.mul_le_mul_left (n ^ 2) hn
    _ = n ^ 3 := by ring

/-- `n ^ 2 ≤ n ^ 3` for `1 ≤ n`. -/
theorem sq_le_cube {n : ℕ} (hn : 1 ≤ n) : n ^ 2 ≤ n ^ 3 := by
  calc n ^ 2 = n ^ 2 * 1 := by ring
    _ ≤ n ^ 2 * n := by simpa using Nat.mul_le_mul_left (n ^ 2) hn
    _ = n ^ 3 := by ring

/-- `1 ≤ n ^ 3` for `1 ≤ n`. -/
theorem one_le_cube {n : ℕ} (hn : 1 ≤ n) : 1 ≤ n ^ 3 := by
  calc (1 : ℕ) = 1 * 1 := by ring
    _ ≤ n * n := Nat.mul_le_mul hn hn
    _ ≤ n * n * n := by simpa using Nat.mul_le_mul_left (n * n) hn
    _ = n ^ 3 := by ring

/-- **The paper's constant form.**  If the entries of `X` and `G` have bit length at
most `18 n²L`, `1 ≤ ω ≤ n` and `n ≤ L`, then every coefficient of every maximal minor
has at most `22 n³L` bits — the same constant as `bMinor_bitLen_le_22`
(`PaperI/Claim15_Arithmetic.lean`), the `C(ω,d)` slot being absorbed into the `4 n³L` slack. -/
theorem pencilMinor_coeff_bitLen_le_22 {q ω n L : ℕ} (X G : Matrix (Fin q) (Fin ω) ℤ)
    (hX : ∀ i j, bitLenInt (X i j) ≤ 18 * n ^ 2 * L)
    (hG : ∀ i j, bitLenInt (G i j) ≤ 18 * n ^ 2 * L)
    (e : Fin ω ↪ Fin q) (hω : 1 ≤ ω) (hωn : ω ≤ n) (hn : 1 ≤ n) (hL : n ≤ L)
    (d : ℕ) :
    bitLenInt ((pencilMinorZ X G e).coeff d) ≤ 22 * n ^ 3 * L := by
  have h := pencilMinor_coeff_bitLen_le X G hX hG e d
  have h1 : bitLenInt (Nat.choose ω d) ≤ n := by
    rw [bitLenInt_natCast, Nat.size_le]
    calc Nat.choose ω d < 2 ^ ω := Nat.choose_lt_two_pow ω d hω
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hωn
  have h2 : bitLenInt (ω.factorial) ≤ n * n + 1 := by
    have hf := bitLenInt_factorial_le ω
    have hs : ω.size ≤ n := by
      calc ω.size ≤ n.size := Nat.size_le_size hωn
        _ ≤ n := Q1Paper.Claim15_Arithmetic.nat_size_le_self n
    have hmul : ω * ω.size ≤ n * n := by
      calc ω * ω.size ≤ ω * n := Nat.mul_le_mul_left _ hs
        _ ≤ n * n := Nat.mul_le_mul_right n hωn
    omega
  have hA : ω * (18 * n ^ 2 * L) ≤ 18 * (n ^ 3 * L) := by
    calc ω * (18 * n ^ 2 * L) ≤ n * (18 * n ^ 2 * L) := Nat.mul_le_mul_right _ hωn
      _ = 18 * (n ^ 3 * L) := by ring
  have hL1 : 1 ≤ L := le_trans hn hL
  have hcube : n ^ 3 ≤ n ^ 3 * L := by
    simpa using Nat.mul_le_mul_left (n ^ 3) hL1
  have hB : n + n ^ 2 + 1 ≤ 4 * (n ^ 3 * L) := by
    have h1' := le_cube hn
    have h2' := sq_le_cube hn
    have h3' := one_le_cube hn
    nlinarith [hcube, h1', h2', h3']
  nlinarith [h, h1, h2, hA, hB]

end Q1Paper.MinorCoeff

/-! ## Axiom audit -/

