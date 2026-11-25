
import Q1Paper.PaperI.S05_Complexity.BareissBase

/-!
Q1Paper/PaperI/S04_Rationality/Claim15_Arithmetic.lean

Claim 15(iv) of the paper: the **arithmetic skeleton** of the bit-length bound
for the coefficients of the cleared system `Phi_{omega,J}`.

This file deliberately does *not* formalise the paper's objects (the pivot block
`X`, the block `G`, the maximal-minor matrix `Z`, the Gram matrix `S = ZᵀZ`, or
the coefficient `b` of `Phi_{omega,J}`).  It isolates the pure `Nat` counting
chain, so that the paper's explicit constants can be checked mechanically:

* §1  generic bit-length arithmetic for `bitLenInt`:
      `bitLenInt (x * y) ≤ b1 + b2`, `bitLenInt (x + y) ≤ 1 + max b1 b2`,
      the difference version, finite sums and finite bilinear sums (the shape of
      a Gram entry `∑ k, Z k i * Z k j`), and the bridge
      `bitLenInt z ≤ b → |z| < 2 ^ b`;
* §2  the numeric side conditions, stated as **hypothesis-free** inequalities on
      the explicit constants `18, 20, 22, 24, 47, 240` (with the exact side
      conditions each one needs);
* §3  the conditional links of the chain, each a standalone theorem:
      `18 n²L` entries → `22 n³L` maximal minors (the `4 n³L` slack absorbs
      `bitLenInt ω!`), `22 n³L` minor coefficients → `47 n³L` Gram entries
      (`44 n³L + 3 n³L`), and `47 n³L` Gram entries → `240 q n⁵L` coefficients.

Side conditions used everywhere: `1 ≤ n` (i.e. `0 < n`), `1 ≤ q` (i.e. `0 < q`)
and `n ≤ L`.  No `L ≥ 2` hypothesis is needed; when `n = 1` the chain is still
valid (`L = 1` is allowed), and when `n ≥ 2` it is implied by `n ≤ L`.

No `sorry`, no `admit`, no new axioms.  Check with
  lake env lean Q1Paper/PaperI/Claim15_Arithmetic.lean
-/


open Matrix

open scoped BigOperators

namespace Q1Paper.Claim15_Arithmetic

open Q1Paper.PaperI

/-! ## 1.  Generic bit-length arithmetic -/

/-- **Multiplicative growth, with explicit bounds.**  If `x` and `y` have at
most `b1`, resp. `b2`, bits, then `x * y` has at most `b1 + b2` bits. -/
theorem bitLenInt_mul_le {x y : ℤ} {b1 b2 : ℕ}
    (hx : bitLenInt x ≤ b1) (hy : bitLenInt y ≤ b2) :
    bitLenInt (x * y) ≤ b1 + b2 := by
  have h := bitLenInt_mul x y
  omega

/-- **Additive growth, with explicit bounds.**  One extra bit for the carry. -/
theorem bitLenInt_add_le {x y : ℤ} {b1 b2 : ℕ}
    (hx : bitLenInt x ≤ b1) (hy : bitLenInt y ≤ b2) :
    bitLenInt (x + y) ≤ 1 + max b1 b2 := by
  have h := bitLenInt_add x y
  omega

/-- **Subtractive growth, with explicit bounds.** -/
theorem bitLenInt_sub_le {x y : ℤ} {b1 b2 : ℕ}
    (hx : bitLenInt x ≤ b1) (hy : bitLenInt y ≤ b2) :
    bitLenInt (x - y) ≤ 1 + max b1 b2 := by
  have h := bitLenInt_sub x y
  omega

/-- **Bridge to the magnitude bound.**  `bitLenInt z ≤ b` is exactly
`|z| < 2 ^ b`; this is the form consumed by `bitLenInt_det_le` /
`bitLenInt_bMinor_le`. -/
theorem abs_lt_two_pow_of_bitLenInt_le {z : ℤ} {b : ℕ} (h : bitLenInt z ≤ b) :
    |z| < (2 : ℤ) ^ b := by
  have h' : z.natAbs < 2 ^ b := (bitLenInt_le_iff).mp h
  have h'' : (z.natAbs : ℤ) < ((2 ^ b : ℕ) : ℤ) := by exact_mod_cast h'
  rw [← Int.abs_eq_natAbs] at h''
  push_cast at h''
  exact h''

/-- **A finite sum**, with a per-term bit bound.  The `s.card` term is the crude
cost of adding `s.card` summands; no logarithm of the cardinality is needed. -/
theorem bitLenInt_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) (b : ι → ℕ)
    (h : ∀ i ∈ s, bitLenInt (f i) ≤ b i) :
    bitLenInt (s.sum f) ≤ s.card + s.sum b := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha (f := f), Finset.sum_insert ha (f := b),
        Finset.card_insert_of_notMem ha]
      have hfa : bitLenInt (f a) ≤ b a := h a (Finset.mem_insert_self a s)
      have hrest : bitLenInt (s.sum f) ≤ s.card + s.sum b :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hstep :
          bitLenInt (f a + s.sum f) ≤ (s.card + 1) + (b a + s.sum b) := by
        calc bitLenInt (f a + s.sum f)
            ≤ 1 + max (bitLenInt (f a)) (bitLenInt (s.sum f)) := bitLenInt_add _ _
          _ ≤ 1 + max (b a) (s.card + s.sum b) :=
              Nat.add_le_add_left (max_le_max hfa hrest) 1
          _ ≤ (s.card + 1) + (b a + s.sum b) := by omega
      exact hstep

/-- `Finset.univ` form of `bitLenInt_sum_le`. -/
theorem bitLenInt_sum_le_univ {ι : Type*} [Fintype ι] (f : ι → ℤ) (b : ι → ℕ)
    (h : ∀ i, bitLenInt (f i) ≤ b i) :
    bitLenInt (Finset.univ.sum f) ≤ Fintype.card ι + Finset.univ.sum b := by
  have h' := bitLenInt_sum_le (Finset.univ) f b (fun i _ => h i)
  simpa using h'

/-- **A finite bilinear sum**, with a common bit bound on each factor.  This is
the shape of a Gram entry `S i j = ∑ k, Z k i * Z k j` (with `ι = Fin (2ω)`) and
of a `q`-term coefficient (with `ι = Fin q`). -/
theorem bitLenInt_sum_mul_le {ι : Type*} (s : Finset ι) (f g : ι → ℤ) (bf bg : ℕ)
    (hf : ∀ i ∈ s, bitLenInt (f i) ≤ bf) (hg : ∀ i ∈ s, bitLenInt (g i) ≤ bg) :
    bitLenInt (s.sum fun i => f i * g i) ≤ s.card + bf + bg := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have hfa : bitLenInt (f a * g a) ≤ bf + bg :=
        bitLenInt_mul_le (hf a (Finset.mem_insert_self a s))
          (hg a (Finset.mem_insert_self a s))
      have hrest : bitLenInt (s.sum fun i => f i * g i) ≤ s.card + bf + bg :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      have hadd := bitLenInt_add (f a * g a) (s.sum fun i => f i * g i)
      have hmax : max (bitLenInt (f a * g a)) (bitLenInt (s.sum fun i => f i * g i))
          ≤ s.card + bf + bg := by
        refine max_le ?_ hrest
        omega
      omega

/-- `Finset.univ` form of `bitLenInt_sum_mul_le`. -/
theorem bitLenInt_sum_mul_le_univ {ι : Type*} [Fintype ι] (f g : ι → ℤ) (bf bg : ℕ)
    (hf : ∀ i, bitLenInt (f i) ≤ bf) (hg : ∀ i, bitLenInt (g i) ≤ bg) :
    bitLenInt (Finset.univ.sum fun i => f i * g i) ≤ Fintype.card ι + bf + bg := by
  have h' := bitLenInt_sum_mul_le (Finset.univ) f g bf bg
    (fun i _ => hf i) (fun i _ => hg i)
  simpa using h'

/-! ## 2.  The numeric side conditions (hypothesis-free constant checks) -/

/-- `Nat.size n ≤ n` (used for the `ω!` term of the determinant bound). -/
theorem nat_size_le_self (n : ℕ) : n.size ≤ n := by
  rw [Nat.size_le]
  exact Nat.lt_two_pow_self

/-- `1 ≤ n ^ k` for `1 ≤ n`. -/
theorem one_le_pow_nat {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : 1 ≤ n ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      calc (1 : ℕ) = 1 * 1 := (one_mul 1).symm
        _ ≤ n ^ k * n := Nat.mul_le_mul ih hn

/-- `n ^ 2 ≤ n ^ 4` for `1 ≤ n`. -/
theorem sq_le_fourth {n : ℕ} (hn : 1 ≤ n) : n ^ 2 ≤ n ^ 4 := by
  have h2 : 1 ≤ n ^ 2 := one_le_pow_nat hn 2
  calc n ^ 2 = n ^ 2 * 1 := by ring
    _ ≤ n ^ 2 * n ^ 2 := Nat.mul_le_mul_left _ h2
    _ = n ^ 4 := by ring

/-- `n ^ 4 ≤ n ^ 3 * L` for `n ≤ L` (the `L`-scaling of one power of `n`). -/
theorem fourth_le_cube_mul {n L : ℕ} (hL : n ≤ L) : n ^ 4 ≤ n ^ 3 * L := by
  calc n ^ 4 = n ^ 3 * n := by ring
    _ ≤ n ^ 3 * L := Nat.mul_le_mul_left _ hL

/-- `n ≤ n ^ 4` for `1 ≤ n`. -/
theorem le_fourth {n : ℕ} (hn : 1 ≤ n) : n ≤ n ^ 4 := by
  have h3 : 1 ≤ n ^ 3 := one_le_pow_nat hn 3
  calc n = n * 1 := by ring
    _ ≤ n * n ^ 3 := Nat.mul_le_mul_left _ h3
    _ = n ^ 4 := by ring

/-- **The factorial slot**: `n * n + 1 ≤ 4 n³ L`, the `4 n³L` that, added to
`18 n³L`, produces the paper's `22 n³L`.  It dominates
`bitLenInt ω! ≤ ω * ω.size + 1 ≤ n * n + 1`. -/
theorem factorialSlot_le {n L : ℕ} (hn : 1 ≤ n) (hL : n ≤ L) :
    n * n + 1 ≤ 4 * n ^ 3 * L := by
  have h24 : n ^ 2 ≤ n ^ 4 := sq_le_fourth hn
  have h45 : n ^ 4 ≤ n ^ 3 * L := fourth_le_cube_mul hL
  have h1 : 1 ≤ n ^ 2 := one_le_pow_nat hn 2
  have hnn : n * n = n ^ 2 := by ring
  nlinarith

/-- **The `18 → 22` step.**  A `ω × ω` minor with `ω ≤ n`, whose entries have
bit length at most `18 n²L`, has bit length at most `22 n³L`:
`18 n³L` for the `ω` entries plus `4 n³L` for `bitLenInt ω!`. -/
theorem minorBound_22 {n L ω : ℕ} (hω : ω ≤ n) (hn : 1 ≤ n) (hL : n ≤ L) :
    ω * (18 * n ^ 2 * L) + (n * n + 1) ≤ 22 * n ^ 3 * L := by
  have h1 : ω * (18 * n ^ 2 * L) ≤ 18 * (n ^ 3 * L) := by
    calc ω * (18 * n ^ 2 * L) ≤ n * (18 * n ^ 2 * L) := Nat.mul_le_mul_right _ hω
      _ = 18 * (n ^ 3 * L) := by ring
  have h2 : n * n + 1 ≤ 4 * n ^ 3 * L := factorialSlot_le hn hL
  nlinarith

/-- **The `20 → 22` step, i.e. the paper's own arithmetic.**  A `ω × ω` minor whose
entries have bit length at most `20 n²L` (the `G`-block bound) is still at most
`22 n³L`, because the `bitLenInt ω!` slot only needs `2 n³L` here: `20 n³L` for the
`ω` entries plus `2 n³L` for the factorial.  This is the step used in the proof of
Claim~\ref{app:zero}; `minorBound_24_of_twenty` below is the *looser* `4 n³L` slot
that the earlier formalisation had, which is why the chain appeared to need `24`. -/
theorem minorBound_22_of_twenty {n L ω : ℕ} (hω : ω ≤ n) (hn : 1 ≤ n) (hL : n ≤ L) :
    ω * (20 * n ^ 2 * L) + (n * n + 1) ≤ 22 * n ^ 3 * L := by
  have h1 : ω * (20 * n ^ 2 * L) ≤ 20 * (n ^ 3 * L) := by
    calc ω * (20 * n ^ 2 * L) ≤ n * (20 * n ^ 2 * L) := Nat.mul_le_mul_right _ hω
      _ = 20 * (n ^ 3 * L) := by ring
  have hL1 : 1 ≤ L := le_trans hn hL
  have hn2 : n * n ≤ n ^ 3 := by nlinarith
  have hLm : n ^ 3 ≤ n ^ 3 * L := by nlinarith
  have h3 : n * n + 1 ≤ 2 * (n ^ 3 * L) := by nlinarith
  nlinarith

/-- **The same step with the `G`-block constant `20`.**  This is *not* used in
the chain; it records that the `20 n²L` entry bound alone gives `24 n³L`, not
`22 n³L`.  Hence the constant `22` of `hZ` belongs to the `18`-bit `X` block. -/
theorem minorBound_24_of_twenty {n L ω : ℕ} (hω : ω ≤ n) (hn : 1 ≤ n) (hL : n ≤ L) :
    ω * (20 * n ^ 2 * L) + (n * n + 1) ≤ 24 * n ^ 3 * L := by
  have h1 : ω * (20 * n ^ 2 * L) ≤ 20 * (n ^ 3 * L) := by
    calc ω * (20 * n ^ 2 * L) ≤ n * (20 * n ^ 2 * L) := Nat.mul_le_mul_right _ hω
      _ = 20 * (n ^ 3 * L) := by ring
  have h2 : n * n + 1 ≤ 4 * n ^ 3 * L := factorialSlot_le hn hL
  nlinarith

/-- **The `22 → 47` step.**  A sum of `2ω` products of two `22 n³L`-bit factors
has bit length at most `47 n³L`:
`44 n³L` for the two factors plus `3 n³L` covering the `2ω ≤ 2n` summation index. -/
theorem gramBound_47 {n L ω : ℕ} (hω : ω ≤ n) (hn : 1 ≤ n) (hL : n ≤ L) :
    2 * ω + 22 * n ^ 3 * L + 22 * n ^ 3 * L ≤ 47 * n ^ 3 * L := by
  have h4 : n ≤ n ^ 4 := le_fourth hn
  have h45 : n ^ 4 ≤ n ^ 3 * L := fourth_le_cube_mul hL
  have h2ω : 2 * ω ≤ 3 * (n ^ 3 * L) := by nlinarith
  nlinarith

/-- **The `47 → 240` core**, scaled by `L`: `94 n³L + 1 ≤ 240 n⁵L`. -/
theorem const_240_scaled {n L : ℕ} (hn : 1 ≤ n) (hL : n ≤ L) :
    94 * n ^ 3 * L + 1 ≤ 240 * n ^ 5 * L := by
  have hbase : 94 * n ^ 3 + 1 ≤ 240 * n ^ 5 := by
    have h2 : 1 ≤ n ^ 2 := one_le_pow_nat hn 2
    have hmono : n ^ 3 ≤ n ^ 3 * n ^ 2 := by
      calc n ^ 3 = n ^ 3 * 1 := by ring
        _ ≤ n ^ 3 * n ^ 2 := Nat.mul_le_mul_left _ h2
    have hpow : n ^ 3 * n ^ 2 = n ^ 5 := by ring
    rw [← hpow]
    nlinarith
  have hL1 : 1 ≤ L := le_trans hn hL
  have hmul : (94 * n ^ 3 + 1) * L ≤ (240 * n ^ 5) * L := Nat.mul_le_mul_right _ hbase
  nlinarith

/-- **The `47 → 240` step** (`q`-term form): a sum of `q` products of two
`47 n³L`-bit factors has bit length at most `240 q n⁵L`. -/
theorem coeffBound_240 {n L q : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) (hL : n ≤ L) :
    q + 47 * n ^ 3 * L + 47 * n ^ 3 * L ≤ 240 * q * n ^ 5 * L := by
  have h240 : 94 * n ^ 3 * L + 1 ≤ 240 * n ^ 5 * L := const_240_scaled hn hL
  have hqA : 94 * n ^ 3 * L ≤ q * (94 * n ^ 3 * L) := by
    calc 94 * n ^ 3 * L = 1 * (94 * n ^ 3 * L) := (one_mul _).symm
      _ ≤ q * (94 * n ^ 3 * L) := Nat.mul_le_mul_right _ hq
  have hid : q * (94 * n ^ 3 * L + 1) = q * (94 * n ^ 3 * L) + q := by ring
  calc q + 47 * n ^ 3 * L + 47 * n ^ 3 * L
      = q + 94 * n ^ 3 * L := by ring
    _ ≤ q * (94 * n ^ 3 * L + 1) := by nlinarith [hqA, hid]
    _ ≤ q * (240 * n ^ 5 * L) := Nat.mul_le_mul_left _ h240
    _ = 240 * q * n ^ 5 * L := by ring

/-- **The explicit constant check requested for the paper**: `2 * (47 n³L) + 1`
fits under `240 q n⁵L`.  Hypothesis-free apart from the side conditions. -/
theorem const_240_explicit {n L q : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) (hL : n ≤ L) :
    2 * (47 * n ^ 3 * L) + 1 ≤ 240 * q * n ^ 5 * L := by
  have h240 : 94 * n ^ 3 * L + 1 ≤ 240 * n ^ 5 * L := const_240_scaled hn hL
  have hqC : 240 * n ^ 5 * L ≤ 240 * q * n ^ 5 * L := by
    calc 240 * n ^ 5 * L = 1 * (240 * n ^ 5 * L) := (one_mul _).symm
      _ ≤ q * (240 * n ^ 5 * L) := Nat.mul_le_mul_right _ hq
      _ = 240 * q * n ^ 5 * L := by ring
  calc 2 * (47 * n ^ 3 * L) + 1 = 94 * n ^ 3 * L + 1 := by ring
    _ ≤ 240 * n ^ 5 * L := h240
    _ ≤ 240 * q * n ^ 5 * L := hqC

/-! ## 3.  The conditional links of the chain -/

/-- **Link `X → Z` (maximal minors).**  If every entry of an `N × N` integer
matrix has bit length at most `18 n²L` and `ω ≤ n`, then every `ω × ω` minor has
bit length at most `22 n³L`.

This is `bitLenInt_bMinor_le` (Leibniz: `ω * b + bitLenInt ω!`) followed by
`minorBound_22`. -/
theorem bMinor_bitLen_le_22 {N n L ω : ℕ} (M : Matrix (Fin N) (Fin N) ℤ)
    (r c : Fin ω → Fin N) (hω : ω ≤ n) (hn : 1 ≤ n) (hL : n ≤ L)
    (hM : ∀ i j, bitLenInt (M i j) ≤ 18 * n ^ 2 * L) :
    bitLenInt (bMinor M r c) ≤ 22 * n ^ 3 * L := by
  have hb : ∀ i j, |M i j| < (2 : ℤ) ^ (18 * n ^ 2 * L) :=
    fun i j => abs_lt_two_pow_of_bitLenInt_le (hM i j)
  have hminor := bitLenInt_bMinor_le M r c hb
  have hsize : ω.size ≤ n := by
    calc ω.size ≤ n.size := Nat.size_le_size hω
      _ ≤ n := nat_size_le_self n
  have hfac : bitLenInt (ω.factorial : ℤ) ≤ n * n + 1 := by
    have h1 := bitLenInt_factorial_le ω
    have h2 : ω * ω.size ≤ n * n := by
      calc ω * ω.size ≤ ω * n := Nat.mul_le_mul_left _ hsize
        _ ≤ n * n := Nat.mul_le_mul_right n hω
    nlinarith
  have hnum := minorBound_22 hω hn hL
  nlinarith

/-- **Link `X, G → Z` (maximal minors), with the `G`-block bound.**  A maximal minor of
`λX − G` has entries drawn from BOTH blocks, so the relevant entry bound is
`max(18, 20) n²L = 20 n²L`; then every `ω × ω` minor still has bit length at most
`22 n³L`, which is the constant the paper uses in Claim~\ref{app:zero}. -/
theorem bMinor_bitLen_le_22_of_twenty {N n L ω : ℕ} (M : Matrix (Fin N) (Fin N) ℤ)
    (r c : Fin ω → Fin N) (hω : ω ≤ n) (hn : 1 ≤ n) (hL : n ≤ L)
    (hM : ∀ i j, bitLenInt (M i j) ≤ 20 * n ^ 2 * L) :
    bitLenInt (bMinor M r c) ≤ 22 * n ^ 3 * L := by
  have hb : ∀ i j, |M i j| < (2 : ℤ) ^ (20 * n ^ 2 * L) :=
    fun i j => abs_lt_two_pow_of_bitLenInt_le (hM i j)
  have hminor := bitLenInt_bMinor_le M r c hb
  have hsize : ω.size ≤ n := by
    calc ω.size ≤ n.size := Nat.size_le_size hω
      _ ≤ n := nat_size_le_self n
  have hfac : bitLenInt (ω.factorial : ℤ) ≤ n * n + 1 := by
    have h1 := bitLenInt_factorial_le ω
    have h2 : ω * ω.size ≤ n * n := by
      calc ω * ω.size ≤ ω * n := Nat.mul_le_mul_left _ hsize
        _ ≤ n * n := Nat.mul_le_mul_right n hω
    nlinarith
  have hnum := minorBound_22_of_twenty hω hn hL
  nlinarith

/-- **Link `Z → S` (Gram entries).**  If every entry of the `2ω × 2ω` integer
matrix `Z` has bit length at most `22 n³L` and `ω ≤ n`, then every Gram entry
`∑ k, Z k i * Z k j` has bit length at most `47 n³L`. -/
theorem gramEntry_bitLen_le_47 {n L ω : ℕ} (hω : ω ≤ n) (hn : 1 ≤ n) (hL : n ≤ L)
    (Z : Fin (2 * ω) → Fin (2 * ω) → ℤ)
    (hZ : ∀ i j, bitLenInt (Z i j) ≤ 22 * n ^ 3 * L) (i j : Fin (2 * ω)) :
    bitLenInt (∑ k : Fin (2 * ω), Z k i * Z k j) ≤ 47 * n ^ 3 * L := by
  have h := bitLenInt_sum_mul_le_univ (fun k : Fin (2 * ω) => Z k i)
      (fun k : Fin (2 * ω) => Z k j) (22 * n ^ 3 * L) (22 * n ^ 3 * L)
      (fun k => hZ k i) (fun k => hZ k j)
  have hcard : Fintype.card (Fin (2 * ω)) = 2 * ω := by simp
  rw [hcard] at h
  exact le_trans h (gramBound_47 hω hn hL)

/-- **Link `S → coefficient`.**  A coefficient expressed as a `q`-term bilinear
sum of `47 n³L`-bit entries has bit length at most `240 q n⁵L`. -/
theorem coefficient_bitLen_le_240 {n L q : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) (hL : n ≤ L)
    (a c : Fin q → ℤ) (ha : ∀ t, bitLenInt (a t) ≤ 47 * n ^ 3 * L)
    (hc : ∀ t, bitLenInt (c t) ≤ 47 * n ^ 3 * L) :
    bitLenInt (∑ t : Fin q, a t * c t) ≤ 240 * q * n ^ 5 * L := by
  have h := bitLenInt_sum_mul_le_univ a c (47 * n ^ 3 * L) (47 * n ^ 3 * L) ha hc
  have hcard : Fintype.card (Fin q) = q := by simp
  rw [hcard] at h
  exact le_trans h (coeffBound_240 hq hn hL)

/-- **Capstone: the composite `Z → S → coefficient` bound.**  If the entries of
`Z` have bit length at most `22 n³L`, then a coefficient given by a `q`-term sum
of products of two Gram entries `∑ k, Z k i * Z k j` has bit length at most
`240 q n⁵L`.

This is the arithmetic skeleton of the last two links of Claim 15, with no
appeal to the paper's actual objects. -/
theorem coefficient_of_minor_gram_le_240 {n L q ω : ℕ} (hω : ω ≤ n) (hq : 1 ≤ q)
    (hn : 1 ≤ n) (hL : n ≤ L) (Z : Fin (2 * ω) → Fin (2 * ω) → ℤ)
    (hZ : ∀ i j, bitLenInt (Z i j) ≤ 22 * n ^ 3 * L)
    (u v : Fin q → Fin (2 * ω) × Fin (2 * ω)) :
    bitLenInt (Finset.univ.sum fun t : Fin q =>
        (Finset.univ.sum fun k : Fin (2 * ω) => Z k (u t).1 * Z k (u t).2) *
        (Finset.univ.sum fun k : Fin (2 * ω) => Z k (v t).1 * Z k (v t).2))
      ≤ 240 * q * n ^ 5 * L := by
  refine coefficient_bitLen_le_240 hq hn hL
    (fun t => Finset.univ.sum fun k : Fin (2 * ω) => Z k (u t).1 * Z k (u t).2)
    (fun t => Finset.univ.sum fun k : Fin (2 * ω) => Z k (v t).1 * Z k (v t).2)
    ?_ ?_
  · intro t
    exact gramEntry_bitLen_le_47 hω hn hL Z hZ (u t).1 (u t).2
  · intro t
    exact gramEntry_bitLen_le_47 hω hn hL Z hZ (v t).1 (v t).2

/-- **Products across the two blocks** (`X`: `18 n²L`, `G`: `20 n²L`):
`38 = 18 + 20`, an instance of `bitLenInt_mul_le` with the paper's constants. -/
theorem blockProduct_bitLen_le_38 {n L : ℕ} {x y : ℤ}
    (hx : bitLenInt x ≤ 18 * n ^ 2 * L) (hy : bitLenInt y ≤ 20 * n ^ 2 * L) :
    bitLenInt (x * y) ≤ 38 * n ^ 2 * L := by
  have h := bitLenInt_mul_le hx hy
  have heq : 18 * n ^ 2 * L + 20 * n ^ 2 * L = 38 * n ^ 2 * L := by ring
  omega

end Q1Paper.Claim15_Arithmetic
