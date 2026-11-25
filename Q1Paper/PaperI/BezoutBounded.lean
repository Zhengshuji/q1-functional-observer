
import Q1Paper.PaperI.RatDescent
import Q1Paper.PaperI.C16Gcd
import Q1Paper.PaperI.Claim11_MinorsGram
import Q1Paper.BezoutReal

/-!
Q1Paper/PaperI/BezoutBounded.lean

**Degree-bounded rational Bézout certificate** — the descent step missing from Claim 16 of
Paper I.

The paper obtains, for a family `f : ι → ℚ[λ]` of polynomials of degree at most `ω`, the
Bézout identity `∑ g i * f i = 1` with multipliers of degree `< ω` *over `ℝ`*
(`Q1Paper.exists_bezout_family_real`).  Claim 16 needs the same over `ℚ`
(`claim16_iii_implies_iv` takes exactly that as its hypothesis).  Here the descent is proved:
the coefficient vector of the real multipliers solves a **rational** linear system in the
unknowns `c i k` (`g i = ∑_{k<ω} c i k * X^k`, `k < ω`), and
`exists_rat_solution_of_exists_real_solution` (`PaperI/RatDescent.lean`) turns a real solution
of that system into a rational one.

Main results:

* `coeff_sum_C_mul_X_pow_mul` : coefficient comparison: the `d`-th coefficient of a truncated
  combination is a linear function of the coefficient vector, with matrix
  `truncSysMatrix`; generic over a commutative ring.
* `natDegree_sum_C_mul_X_pow_le`, `coeffFamily_deg` : a reassembled multiplier
  `∑_{k<ω} c k * X^k` has degree `≤ ω - 1` (hence `< ω` when it is nonzero).
* `exists_rat_bounded_bezout_of_real_bounded_bezout_arb` : the descent, for an arbitrary
  finite index type `ι`.
* `exists_rat_bounded_bezout_of_real_bounded_bezout` : the requested `Fin ω` form.
* `exists_rat_bounded_bezout_of_no_common_root_arb`,
  `exists_rat_bounded_bezout_of_no_common_root` : the same with the "no common complex root"
  hypothesis (equivalently: the gcd of the family is a nonzero constant), composed with
  `Q1Paper.exists_bezout_family_real`.
* `claim16_iii_implies_iv_of_gcd_isConst`, `claim16_ii_implies_iv_rat` : Claim 16,
  (iii) ⟹ (iv) and (ii) ⟹ (iv) over `ℚ`, with the degree bound `2ω−2` — i.e. the gap recorded
  at the end of `PaperI/Claim16.lean` and `PaperI/C16Gcd.lean` is closed.
* a `True` point showing that the main theorem is not vacuous.

No `sorry`, no `admit`, no new axioms.
-/


open scoped BigOperators
open Matrix Polynomial

namespace Q1Paper

noncomputable section

/-! ## Coefficient comparison -/

/-- **Coefficient comparison.**  If `g i = ∑_{k<ω} c i k * X^k`, then the `d`-th coefficient of
`∑ i, g i * f i` is the linear expression `∑ i ∑ k, c i k * [k ≤ d] * (f i).coeff (d - k)`.

(The truncation `[k ≤ d]` is exactly the `if` of `Polynomial.coeff_X_pow_mul'`; it is what
makes the nat-subtraction `d - k` correct for all `d`, including `d < k`.) -/
theorem coeff_sum_C_mul_X_pow_mul {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {ω : ℕ}
    (c : ι → Fin ω → R) (f : ι → Polynomial R) (d : ℕ) :
    (∑ i : ι, (∑ k : Fin ω, Polynomial.C (c i k) * Polynomial.X ^ (k : ℕ)) * f i).coeff d
      = ∑ i : ι, ∑ k : Fin ω,
          c i k * (if (k : ℕ) ≤ d then (f i).coeff (d - (k : ℕ)) else 0) := by
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h : (Polynomial.C (c i k) * Polynomial.X ^ (k : ℕ) : Polynomial R) * f i
      = Polynomial.X ^ (k : ℕ) * (Polynomial.C (c i k) * f i) := by
    rw [mul_comm (Polynomial.C (c i k)) (Polynomial.X ^ (k : ℕ)), mul_assoc]
  rw [h, Polynomial.coeff_X_pow_mul']
  by_cases hk : (k : ℕ) ≤ d
  · rw [if_pos hk, if_pos hk, Polynomial.coeff_C_mul]
  · rw [if_neg hk, if_neg hk, mul_zero]

/-! ## The truncated linear system -/

/-- The coefficient matrix of the truncated linear system.  Row `d` is the coefficient of
`X^d` in `∑ i, g i * f i`, expressed linearly in the unknown coefficient vector
`c i k = (g i).coeff k` with `k < ω`. -/
def truncSysMatrix {ι : Type*} (ω D : ℕ) (f : ι → Polynomial ℚ) :
    Matrix (Fin D) (ι × Fin ω) ℚ :=
  fun d ik => if (ik.2 : ℕ) ≤ (d : ℕ) then (f ik.1).coeff ((d : ℕ) - (ik.2 : ℕ)) else 0

/-- Right-hand side of the truncated system: the coefficient vector of `1`. -/
def truncSysRhs (D : ℕ) : Fin D → ℚ :=
  fun d => if (d : ℕ) = 0 then 1 else 0

/-- Reassembly: a coefficient vector for the truncated system gives a family of polynomials
of degree `< ω`. -/
def coeffFamily {ι : Type*} (ω : ℕ) (y : ι × Fin ω → ℚ) : ι → Polynomial ℚ :=
  fun i => ∑ k : Fin ω, Polynomial.C (y (i, k)) * Polynomial.X ^ (k : ℕ)

/-- A reassembled multiplier has degree at most `ω - 1`. -/
theorem natDegree_sum_C_mul_X_pow_le {ω : ℕ} (c : Fin ω → ℚ) :
    (∑ k : Fin ω, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)).natDegree ≤ ω - 1 := by
  rcases Nat.eq_zero_or_pos ω with h | h
  · subst h
    simp
  · refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ)
      (n := ω - 1) (fun k : Fin ω => Polynomial.C (c k) * Polynomial.X ^ (k : ℕ))
      (fun k _ => ?_)
    calc (Polynomial.C (c k) * Polynomial.X ^ (k : ℕ) : Polynomial ℚ).natDegree
        ≤ (Polynomial.C (c k)).natDegree + (Polynomial.X ^ (k : ℕ)).natDegree :=
          Polynomial.natDegree_mul_le
      _ = 0 + (k : ℕ) := by
          rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
      _ ≤ ω - 1 := by have := k.isLt; omega

/-- The degree bound for a reassembled multiplier, in the disjunctive form used in the
statement of the main theorem. -/
theorem coeffFamily_deg {ι : Type*} {ω : ℕ} (y : ι × Fin ω → ℚ) (i : ι) :
    coeffFamily ω y i = 0 ∨ (coeffFamily ω y i).natDegree < ω := by
  by_cases hz : coeffFamily ω y i = 0
  · exact Or.inl hz
  · right
    rcases Nat.eq_zero_or_pos ω with h | h
    · exfalso
      subst h
      exact hz (by simp [coeffFamily])
    · have h1 := natDegree_sum_C_mul_X_pow_le (fun k : Fin ω => y (i, k))
      have h2 : (coeffFamily ω y i).natDegree ≤ ω - 1 := by
        simpa [coeffFamily] using h1
      omega

/-! ## The descent -/

/-- **A real bounded Bézout family over a rational family descends to `ℚ`**
(general finite index type).

The real multipliers give a real solution of the truncated rational system; by
`exists_rat_solution_of_exists_real_solution` the system has a rational solution, which
reassembles into rational multipliers.  The truncation height `∑ i, (f i).natDegree + ω + 1`
is chosen so that all coefficients of `∑ g i * f i` are covered (`deg ≤ (ω-1) + deg f i`). -/
theorem exists_rat_bounded_bezout_of_real_bounded_bezout_arb
    {ι : Type*} [Fintype ι] (ω : ℕ) (f : ι → Polynomial ℚ)
    (hreal : ∃ g : ι → Polynomial ℝ,
      (∀ i, g i = 0 ∨ (g i).natDegree < ω) ∧
      (∑ i, g i * (f i).map (algebraMap ℚ ℝ) = 1)) :
    ∃ g : ι → Polynomial ℚ,
      (∀ i, g i = 0 ∨ (g i).natDegree < ω) ∧
      (∑ i, g i * f i = 1) := by
  classical
  -- Bound on the degrees of the `f i`.
  have hSbound : ∀ i : ι, (f i).natDegree ≤ ∑ j : ι, (f j).natDegree := by
    intro i
    exact Finset.single_le_sum (s := Finset.univ) (f := fun j : ι => (f j).natDegree)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  -- Step 1: the real multipliers solve the truncated rational system.
  have hsys : ∃ x : ι × Fin ω → ℝ,
      ∀ d : Fin (∑ j : ι, (f j).natDegree + ω + 1),
        ∑ ik : ι × Fin ω,
            ((truncSysMatrix ω (∑ j : ι, (f j).natDegree + ω + 1) f) d ik : ℝ) * x ik
          = ((truncSysRhs (∑ j : ι, (f j).natDegree + ω + 1)) d : ℝ) := by
    obtain ⟨g, hgdeg, hgsum⟩ := hreal
    refine ⟨fun ik => (g ik.1).coeff (ik.2 : ℕ), fun d => ?_⟩
    -- each `g i` is the sum of its first `ω` terms
    have hg : ∀ i : ι, g i = ∑ k : Fin ω, Polynomial.C ((g i).coeff (k : ℕ)) *
        Polynomial.X ^ (k : ℕ) := by
      intro i
      rcases hgdeg i with h0 | hlt
      · rw [h0]
        simp
      · calc g i = ∑ k ∈ Finset.range ω, Polynomial.C ((g i).coeff k) * Polynomial.X ^ k :=
              Polynomial.as_sum_range_C_mul_X_pow' (g i) hlt
          _ = ∑ k : Fin ω, Polynomial.C ((g i).coeff (k : ℕ)) * Polynomial.X ^ (k : ℕ) :=
              (Fin.sum_univ_eq_sum_range
                (fun k => Polynomial.C ((g i).coeff k) * Polynomial.X ^ k) ω).symm
    -- each truncated multiplier equals the corresponding `g i`
    have hstep : ∀ i : ι, (∑ k : Fin ω, Polynomial.C ((g i).coeff (k : ℕ)) *
        Polynomial.X ^ (k : ℕ)) = g i := fun i => (hg i).symm
    -- substitute into the real identity
    have hsum1 : (∑ i : ι, (∑ k : Fin ω, Polynomial.C ((g i).coeff (k : ℕ)) *
        Polynomial.X ^ (k : ℕ)) * (f i).map (algebraMap ℚ ℝ)) = 1 := by
      calc (∑ i : ι, (∑ k : Fin ω, Polynomial.C ((g i).coeff (k : ℕ)) *
            Polynomial.X ^ (k : ℕ)) * (f i).map (algebraMap ℚ ℝ))
          = ∑ i : ι, g i * (f i).map (algebraMap ℚ ℝ) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hstep i]
        _ = 1 := hgsum
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff (d : ℕ)) hsum1
    rw [coeff_sum_C_mul_X_pow_mul (fun i k => (g i).coeff (k : ℕ))
      (fun i => (f i).map (algebraMap ℚ ℝ)) (d : ℕ)] at hcoeff
    rw [Polynomial.coeff_one] at hcoeff
    -- rewrite the matrix entries over `ℝ`
    rw [Fintype.sum_prod_type]
    have hA' : ∀ (i : ι) (k : Fin ω),
        ((truncSysMatrix ω (∑ j : ι, (f j).natDegree + ω + 1) f) d (i, k) : ℝ)
          = (if (k : ℕ) ≤ (d : ℕ)
              then ((f i).map (algebraMap ℚ ℝ)).coeff ((d : ℕ) - (k : ℕ)) else 0) := by
      intro i k
      by_cases hk : (k : ℕ) ≤ (d : ℕ)
      · rw [truncSysMatrix]
        rw [if_pos hk, if_pos hk]
        exact (Polynomial.coeff_map (p := f i) (algebraMap ℚ ℝ) ((d : ℕ) - (k : ℕ))).symm
      · rw [truncSysMatrix]
        rw [if_neg hk, if_neg hk]
        simp
    simp only [hA']
    have hb' : ((truncSysRhs (∑ j : ι, (f j).natDegree + ω + 1)) d : ℝ)
        = (if (d : ℕ) = 0 then (1 : ℝ) else 0) := by
      rw [truncSysRhs]
      by_cases hd0 : (d : ℕ) = 0
      · rw [if_pos hd0, if_pos hd0]
        norm_num
      · rw [if_neg hd0, if_neg hd0]
        norm_num
    rw [hb', ← hcoeff]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => mul_comm _ _))
  -- Step 2: descend to `ℚ`.
  obtain ⟨y, hy⟩ := exists_rat_solution_of_exists_real_solution_arb
    (truncSysMatrix ω (∑ j : ι, (f j).natDegree + ω + 1) f)
    (truncSysRhs (∑ j : ι, (f j).natDegree + ω + 1)) hsys
  -- Step 3: reassemble and check the identity coefficient by coefficient.
  refine ⟨coeffFamily ω y, coeffFamily_deg y, ?_⟩
  refine Polynomial.ext (fun d => ?_)
  by_cases hd : d < ∑ j : ι, (f j).natDegree + ω + 1
  · -- coefficients below the truncation height: the linear system
    set dd : Fin (∑ j : ι, (f j).natDegree + ω + 1) := ⟨d, hd⟩ with hdd
    have hsysd : ∑ i : ι, ∑ k : Fin ω,
        (truncSysMatrix ω (∑ j : ι, (f j).natDegree + ω + 1) f) dd (i, k) * y (i, k)
          = truncSysRhs (∑ j : ι, (f j).natDegree + ω + 1) dd := by
      have h := hy dd
      rw [Fintype.sum_prod_type] at h
      simpa using h
    have hA'' : ∀ (i : ι) (k : Fin ω),
        (truncSysMatrix ω (∑ j : ι, (f j).natDegree + ω + 1) f) dd (i, k)
          = (if (k : ℕ) ≤ d then (f i).coeff (d - (k : ℕ)) else 0) := by
      intro i k
      rfl
    have hgoal : (∑ i : ι, coeffFamily ω y i * f i).coeff d
        = ∑ i : ι, ∑ k : Fin ω,
            y (i, k) * (if (k : ℕ) ≤ d then (f i).coeff (d - (k : ℕ)) else 0) :=
      coeff_sum_C_mul_X_pow_mul (fun i k => y (i, k)) f d
    have key : ∑ i : ι, ∑ k : Fin ω,
        y (i, k) * (if (k : ℕ) ≤ d then (f i).coeff (d - (k : ℕ)) else 0)
          = if d = 0 then (1 : ℚ) else 0 := by
      have h1 : (∑ i : ι, ∑ k : Fin ω,
            y (i, k) * (if (k : ℕ) ≤ d then (f i).coeff (d - (k : ℕ)) else 0))
          = ∑ i : ι, ∑ k : Fin ω,
            (truncSysMatrix ω (∑ j : ι, (f j).natDegree + ω + 1) f) dd (i, k) * y (i, k) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
        rw [hA'' i k, mul_comm]
      rw [h1, hsysd, truncSysRhs]
    rw [Polynomial.coeff_one, hgoal, key]
  · -- coefficients above it: both sides vanish
    have hge : ∑ j : ι, (f j).natDegree + ω + 1 ≤ d := by omega
    rw [Polynomial.coeff_one]
    have hd0 : ¬ d = 0 := by omega
    rw [if_neg hd0]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hbound : (∑ i : ι, coeffFamily ω y i * f i).natDegree
        ≤ (ω - 1) + ∑ j : ι, (f j).natDegree := by
      refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ)
        (n := (ω - 1) + ∑ j : ι, (f j).natDegree)
        (fun i : ι => coeffFamily ω y i * f i) (fun i _ => ?_)
      calc (coeffFamily ω y i * f i).natDegree
          ≤ (coeffFamily ω y i).natDegree + (f i).natDegree := Polynomial.natDegree_mul_le
        _ ≤ (ω - 1) + (f i).natDegree := by
            have h1 : (coeffFamily ω y i).natDegree ≤ ω - 1 := by
              simpa [coeffFamily] using
                natDegree_sum_C_mul_X_pow_le (fun k : Fin ω => y (i, k))
            omega
        _ ≤ (ω - 1) + ∑ j : ι, (f j).natDegree := by
            have h2 := hSbound i
            omega
    omega

/-- **The requested statement.**  A degree-bounded Bézout family over `ℝ` for a family
`f : Fin ω → ℚ[λ]` (with `deg g i < ω`) descends to a degree-bounded Bézout family over `ℚ`. -/
theorem exists_rat_bounded_bezout_of_real_bounded_bezout
    (ω : ℕ) (f : Fin ω → Polynomial ℚ)
    (hreal : ∃ g : Fin ω → Polynomial ℝ,
      (∀ i, g i = 0 ∨ (g i).natDegree < ω) ∧
      (∑ i, g i * (f i).map (algebraMap ℚ ℝ) = 1)) :
    ∃ g : Fin ω → Polynomial ℚ,
      (∀ i, g i = 0 ∨ (g i).natDegree < ω) ∧
      (∑ i, g i * f i = 1) :=
  exists_rat_bounded_bezout_of_real_bounded_bezout_arb ω f hreal

/-! ## From "no common complex root" to the rational bounded family -/

/-- The complexification of the realification of a rational polynomial is its
complexification. -/
theorem map_map_ratReal_realComplex (p : Polynomial ℚ) :
    (p.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ) = p.map (algebraMap ℚ ℂ) := by
  rw [Polynomial.map_map]
  congr 1

/-- **Degree-bounded rational Bézout family from "no common complex root"**
(arbitrary finite index type).

The hypothesis is the root form (ii) of Claim 16 (equivalently, by
`gcd_isConst_iff_no_common_complex_root`, the constant-gcd form (iii)); the conclusion is the
degree-bounded identity over `ℚ`. -/
theorem exists_rat_bounded_bezout_of_no_common_root_arb
    {ι : Type*} [Fintype ι] (ω : ℕ) (hω : 1 ≤ ω) (f : ι → Polynomial ℚ)
    (hdeg : ∀ i, (f i).natDegree ≤ ω)
    (hroot : ∀ z : ℂ, ∃ i, Polynomial.eval z ((f i).map (algebraMap ℚ ℂ)) ≠ 0) :
    ∃ g : ι → Polynomial ℚ,
      (∀ i, g i = 0 ∨ (g i).natDegree < ω) ∧
      (∑ i, g i * f i = 1) := by
  refine exists_rat_bounded_bezout_of_real_bounded_bezout_arb ω f ?_
  have hdegR : ∀ i, ((f i).map (algebraMap ℚ ℝ)).natDegree ≤ ω := by
    intro i
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective]
    exact hdeg i
  have hrootR : ∀ z : ℂ, ∃ i, Polynomial.eval z
      (((f i).map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)) ≠ 0 := by
    intro z
    obtain ⟨i, hi⟩ := hroot z
    exact ⟨i, by rw [map_map_ratReal_realComplex]; exact hi⟩
  obtain ⟨g, hsum, hgd⟩ :=
    Q1Paper.exists_bezout_family_real (f := fun i => (f i).map (algebraMap ℚ ℝ))
      hω hdegR hrootR
  exact ⟨g, fun i => Or.inr (hgd i), hsum⟩

/-- **Degree-bounded rational Bézout family from "no common complex root"**, `Fin ω` form. -/
theorem exists_rat_bounded_bezout_of_no_common_root
    (ω : ℕ) (hω : 1 ≤ ω) (f : Fin ω → Polynomial ℚ)
    (hdeg : ∀ i, (f i).natDegree ≤ ω)
    (hroot : ∀ z : ℂ, ∃ i, Polynomial.eval z ((f i).map (algebraMap ℚ ℂ)) ≠ 0) :
    ∃ g : Fin ω → Polynomial ℚ,
      (∀ i, g i = 0 ∨ (g i).natDegree < ω) ∧
      (∑ i, g i * f i = 1) :=
  exists_rat_bounded_bezout_of_no_common_root_arb ω hω f hdeg hroot

/-! ## Feeding Claim 16 -/

/-- The two pencil definitions in the project agree: `PaperI.pencil` (entrywise,
`SpectralMinor.lean`) and `Q1Paper.pencil` (a matrix expression, `G3Coeff.lean`). -/
theorem pencil_eq_paperI_pencil {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℚ) :
    PaperI.pencil X G = pencil X G := by
  funext i j
  exact (Q1Paper.pencil_apply X G i j).symm

/-- **Claim 16, (iii) ⟹ (iv) with the degree bound `2ω−2`.**

The hypothesis is the constant-gcd form (iii) of Claim 16 for the pencil `λX − G`.  Its
maximal minors have no common complex root, hence (by
`exists_rat_bounded_bezout_of_no_common_root_arb`, which rests on
`exists_bezout_family_real` and on the rational descent proved above) they admit a
`ℚ[λ]`-Bézout family with all multipliers of degree `< ω`.  That is exactly the hypothesis of
`claim16_iii_implies_iv`, which then produces the degree-bounded left inverse.

This closes the gap recorded at the end of `PaperI/Claim16.lean` and
`PaperI/C16Gcd.lean` ("the transport back to `ℚ` needs a descent argument for the rational
linear system which is not formalised here"). -/
theorem claim16_iii_implies_iv_of_gcd_isConst {q ω : ℕ} (hω : 1 ≤ ω)
    (X G : Matrix (Fin q) (Fin ω) ℚ) (h : FamilyGcdIsConst (pencilMinors X G)) :
    ∃ S : Matrix (Fin ω) (Fin q) ℚ[X],
      S * pencil X G = 1 ∧ ∀ i j, (S i j).natDegree ≤ 2 * ω - 2 := by
  have hroot : NoCommonComplexRoot (pencilMinors X G) :=
    (pencilMinors_gcd_isConst_iff_no_common_complex_root X G).mp h
  have hdeg : ∀ e : Fin ω ↪ Fin q, (pencilMinors X G e).natDegree ≤ ω := by
    intro e
    have h := PaperI.natDegree_maximalMinor_le X G (e : Fin ω → Fin q) id
    rw [pencil_eq_paperI_pencil X G] at h
    exact h
  obtain ⟨g, hgdeg, hgsum⟩ :=
    exists_rat_bounded_bezout_of_no_common_root_arb (ι := Fin ω ↪ Fin q) ω hω
      (pencilMinors X G) hdeg hroot
  refine claim16_iii_implies_iv hω X G ⟨g, hgsum, fun e => ?_⟩
  rcases hgdeg e with h0 | hlt
  · rw [h0, Polynomial.natDegree_zero]
    omega
  · exact hlt

/-- **Claim 16, (ii) ⟹ (iv) over `ℚ`.**  The root form (ii) of Claim 16 gives the degree-bounded
left inverse over `ℚ`.  Previously this direction was available over an algebraically closed
field only (`claim16_ii_implies_iv`). -/
theorem claim16_ii_implies_iv_rat {q ω : ℕ} (hω : 1 ≤ ω)
    (X G : Matrix (Fin q) (Fin ω) ℚ) (hroot : NoCommonComplexRoot (pencilMinors X G)) :
    ∃ S : Matrix (Fin ω) (Fin q) ℚ[X],
      S * pencil X G = 1 ∧ ∀ i j, (S i j).natDegree ≤ 2 * ω - 2 :=
  claim16_iii_implies_iv_of_gcd_isConst hω X G
    (gcd_isConst_of_no_common_complex_root hroot)

/-! ## Non-vacuity: a `True` point -/

/-- The main theorem is not vacuous: for `ω = 1`, the constant family `1` admits the real
bounded family `1`, and the descent produces a rational one (indeed `g 0` has degree `0`). -/
example : ∃ g : Fin 1 → Polynomial ℚ,
    (∀ i, g i = 0 ∨ (g i).natDegree < 1) ∧
    (∑ i, g i * (fun _ : Fin 1 => (1 : Polynomial ℚ)) i = 1) :=
  exists_rat_bounded_bezout_of_real_bounded_bezout 1 (fun _ : Fin 1 => 1)
    ⟨fun _ => 1, ⟨fun _ => Or.inr (by simp), by simp⟩⟩

end

end Q1Paper

/-! ## Axiom audit and statement check -/


#check @Q1Paper.exists_rat_bounded_bezout_of_real_bounded_bezout
#check @Q1Paper.exists_rat_bounded_bezout_of_real_bounded_bezout_arb
#check @Q1Paper.exists_rat_bounded_bezout_of_no_common_root_arb
#check @Q1Paper.claim16_iii_implies_iv_of_gcd_isConst
#check @Q1Paper.claim16_ii_implies_iv_rat
