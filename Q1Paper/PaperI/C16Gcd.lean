/-
Q1Paper/PaperI/C16Gcd.lean

Claim 16 (`lem:zero`) of Paper I, part (iii), in its **gcd form**, and its link to the
"no common complex root" form (ii).

For `X G : Matrix (Fin q) (Fin ω) ℚ` (the claim assumes `q ≥ ω ≥ 1`; the formal statements
below are stated for all `q ω` and do not need those hypotheses) the pencil is
`Q(λ) = λX − G = pencil X G`, and the family of its maximal `ω × ω` minors, indexed by the
row embeddings `Fin ω ↪ Fin q`, is `pencilMinors X G e = minors (pencil X G) e`
(a `ω × ω` determinant over `ℚ[λ]`, hence a polynomial in `λ`).

The two conditions of the claim are

  (iii) `FamilyGcdIsConst f` : the family does not vanish identically and the gcd of the
        family in `ℚ[λ]` is a nonzero constant, i.e. `∃ c ≠ 0, gcd f = C c`
        (the gcd is `Finset.gcd` over the finite index type; this form already forces
        "not all vanish", since the gcd of the zero family is `0` — see
        `exists_ne_zero_of_gcd_isConst`);

  (ii)  `NoCommonComplexRoot f` : no `z : ℂ` is a root of every member of the family,
        i.e. `∀ z : ℂ, ∃ i, (f i).map (algebraMap ℚ ℂ) |>.eval z ≠ 0`.

Main results (no `sorry`, no `admit`, no new axioms; see the `#print axioms` block at the
end of the file):

* `gcd_isConst_iff_no_common_complex_root` : **(iii) ⟺ (ii)** for an arbitrary finite
  family over `ℚ`.  The two directions are
  - (iii) ⟹ (ii): `Finset.gcd_eq_sum_mul` (Bézout for a finite family, valid in any Bézout
    domain) turns the gcd into a `ℚ[λ]`-combination equal to the nonzero constant `c`;
    mapping to `ℂ[λ]` and evaluating at a putative common root `z` gives `c = 0`.
  - (ii) ⟹ (iii): the gcd `d` is nonzero; if `deg d > 0` then `d`, viewed in `ℂ[λ]`,
    has a complex root `z` (fundamental theorem of algebra); since `d ∣ f i` we get
    `(f i).map|>.eval z = 0` for every `i`, contradicting (ii).  Hence `d` is a
    nonzero constant.
  No minimal polynomial, resultant or algebraic-closure descent is needed: the
  "the root is algebraic over `ℚ`" step is replaced by the Bézout identity, which is
  available in `ℚ[λ]` because `ℚ[λ]` is a Bézout domain.
* `pencilMinors_gcd_isConst_iff_no_common_complex_root` : the pencil instance of the
  above (Claim 16, (iii) ⟺ (ii)).
* `exists_sum_mul_eq_one_of_gcd_isConst` : (iii) gives a `ℚ[λ]`-Bézout family
  `∑ g e * f e = 1` (with **no** degree bound).
* `exists_leftInverse_pencil_of_gcd_isConst` : (iii) gives a polynomial left inverse
  `S * Q = 1` over `ℚ[λ]` (via the adjugate assembly `leftInverse_of_bezout`).
* `rank_eq_of_leftInverse_pencil`, `claim16_iii_implies_i_of_gcd_isConst` :
  (iii) ⟹ (i), i.e. `rank (λ • X − G) = ω` at **every** `λ : ℂ`.
* `exists_minor_det_ne_zero_of_rank` : a `q × ω` complex matrix of rank `ω` has a nonzero
  maximal minor with the identity column choice (the column selection of the rank/minors
  criterion is a permutation of `Fin ω`);
* `eval_map_minors_pencil` : evaluating a maximal minor of `pencil X G` at `lam : ℂ` is the
  corresponding maximal minor of the evaluated matrix `lam • X − G`;
* `rank_eq_iff_no_common_complex_root` : **(i) ⟺ (ii)**, i.e.
  `(∀ λ : ℂ, rank (λ • X − G) = ω) ⟺ NoCommonComplexRoot (pencilMinors X G)`.
  Combined with `pencilMinors_gcd_isConst_iff_no_common_complex_root` this gives the full
  equivalence of (i), (ii) and (iii) of Claim 16.
* `claim16_i_iff_iii` : **(i) ⟺ (iii)** (transitivity through (ii)).
* `gcd_isConst_of_bezout`, `gcd_isConst_of_bezout_pencil` : the degree-bounded Bézout
  hypothesis of the existing `claim16_iii_implies_iv` implies (iii); thus that hypothesis is
  a *strengthening* of (iii), and (iii) ⟹ (i) here covers the same conclusion without any
  degree bound.

What is *not* proved here: the *degree-bounded* rational Bézout family
`∀ e, (g e).natDegree < ω`, which is exactly the hypothesis of the existing
`claim16_iii_implies_iv`.  The paper obtains the bound over `ℝ` (`exists_bezout_family_real`,
via hyperplane avoidance and the fundamental theorem of algebra) and then descends to `ℚ`
by observing that the defining linear system has rational data; the descent step
("a rational linear system solvable over `ℝ` is solvable over `ℚ`") is not formalised.
Because of this, (iii) ⟹ (iv) with the bound `deg S ≤ 2ω−2` is *not* obtained here; only
the unbounded left inverse and its consequence (i) are.
-/

import Q1Paper.PaperI.Claim16
import Q1Paper.PaperI.MinorRank
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.GCDMonoid.Finset

open Matrix Polynomial
open scoped BigOperators

namespace Q1Paper

noncomputable section

/-! ## The family of maximal minors of the pencil -/

/-- The family of maximal `ω × ω` minors of the pencil `λX − G`, indexed by the row
embeddings `Fin ω ↪ Fin q` (this is the index family of `minors` and of
`claim16_iii_implies_iv`). -/
def pencilMinors {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℚ) : (Fin ω ↪ Fin q) → ℚ[X] :=
  fun e => minors (pencil X G) e

/-- **(iii) of Claim 16, gcd form.**  The family does not vanish identically and its gcd
in `ℚ[λ]` is a nonzero constant.  ("Does not vanish identically" is automatic here: the
gcd of the identically zero family is `0`.  See `exists_ne_zero_of_gcd_isConst`.) -/
def FamilyGcdIsConst {ι : Type*} [Fintype ι] (f : ι → ℚ[X]) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ Finset.univ.gcd f = Polynomial.C c

/-- **(ii) of Claim 16, root form.**  No complex number is a root of every member of the
family. -/
def NoCommonComplexRoot {ι : Type*} (f : ι → ℚ[X]) : Prop :=
  ∀ z : ℂ, ∃ i, ((f i).map (algebraMap ℚ ℂ)).eval z ≠ 0

/-- The clause "the maximal minors do not all vanish" of (iii) is implied by the gcd
condition: a family of zeros has gcd `0`. -/
theorem exists_ne_zero_of_gcd_isConst {ι : Type*} [Fintype ι] {f : ι → ℚ[X]}
    (h : FamilyGcdIsConst f) : ∃ i, f i ≠ 0 := by
  classical
  obtain ⟨c, hc, hgcd⟩ := h
  by_contra hcon
  push Not at hcon
  have hzero : Finset.univ.gcd f = 0 := by
    rw [Finset.gcd_eq_zero_iff]
    exact fun x _ => hcon x
  rw [hzero] at hgcd
  exact (Polynomial.C_ne_zero.mpr hc) hgcd.symm

/-! ## (iii) ⟹ (ii): a constant gcd gives a Bézout identity, hence no common root -/

/-- **Bézout form of (iii) (no degree bound).**  If the gcd of a finite family in `ℚ[λ]`
is a nonzero constant, then some `ℚ[λ]`-combination of the family is `1`.

This is `Finset.gcd_eq_sum_mul` (Bézout's lemma for a finite family in a Bézout domain),
rescaled by the inverse of the constant. -/
theorem exists_sum_mul_eq_one_of_gcd_isConst {ι : Type*} [Fintype ι] {f : ι → ℚ[X]}
    (h : FamilyGcdIsConst f) :
    ∃ g : ι → ℚ[X], (∑ a, g a * f a) = 1 := by
  classical
  obtain ⟨c, hc, hgcd⟩ := h
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset ι) f
  refine ⟨fun a => Polynomial.C c⁻¹ * g a, ?_⟩
  have hsplit : (∑ a, (Polynomial.C c⁻¹ * g a) * f a)
      = Polynomial.C c⁻¹ * (∑ a, f a * g a) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsplit]
  have hsum : (∑ a, f a * g a) = Finset.univ.gcd f := hg.symm
  rw [hsum, hgcd, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1]

/-- **(iii) ⟹ (ii).**  A family whose gcd is a nonzero constant has no common complex
root: a common root would make every `ℚ[λ]`-combination of the family vanish there, but
the Bézout combination is the nonzero constant `c`. -/
theorem no_common_complex_root_of_gcd_isConst {ι : Type*} [Fintype ι] {f : ι → ℚ[X]}
    (h : FamilyGcdIsConst f) : NoCommonComplexRoot f := by
  classical
  intro z
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ i, ((f i).map (algebraMap ℚ ℂ)).eval z = 0`
  obtain ⟨c, hc, hgcd⟩ := h
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset ι) f
  have hmap : Polynomial.C ((algebraMap ℚ ℂ) c)
      = ∑ a, (f a).map (algebraMap ℚ ℂ) * (g a).map (algebraMap ℚ ℂ) := by
    have hCsum : (Polynomial.C c : ℚ[X]) = ∑ a, f a * g a := hgcd.symm.trans hg
    rw [← Polynomial.map_C, hCsum, Polynomial.map_sum]
    exact Finset.sum_congr rfl fun a _ => Polynomial.map_mul ..
  have hzero : ∀ a ∈ (Finset.univ : Finset ι),
      (Polynomial.eval z) ((f a).map (algebraMap ℚ ℂ) * (g a).map (algebraMap ℚ ℂ)) = 0 := by
    intro a _
    rw [Polynomial.eval_mul, hcon a, zero_mul]
  have heval := congrArg (fun p : ℂ[X] => p.eval z) hmap
  rw [Polynomial.eval_finsetSum, Polynomial.eval_C, Finset.sum_eq_zero hzero] at heval
  exact hc ((algebraMap ℚ ℂ).injective (by simpa using heval))

/-! ## (ii) ⟹ (iii): no common root forces the gcd to be a nonzero constant -/

/-- **(ii) ⟹ (iii).**  If a finite family in `ℚ[λ]` has no common complex root, its gcd is
a nonzero constant.  A gcd of positive degree would have a complex root `z` (fundamental
theorem of algebra), and as the gcd divides every member, `z` would be a common root. -/
theorem gcd_isConst_of_no_common_complex_root {ι : Type*} [Fintype ι] {f : ι → ℚ[X]}
    (h : NoCommonComplexRoot f) : FamilyGcdIsConst f := by
  classical
  set d : ℚ[X] := Finset.univ.gcd f with hd
  have hdvd : ∀ a, d ∣ f a := fun a => Finset.gcd_dvd (Finset.mem_univ a)
  have hdne : d ≠ 0 := by
    rw [hd, Finset.gcd_ne_zero_iff]
    obtain ⟨i, hi⟩ := h 0
    exact ⟨i, Finset.mem_univ i,
      fun h0 => hi (by rw [h0, Polynomial.map_zero, Polynomial.eval_zero])⟩
  have hdeg : d.natDegree = 0 := by
    by_contra hne
    have hpos : 0 < d.natDegree := Nat.pos_of_ne_zero hne
    -- the complexification of `d` has positive degree, hence a complex root
    have hmapne : d.map (algebraMap ℚ ℂ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hdne
    have hdegmap : (d.map (algebraMap ℚ ℂ)).natDegree = d.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective d
    have hdegpos : 0 < (d.map (algebraMap ℚ ℂ)).natDegree := by
      rw [hdegmap]; exact hpos
    have hdpos : 0 < (d.map (algebraMap ℚ ℂ)).degree := by
      rw [Polynomial.degree_eq_natDegree hmapne]
      exact_mod_cast hdegpos
    obtain ⟨z, hz⟩ := Complex.exists_root hdpos
    obtain ⟨i, hi⟩ := h z
    obtain ⟨q, hq⟩ := hdvd i
    apply hi
    have hz0 : (Polynomial.map (algebraMap ℚ ℂ) d).eval z = 0 := hz
    rw [hq, Polynomial.map_mul, Polynomial.eval_mul, hz0, zero_mul]
  have hdC : d = Polynomial.C (d.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hcoeff : d.coeff 0 ≠ 0 := by
    have hlc : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hdne
    rwa [← Polynomial.coeff_natDegree, hdeg] at hlc
  exact ⟨d.coeff 0, hcoeff, by rw [← hd]; exact hdC⟩

/-- **Claim 16, (iii) ⟺ (ii)**, for an arbitrary finite family of polynomials over `ℚ`:
the gcd of the family in `ℚ[λ]` is a nonzero constant exactly when the family has no
common complex root. -/
theorem gcd_isConst_iff_no_common_complex_root {ι : Type*} [Fintype ι] (f : ι → ℚ[X]) :
    FamilyGcdIsConst f ↔ NoCommonComplexRoot f :=
  ⟨no_common_complex_root_of_gcd_isConst, gcd_isConst_of_no_common_complex_root⟩

/-- **Claim 16, (iii) ⟺ (ii)**, for the pencil `λX − G`. -/
theorem pencilMinors_gcd_isConst_iff_no_common_complex_root {q ω : ℕ}
    (X G : Matrix (Fin q) (Fin ω) ℚ) :
    FamilyGcdIsConst (pencilMinors X G) ↔ NoCommonComplexRoot (pencilMinors X G) :=
  gcd_isConst_iff_no_common_complex_root (pencilMinors X G)

/-! ## From the gcd condition to a polynomial left inverse, and to (i) -/

/-- **(iii) ⟹ (iv) without the degree bound.**  The Bézout family of
`exists_sum_mul_eq_one_of_gcd_isConst` assembles, through the adjugate blocks
`adjRowInverse`, into a polynomial left inverse of the pencil over `ℚ[λ]`. -/
theorem exists_leftInverse_pencil_of_gcd_isConst {q ω : ℕ}
    (X G : Matrix (Fin q) (Fin ω) ℚ) (h : FamilyGcdIsConst (pencilMinors X G)) :
    ∃ S : Matrix (Fin ω) (Fin q) ℚ[X], S * pencil X G = 1 := by
  classical
  obtain ⟨g, hg⟩ := exists_sum_mul_eq_one_of_gcd_isConst h
  exact ⟨∑ e, g e • adjRowInverse (e : Fin ω → Fin q) (pencil X G),
    leftInverse_of_bezout (Q := pencil X G) hg⟩

/-- A polynomial left inverse of the pencil forces full column rank at every complex
parameter: evaluating at `λ` gives a left inverse of `λ • X − G`. -/
theorem rank_eq_of_leftInverse_pencil {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℚ)
    (S : Matrix (Fin ω) (Fin q) ℚ[X]) (hmul : S * pencil X G = 1) :
    ∀ lam : ℂ, (lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).rank = ω := by
  intro lam
  set M : Matrix (Fin q) (Fin ω) ℂ :=
    lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ) with hM
  set T : Matrix (Fin ω) (Fin q) ℂ :=
    S.map (Polynomial.eval₂ (algebraMap ℚ ℂ) lam) with hT
  have h1 : T * M = 1 := by
    have h := congrArg (fun N : Matrix (Fin ω) (Fin ω) ℚ[X] =>
      N.map (Polynomial.eval₂ (algebraMap ℚ ℂ) lam)) hmul
    rw [map_mul_eval₂, map_one_eval₂, pencil_map_eval₂] at h
    rw [hT, hM]
    exact h
  have hle : ω ≤ M.rank := by
    have h2 : (1 : Matrix (Fin ω) (Fin ω) ℂ).rank ≤ M.rank := by
      rw [← h1]
      exact Matrix.rank_mul_le_right T M
    rwa [Matrix.rank_one, Fintype.card_fin] at h2
  have hge : M.rank ≤ ω := by
    simpa using Matrix.rank_le_card_width M
  exact le_antisymm hge hle

/-- **Claim 16, (iii) ⟹ (i).**  The gcd form of (iii) gives `rank (λ • X − G) = ω` for
every `λ : ℂ` (no degree bound on the left inverse is needed for this direction). -/
theorem claim16_iii_implies_i_of_gcd_isConst {q ω : ℕ}
    (X G : Matrix (Fin q) (Fin ω) ℚ) (h : FamilyGcdIsConst (pencilMinors X G)) :
    ∀ lam : ℂ, (lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).rank = ω := by
  obtain ⟨S, hS⟩ := exists_leftInverse_pencil_of_gcd_isConst X G h
  exact rank_eq_of_leftInverse_pencil X G S hS

/-! ## (i) ⟺ (ii): full column rank at every complex parameter -/

/-- A `q × ω` complex matrix of rank `ω` has a nonzero maximal minor whose column choice is
the identity (all `ω` columns): the column selection produced by the rank/minors criterion
is a permutation of `Fin ω`, which changes the determinant only by its sign. -/
theorem exists_minor_det_ne_zero_of_rank {q ω : ℕ} (M : Matrix (Fin q) (Fin ω) ℂ)
    (h : M.rank = ω) :
    ∃ e : Fin ω ↪ Fin q, (M.submatrix (e : Fin ω → Fin q) id).det ≠ 0 := by
  obtain ⟨ρ, κ, hρ, hκ, hdet⟩ := PaperI.exists_det_submatrix_ne_zero_of_rank M h
  have hbij : Function.Bijective κ := Finite.injective_iff_bijective.mp hκ
  set σ : Equiv.Perm (Fin ω) := Equiv.ofBijective κ hbij with hσ
  have hκσ : (σ : Fin ω → Fin ω) = κ := rfl
  have hsub : M.submatrix ρ κ = (M.submatrix ρ id).submatrix id (σ : Fin ω → Fin ω) := by
    rw [Matrix.submatrix_submatrix]
    simp [hκσ]
  rw [hsub, Matrix.det_permute'] at hdet
  refine ⟨⟨ρ, hρ⟩, ?_⟩
  intro h0
  have h0' : (M.submatrix ρ id).det = 0 := h0
  exact hdet (by rw [h0', mul_zero])

/-- Evaluating a maximal minor of the pencil at `lam : ℂ` is the corresponding minor of the
evaluated matrix `lam • X − G`. -/
theorem eval_map_minors_pencil {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℚ)
    (e : Fin ω ↪ Fin q) (lam : ℂ) :
    Polynomial.eval lam ((minors (pencil X G) e).map (algebraMap ℚ ℂ))
      = ((lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).submatrix
          (e : Fin ω → Fin q) id).det := by
  have hmat : ((pencil X G).submatrix (e : Fin ω → Fin q) id).map
        (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) lam)
      = (lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).submatrix
          (e : Fin ω → Fin q) id := by
    ext i j
    show Polynomial.eval₂ (algebraMap ℚ ℂ) lam (pencil X G (e i) j)
      = lam * (algebraMap ℚ ℂ) (X (e i) j) - (algebraMap ℚ ℂ) (G (e i) j)
    rw [pencil_apply]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
    ring
  have hdet := RingHom.map_det (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) lam)
    ((pencil X G).submatrix (e : Fin ω → Fin q) id)
  rw [← Polynomial.eval₂_eq_eval_map, minors,
    show Polynomial.eval₂ (algebraMap ℚ ℂ) lam
        ((pencil X G).submatrix (e : Fin ω → Fin q) id).det
      = (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) lam)
          ((pencil X G).submatrix (e : Fin ω → Fin q) id).det from rfl,
    hdet,
    show (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) lam).mapMatrix
        ((pencil X G).submatrix (e : Fin ω → Fin q) id)
      = ((pencil X G).submatrix (e : Fin ω → Fin q) id).map
          (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) lam) from rfl,
    hmat]

/-- **Claim 16, (i) ⟺ (ii) ⟺ (iii).**  For `X G : Matrix (Fin q) (Fin ω) ℚ` the pencil
`λX − G` has full column rank `ω` at every complex parameter exactly when its maximal
minors have no common complex root, and by
`pencilMinors_gcd_isConst_iff_no_common_complex_root` this is also exactly when the gcd of
the minors in `ℚ[λ]` is a nonzero constant. -/
theorem rank_eq_iff_no_common_complex_root {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℚ) :
    (∀ lam : ℂ, (lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).rank = ω)
      ↔ NoCommonComplexRoot (pencilMinors X G) := by
  constructor
  · intro h z
    obtain ⟨e, hdet⟩ := exists_minor_det_ne_zero_of_rank _ (h z)
    exact ⟨e, by
      show Polynomial.eval z ((minors (pencil X G) e).map (algebraMap ℚ ℂ)) ≠ 0
      rw [eval_map_minors_pencil]
      exact hdet⟩
  · intro h
    exact claim16_iii_implies_i_of_gcd_isConst X G
      ((pencilMinors_gcd_isConst_iff_no_common_complex_root X G).mpr h)

/-! ## The Bézout hypothesis of `claim16_iii_implies_iv` is a strengthening of (iii) -/

/-- A family with a `ℚ[λ]`-Bézout identity has a constant gcd: the gcd divides every member,
hence divides the combination `1`, so it has degree `0` and is a nonzero constant. -/
theorem gcd_isConst_of_bezout {ι : Type*} [Fintype ι] {f : ι → ℚ[X]}
    (h : ∃ g : ι → ℚ[X], (∑ a, g a * f a) = 1) : FamilyGcdIsConst f := by
  classical
  obtain ⟨g, hg⟩ := h
  set d : ℚ[X] := Finset.univ.gcd f with hd
  have hdvd : d ∣ (1 : ℚ[X]) := by
    rw [← hg]
    exact Finset.dvd_sum fun a _ =>
      dvd_mul_of_dvd_right (Finset.gcd_dvd (Finset.mem_univ a)) (g a)
  have hdne : d ≠ 0 := by
    obtain ⟨u, hu⟩ := hdvd
    intro h0
    rw [h0, zero_mul] at hu
    exact one_ne_zero hu
  have hdeg : d.natDegree = 0 := by
    have hle := Polynomial.natDegree_le_of_dvd hdvd one_ne_zero
    simpa using hle
  have hdC : d = Polynomial.C (d.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hcoeff : d.coeff 0 ≠ 0 := by
    have hlc : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hdne
    rwa [← Polynomial.coeff_natDegree, hdeg] at hlc
  exact ⟨d.coeff 0, hcoeff, by rw [← hd]; exact hdC⟩

/-- The hypothesis of `claim16_iii_implies_iv` (a degree-bounded `ℚ[λ]`-Bézout family for the
maximal minors) implies the gcd form (iii) of the claim.  Hence (iii) is the *weaker* of the
two, and the existing `claim16_iii_implies_iv` takes a strictly stronger hypothesis. -/
theorem gcd_isConst_of_bezout_pencil {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℚ)
    (hbez : ∃ g : (Fin ω ↪ Fin q) → ℚ[X],
      (∑ e, g e * minors (pencil X G) e) = 1 ∧ ∀ e, (g e).natDegree < ω) :
    FamilyGcdIsConst (pencilMinors X G) := by
  obtain ⟨g, hg, -⟩ := hbez
  exact gcd_isConst_of_bezout ⟨g, hg⟩

/-- **Claim 16, (i) ⟺ (iii).**  Full column rank of the pencil at every complex parameter
exactly when the gcd of its maximal minors in `ℚ[λ]` is a nonzero constant. -/
theorem claim16_i_iff_iii {q ω : ℕ} (X G : Matrix (Fin q) (Fin ω) ℚ) :
    (∀ lam : ℂ, (lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).rank = ω)
      ↔ FamilyGcdIsConst (pencilMinors X G) :=
  (rank_eq_iff_no_common_complex_root X G).trans
    (pencilMinors_gcd_isConst_iff_no_common_complex_root X G).symm

/-! ## Sanity checks: the two predicates are not vacuous -/

/-- A `True` point for (ii): the constant family `1` has no common root. -/
example : NoCommonComplexRoot (fun _ : Fin 1 => (1 : ℚ[X])) := by
  intro z
  exact ⟨0, by simp⟩

/-- A `False` point for (ii): the family `λ` has the common root `0`. -/
example : ¬ NoCommonComplexRoot (fun _ : Fin 1 => (Polynomial.X : ℚ[X])) := by
  intro h
  obtain ⟨i, hi⟩ := h 0
  simp at hi

/-- The same `True` point, run through (ii) ⟹ (iii): the gcd of the constant family `1`
is the nonzero constant `1`. -/
example : FamilyGcdIsConst (fun _ : Fin 1 => (1 : ℚ[X])) :=
  gcd_isConst_of_no_common_complex_root (by intro z; exact ⟨0, by simp⟩)

end

end Q1Paper

/-! ## Axiom audit -/

