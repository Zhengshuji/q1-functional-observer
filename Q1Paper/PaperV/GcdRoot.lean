import Mathlib

/-!
Q1Paper/PaperV/GcdRoot.lean

§III, the algebraic core of the criterion: **no common root ⟺ the gcd is a unit**.

Paper statement (Theorem 4, step (i) ⟺ (ii)): the minors of the pencil have constant rank
`d'` for all `λ` exactly when their greatest common divisor is a *unit*, equivalently has
degree zero.  Over `K = ℂ(t)` this is the statement proved here for an algebraically closed
field, instantiated later at the algebraic closure of the function field.

## Why the statement is phrased with `IsCoprime`

`EuclideanDomain.gcd` is the *raw* Euclidean algorithm; Mathlib documents it as "a
(non-unique) element" (`Mathlib/Algebra/EuclideanDomain/Defs.lean`).  It is determined only
up to units.  For example over `ℂ`, tracing `gcd a b = if a = 0 then b else gcd (b % a) a`
on `f = 2X`, `g = 2X + 2` gives `gcd f g = 2`, although `f` and `g` have no common root.

So the literal statement `EuclideanDomain.gcd f g = 1 ↔ no common root` is **false**; what
holds is

* `IsCoprime f g ↔ no common root` (`isCoprime_iff_no_common_root`), with no normalization
  convention at all, and
* `gcd f g = 1 ↔ no common root` **provided the gcd is monic**
  (`gcd_eq_one_iff_no_common_root`, hypothesis `hmon`) — the convention under which "the gcd
  is `1`" is used in the paper.  Over `ℚ` this is the `GCDMonoid ℚ[X]` instance Mathlib uses,
  so `hmon` is automatic there.

This is exactly the normalization-freeness that the paper's "unit" and "degree zero" phrasing
enjoys: neither `gcd = 1` nor `deg gcd = 0` is asserted without it.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

open Polynomial

namespace Q1Paper.PaperV

variable {K : Type*}

attribute [local instance] Classical.decEq Classical.propDecidable

section Field

variable [Field K]

/-- The gcd of `f` and `g` is nonzero as soon as `f` is. -/
theorem gcd_ne_zero {f g : K[X]} (hf : f ≠ 0) : EuclideanDomain.gcd f g ≠ 0 := by
  intro h0
  have hd : EuclideanDomain.gcd f g ∣ f := EuclideanDomain.gcd_dvd_left f g
  rw [h0] at hd
  exact hf (zero_dvd_iff.mp hd)

/-- A nonzero non-unit polynomial over an algebraically closed field has a root. -/
theorem exists_root_of_not_isUnit [IsAlgClosed K] {d : K[X]} (hd : d ≠ 0)
    (hu : ¬ IsUnit d) : ∃ x : K, d.IsRoot x := by
  have hdeg : d.natDegree ≠ 0 := by
    intro h
    apply hu
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp h
    have hc0 : c ≠ 0 := by
      intro hc'
      rw [hc', Polynomial.C.map_zero] at hc
      exact hd hc.symm
    rw [← hc]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
  have hpos : 0 < d.natDegree := Nat.pos_of_ne_zero hdeg
  have hdpos : d.degree ≠ 0 :=
    ne_of_gt ((Polynomial.natDegree_pos_iff_degree_pos (p := d)).mp hpos)
  exact IsAlgClosed.exists_root d hdpos

/-- **Theorem 4's algebraic core (normalization-free).** Two nonzero polynomials over an
algebraically closed field are coprime iff they have no common root.  "Coprime" is the
unit-normalized form of "the gcd is a unit", so this needs no convention for `gcd`. -/
theorem isCoprime_iff_no_common_root [IsAlgClosed K] (f g : K[X]) (hf : f ≠ 0)
    (hg : g ≠ 0) : IsCoprime f g ↔ ∀ x : K, ¬ (f.IsRoot x ∧ g.IsRoot x) := by
  constructor
  · rintro ⟨a, b, hab⟩ x hx
    obtain ⟨hfx, hgx⟩ := hx
    simp only [Polynomial.IsRoot] at hfx hgx
    have key : a.eval x * f.eval x + b.eval x * g.eval x = 1 := by
      have := congrArg (Polynomial.eval x) hab
      simpa using this
    simp only [hfx, hgx, mul_zero, zero_add, add_zero] at key
    exact one_ne_zero key.symm
  · intro h
    by_contra hcop
    have hd0 : EuclideanDomain.gcd f g ≠ 0 := gcd_ne_zero hf
    have hu : ¬ IsUnit (EuclideanDomain.gcd f g) := by
      rwa [EuclideanDomain.gcd_isUnit_iff]
    obtain ⟨x, hx⟩ := exists_root_of_not_isUnit hd0 hu
    have hxd : X - C x ∣ EuclideanDomain.gcd f g := dvd_iff_isRoot.mpr hx
    exact h x ⟨dvd_iff_isRoot.mp (hxd.trans (EuclideanDomain.gcd_dvd_left f g)),
               dvd_iff_isRoot.mp (hxd.trans (EuclideanDomain.gcd_dvd_right f g))⟩

/-- **Paper form.** With the gcd in monic (normalized) form — the convention under which one
writes "the gcd equals `1`" — the equivalence holds literally. -/
theorem gcd_eq_one_iff_no_common_root [IsAlgClosed K] (f g : K[X]) (hf : f ≠ 0) (hg : g ≠ 0)
    (hmon : (EuclideanDomain.gcd f g).Monic) :
    EuclideanDomain.gcd f g = 1 ↔ ∀ x : K, ¬ (f.IsRoot x ∧ g.IsRoot x) := by
  constructor
  · rintro h1 x hx
    obtain ⟨hfx, hgx⟩ := hx
    have h1' : X - C x ∣ f := dvd_iff_isRoot.mpr hfx
    have h2' : X - C x ∣ g := dvd_iff_isRoot.mpr hgx
    have h3 : X - C x ∣ EuclideanDomain.gcd f g := EuclideanDomain.dvd_gcd h1' h2'
    rw [h1] at h3
    have hle : (X - C x).natDegree ≤ (1 : K[X]).natDegree := natDegree_le_of_dvd h3 one_ne_zero
    rw [natDegree_X_sub_C, natDegree_one] at hle
    omega
  · intro h
    have hdvd_f : EuclideanDomain.gcd f g ∣ f := EuclideanDomain.gcd_dvd_left f g
    have hdeg : (EuclideanDomain.gcd f g).natDegree = 0 := by
      by_contra hne
      have hpos : 0 < (EuclideanDomain.gcd f g).natDegree := Nat.pos_of_ne_zero hne
      have hdpos : (EuclideanDomain.gcd f g).degree ≠ 0 :=
        ne_of_gt ((Polynomial.natDegree_pos_iff_degree_pos (p := EuclideanDomain.gcd f g)).mp hpos)
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (EuclideanDomain.gcd f g) hdpos
      have hxd : X - C x ∣ EuclideanDomain.gcd f g := dvd_iff_isRoot.mpr hx
      exact h x ⟨dvd_iff_isRoot.mp (hxd.trans hdvd_f),
                 dvd_iff_isRoot.mp (hxd.trans (EuclideanDomain.gcd_dvd_right f g))⟩
    exact (Monic.natDegree_eq_zero hmon).mp hdeg

/-- **Theorem 4 (converse shape).** Over an algebraically closed field, a gcd that is not a unit forces a
common root: this is the step "a generic gcd of positive degree makes the fibre bad", used in the converse
direction of the criterion. -/
theorem exists_common_root_of_not_isUnit {K : Type*} [Field K] [IsAlgClosed K]
    {f g : Polynomial K} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ¬ IsUnit (EuclideanDomain.gcd f g)) :
    ∃ x : K, f.IsRoot x ∧ g.IsRoot x := by
  have hdvd_left : EuclideanDomain.gcd f g ∣ f := EuclideanDomain.gcd_dvd_left f g
  have hdvd_right : EuclideanDomain.gcd f g ∣ g := EuclideanDomain.gcd_dvd_right f g
  have hd0 : EuclideanDomain.gcd f g ≠ 0 := ne_zero_of_dvd_ne_zero hf hdvd_left
  have hpos : 0 < (EuclideanDomain.gcd f g).natDegree := by
    rcases Nat.eq_zero_or_pos (EuclideanDomain.gcd f g).natDegree with hzero | hpos
    · exfalso
      have hdeg0 : (EuclideanDomain.gcd f g).degree = 0 := by
        rw [Polynomial.degree_eq_natDegree hd0, hzero]
        simp
      exact h (Polynomial.isUnit_iff_degree_eq_zero.mpr hdeg0)
    · exact hpos
  have hdeg : (EuclideanDomain.gcd f g).degree ≠ 0 :=
    ne_of_gt (by rwa [Polynomial.natDegree_pos_iff_degree_pos] at hpos)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (EuclideanDomain.gcd f g) hdeg
  refine ⟨x, ?_, ?_⟩
  · rw [Polynomial.IsRoot.def] at hx ⊢
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd_left hx
  · rw [Polynomial.IsRoot.def] at hx ⊢
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd_right hx


end Field

end Q1Paper.PaperV
