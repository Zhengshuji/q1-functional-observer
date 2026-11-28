import Mathlib

/-!
Q1Paper/PaperV/RootBound.lean

§V, the counting step behind Theorem 8's failure probability.

Paper usage: in the one-sided test the coefficient vector `c` is drawn from a finite grid `S_c`, and
the test fails only when the resultant `D_c` vanishes. Since `D_c` is a nonzero polynomial of degree
at most `d'` in `c`, at most `d'` of the sampled points can be bad, which is the `d'/|S_c|` term of the
paper's bound.

That is a counting statement about roots of a nonzero polynomial, proved here without any probability
theory: a nonzero polynomial of degree `n` has at most `n` roots, so a fortiori at most `n` of the
points of any finite set are roots.

* `card_roots_le_natDegree` : the roots of a nonzero polynomial inside a finite set number at most
  its degree;
* `exists_ne_root_of_card` : consequently, if the set is larger than the degree, some point of it is
  not a root — the "one-sided" part of the test.
-/

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

namespace Q1Paper.PaperV

variable {K : Type*} [Field K]

/-- A nonzero polynomial has at most `natDegree` roots inside any finite set. -/
theorem card_roots_le_natDegree (p : Polynomial K) (hp : p ≠ 0) (S : Finset K) :
    (S.filter fun x => p.IsRoot x).card ≤ p.natDegree := by
  classical
  have hsub : (S.filter fun x => p.IsRoot x) ⊆ p.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hp, hx.2⟩)
  calc (S.filter fun x => p.IsRoot x).card
      ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := by
        have h := Polynomial.card_roots hp
        rw [Polynomial.degree_eq_natDegree hp] at h
        exact_mod_cast h

/-- **Theorem 8, counting step.** If the grid is strictly larger than the degree, some grid point is
not a root: drawing uniformly from the grid therefore hits a good point with positive probability. -/
theorem exists_ne_root_of_card (p : Polynomial K) (hp : p ≠ 0) (S : Finset K)
    (hS : p.natDegree < S.card) : ∃ x ∈ S, ¬ p.IsRoot x := by
  classical
  by_contra hcon
  push_neg at hcon
  have hall : S.filter (fun x => p.IsRoot x) = S := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.1, fun hx => ⟨hx, hcon x hx⟩⟩
  have hle := card_roots_le_natDegree p hp S
  rw [hall] at hle
  omega

end Q1Paper.PaperV
