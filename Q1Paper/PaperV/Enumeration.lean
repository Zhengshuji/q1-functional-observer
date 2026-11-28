import Mathlib

/-!
Q1Paper/PaperV/Enumeration.lean

§V, the logical skeleton of Theorem 22's enumeration.

Paper usage: for `t = 1` every feasible `U` is `Z''`-invariant (Theorem 22's structure step, formalised
in `Invariant.lean` together with the dimension step in `FibreDim.lean`). When the invariant subspaces
of the relevant dimension form a finite set, feasibility can therefore be decided by running the
fibre test on that list.

What is formalised here is exactly the enumerative skeleton: if a finite list is *complete* (it
contains every candidate), then an existential search over the list is equivalent to the unbounded
existential, and is decidable. The construction of the list itself — enumerating the invariant
subspaces — stays paper-side.

No `sorry`, no axioms beyond Lean's three standard ones.
-/

namespace Q1Paper.PaperV

variable {α : Type*}

/-- **Theorem 22, enumerative skeleton.** If a finite list contains every point satisfying `P`, then the
unbounded existential over `P` is the same as the existential over the list. -/
theorem exists_iff_exists_mem_finset (P : α → Prop) (L : Finset α)
    (hcomplete : ∀ a, P a → a ∈ L) :
    (∃ a, P a) ↔ ∃ a ∈ L, P a := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, hcomplete a ha, ha⟩
  · rintro ⟨a, _, ha⟩
    exact ⟨a, ha⟩

/-- Consequently the search over a complete finite list decides the existential. -/
def decidable_exists_of_complete_finset (P : α → Prop) [DecidablePred P] (L : Finset α)
    (hcomplete : ∀ a, P a → a ∈ L) : Decidable (∃ a, P a) :=
  decidable_of_iff (∃ a ∈ L, P a) (exists_iff_exists_mem_finset P L hcomplete).symm

end Q1Paper.PaperV
