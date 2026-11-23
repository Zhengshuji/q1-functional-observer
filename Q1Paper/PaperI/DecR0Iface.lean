/-
Q1Paper/PaperI/DecR0Iface.lean

An **interface** for the `r = 0` decision problem (R0) of Proposition 4, kept separate from any
particular algorithm.

`PaperI/Prop4.lean` defines `decR0` as `decide (R0)` — a `noncomputable` *specification* of a
decision function, not an algorithm.  The honest formal statement of "the `r = 0` case is
decidable" separates three things:

* the mathematical criterion — (R0), restated verbatim from `PaperI/Prop4.lean`
  (the existential of part (v) of Claim 16, i.e. `prop4_r0_iff_spectral`);
* the existence of a decision procedure — `R0Solver`: a `Bool`-valued `run` together with the
  proof `run X G = true ↔ (R0)` (soundness and completeness in a single iff);
* its cost — deliberately *not* part of the interface.  A **computable** `run` would need a
  computable rank (a minor-selection rank test, or a rational Gaussian-elimination /
  linear-system solver) together with a proof that it decides solvability of the block system
  in the unknowns `S_0, …, S_{2ω-2}`.  At the pinned Mathlib (`leanprover/lean4:v4.35.0`,
  Mathlib rev `f0b4c81`) there is no computable rank, no RREF existence and no rational
  solver; the project's Bareiss development (`PaperI/BareissTableau.lean`,
  `PaperI/BareissAssemble.lean`) supplies fraction-free elimination only for square matrices
  with nonzero leading principal minors.  This file therefore leaves computability and cost
  external on purpose: `R0Solver` is the contract an executable solver must meet, and
  `spectral_decidable_of_solver` turns any inhabitant into a `Decidable` instance for the
  spectral condition.  `R0Solver_nonempty` shows the interface is inhabited (classically, by
  exactly the `decR0` specification), so the contract is not vacuous.

This is a *correctness/interface* statement, not a complexity statement.

Note on the shape of the `Decidable` result: `Decidable p` lives in `Type`, so Lean's
`theorem` command refuses a declaration whose type ends in `Decidable _` ("type of theorem
… is not a proposition").  `spectral_decidable_of_solver` is therefore a `def` (same name,
same type); `R0Solver_nonempty`, whose type is the proposition `Nonempty _`, stays a
`theorem`.

No `sorry`, no `admit`, no new axioms.
-/

import Q1Paper.PaperI.Prop4

open Matrix
open scoped BigOperators

namespace Q1Paper

/-! ## 1. The solver interface -/

/-- A decision procedure for (R0), the `r = 0` rational linear system of Proposition 4.

`run X G = true` must hold exactly when the block system (R0) — unknown blocks
`S_0, …, S_{2ω-2} : Matrix (Fin ω) (Fin q) ℚ` with `S_0 G = -1`, `S_{j-1} X - S_j G = 0`,
`S_{2ω-2} X = 0` — is solvable.  The field `correct` bundles soundness and completeness.

Nothing here asserts that `run` is computable or polynomial-time: that is the external
ingredient described in the file docstring (a computable rank / rational solver). -/
structure R0Solver (q ω : ℕ) where
  run : Matrix (Fin q) (Fin ω) ℚ → Matrix (Fin q) (Fin ω) ℚ → Bool
  correct : ∀ (X G : Matrix (Fin q) (Fin ω) ℚ), 1 ≤ ω →
    (run X G = true ↔
      (∃ S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin q) ℚ,
        S 0 * G = -1 ∧
        (∀ j : Fin (2 * ω - 2), S (Fin.castSucc j) * X - S (Fin.succ j) * G = 0) ∧
        S (Fin.last (2 * ω - 2)) * X = 0))

/-- **Any solver decides the spectral condition.**

Rewrite (R0) as the spectral condition with `prop4_r0_iff_spectral`; the solver's `correct`
field then gives `S.run X G = true ↔ ∀ λ, rank (λ • X − G) = ω`, and `decidable_of_iff`
transports the decision of the `Bool` equality `S.run X G = true` to the spectral statement.
Evaluating the resulting instance reduces to evaluating `S.run X G`: the proof component is
erased.  (This is a `def`, not a `theorem`, because `Decidable` is `Type`-valued.) -/
def spectral_decidable_of_solver (q ω : ℕ) (hω : 1 ≤ ω) (S : R0Solver q ω) :
    ∀ (X G : Matrix (Fin q) (Fin ω) ℚ),
      Decidable (∀ lam : ℂ, (lam • X.map (algebraMap ℚ ℂ) - G.map (algebraMap ℚ ℂ)).rank = ω) := by
  intro X G
  exact decidable_of_iff (S.run X G = true)
    ((S.correct X G hω).trans (prop4_r0_iff_spectral hω X G))

/-! ## 2. Non-vacuity: the interface is inhabited -/

/-- **The interface is inhabited.**

Take `run := decR0 q ω` — the classical `decide` of the (R0) predicate, exactly the
specification used in `PaperI/Prop4.lean` — and `correct` from `decR0_correct` composed with
`prop4_r0_iff_spectral`.  This shows the contract of §1 is satisfiable; it does *not* provide
an executable solver (see the file docstring). -/
theorem R0Solver_nonempty (q ω : ℕ) (hω : 1 ≤ ω) : Nonempty (R0Solver q ω) :=
  ⟨{ run := fun X G => decR0 q ω X G
     correct := fun X G _ =>
       (decR0_correct (q := q) (ω := ω) hω X G).trans
         (prop4_r0_iff_spectral (q := q) (ω := ω) hω X G).symm }⟩

end Q1Paper

/-! ## Axiom audit -/

