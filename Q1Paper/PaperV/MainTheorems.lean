import Q1Paper.PaperV.Specialize
import Q1Paper.PaperV.Fibre
import Q1Paper.PaperV.ColumnDrop

/-!
Q1Paper/PaperV/MainTheorems.lean

Entry point of Paper V's Lean development: the fibre (Theorem 1) and the
specialisation lemma (Lemma 2) that carries the criterion.

Scope note.  The paper's Theorems 4-17 are of three kinds, and this file states which
kind this repository formalises.

* **Formalised here.**  Theorem 1 (the fibre is a coset of `T 鈯?U`, nonempty exactly
  when the translate lies in `U + T`) and Lemma 2 (specialisation does not drop the
  位-degree; divisibility is preserved), together with the corollary that a positive
  degree divisor with constant leading coefficient stays positive after specialising.
  Lemma 2 is the only non-trivial step of the criterion of Theorem 4.

* **Paper only, with a recorded reason.**  Theorem 4's gcd criterion is a statement
  about gcds in `K(t)[位]` for a *matrix* pencil, whose formalisation needs multivariate
  polynomial gcds and matrix minors simultaneously; Theorem 11 (fixed spectral factor)
  uses the dimension of an incidence variety; Theorem 12 (the bad set is closed) uses
  quantifier elimination over the coefficient space.  These are recorded as paper proofs
  in the artifact's evidence table, not as Lean kernels.

* **Certified exactly, not formalised.**  The examples of 搂V are decided by exact
  rational arithmetic in `verification/` (minors symbolically, gcd in `鈩歔位]`, and the
  original conditions re-verified on the realisable instances).
-/
