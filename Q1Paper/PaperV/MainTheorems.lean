import Q1Paper.PaperV.Specialize
import Q1Paper.PaperV.Fibre
import Q1Paper.PaperV.ColumnDrop
import Q1Paper.PaperV.LeadingCoeff
import Q1Paper.PaperV.GcdRoot
import Q1Paper.PaperV.Invariant
import Q1Paper.PaperV.CoeffTest
import Q1Paper.PaperV.KerRank
import Q1Paper.PaperV.FibreDim
import Q1Paper.PaperV.UnitIdeal
import Q1Paper.PaperV.FamilyGcd
import Q1Paper.PaperV.MinorEval
import Q1Paper.PaperV.RankMinor
import Q1Paper.PaperV.Criterion
import Q1Paper.PaperV.SpectralRank
import Q1Paper.PaperV.UnionZeros
import Q1Paper.PaperV.RootBound
import Q1Paper.PaperV.CriticalSet
import Q1Paper.PaperV.UniformBadness
import Q1Paper.PaperV.Necessity
import Q1Paper.PaperV.Gauss
import Q1Paper.PaperV.CriterionNecessity
import Q1Paper.PaperV.Enumeration

/-!
Q1Paper/PaperV/MainTheorems.lean

Entry point of Paper V's Lean development: the fibre (Theorem 2) and the
specialisation lemma (Lemma 5) that carries the criterion.

Scope note.  The paper's Theorems 4-17 are of three kinds, and this file states which
kind this repository formalises.

* **Formalised here.**  Theorem 2 (the fibre is a coset of `T ⊓ U`, nonempty exactly
  when the translate lies in `U + T`) and Lemma 5 (specialisation does not drop the
  λ-degree; divisibility is preserved), together with the corollary that a positive
  degree divisor with constant leading coefficient stays positive after specialising.
  Lemma 5 is the only non-trivial step of the criterion of Theorem 4.

* **Paper only, with a recorded reason.**  Theorem 13 (fixed spectral factor)
  uses the dimension of an incidence variety; Corollary 12 and Theorem 14 (the bad set is
  closed on each stratum) use quantifier elimination over the coefficient space, and the
  global statement is false (Example 27); Theorem 6 (intrinsic form) is paper-side.  These
  are recorded as paper proofs in the artifact's evidence table, not as Lean kernels.
  Theorem 4 itself is complete in matrix form: sufficiency in `Criterion.lean`, necessity in
  `CriterionNecessity.lean` (`rank_lt_of_gcd_pos`).

* **Certified exactly, not formalised.**  The examples of §V are decided by exact
  rational arithmetic in `verification/` (minors symbolically, gcd in `ℂ(t)[λ]`, and the
  original conditions re-verified on the realisable instances).
-/
