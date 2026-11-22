/-
PaperI.lean

Entry point of the Paper I formalization (feasibility, compression, finite
certificate, fixed-order and FPT upper bounds).  It imports the Paper I
modules only; the companion papers' modules are deliberately absent.

Build:
  lake build Q1Paper.PaperI.MainTheorems
  lake env lean Q1Paper/PaperI/Audit.lean
-/

import Q1Paper.PaperI.MainTheorems
