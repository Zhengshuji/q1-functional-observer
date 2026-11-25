/-
Q1Paper/PaperII/Audit.lean

The axiom footprint of every declaration of Paper II's Lean development.

Generated from the `PaperII/` sources (declaration names only).  Every audited
declaration must depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

import Q1Paper.PaperII.Interface
import Q1Paper.PaperII.Sandwich
import Q1Paper.PaperII.Monotone
import Q1Paper.PaperII.LowerBound
import Q1Paper.PaperII.Converse
import Q1Paper.PaperII.Saturate
import Q1Paper.PaperII.MinOrder

-- Converse.lean
#print axioms Q1Paper.PaperII.WRc
#print axioms Q1Paper.PaperII.WRc_eq_map
#print axioms Q1Paper.PaperII.map_symm_map
#print axioms Q1Paper.PaperII.feasible_to_DEC

-- Interface.lean
#print axioms Q1Paper.PaperII.Mcol
#print axioms Q1Paper.PaperII.Φ
#print axioms Q1Paper.PaperII.Mcol_left
#print axioms Q1Paper.PaperII.Mcol_right
#print axioms Q1Paper.PaperII.Φ_apply
#print axioms Q1Paper.PaperII.Φ_vecMul
#print axioms Q1Paper.PaperII.map_rowSpace_Mcol
#print axioms Q1Paper.PaperII.t
#print axioms Q1Paper.PaperII.t_eq_finrank_sub
#print axioms Q1Paper.PaperII.t_le_iff
#print axioms Q1Paper.PaperII.DecOrder
#print axioms Q1Paper.PaperII.IsFeasible
#print axioms Q1Paper.PaperII.isFeasible_pairRowSpace_iff

-- LowerBound.lean
#print axioms Q1Paper.PaperII.finrank_sup_pi_le
#print axioms Q1Paper.PaperII.finrank_pi1_mono
#print axioms Q1Paper.PaperII.lowerBound_core
#print axioms Q1Paper.PaperII.lowerBound_sub

-- MinOrder.lean
#print axioms Q1Paper.PaperII.tMinSet
#print axioms Q1Paper.PaperII.tMin
#print axioms Q1Paper.PaperII.tMin_le_iff_dec
#print axioms Q1Paper.PaperII.ell
#print axioms Q1Paper.PaperII.omega_le_ell
#print axioms Q1Paper.PaperII.t_le_two_ell
#print axioms Q1Paper.PaperII.tMin_le_two_ell
#print axioms Q1Paper.PaperII.dec_sInf_tMinSet
#print axioms Q1Paper.PaperII.exists_least_of_monotone

-- Monotone.lean
#print axioms Q1Paper.PaperII.pairRowSpace_fromRows
#print axioms Q1Paper.PaperII.pairRowSpace_pad
#print axioms Q1Paper.PaperII.decC_mono_add
#print axioms Q1Paper.PaperII.decC_mono

-- Sandwich.lean
#print axioms Q1Paper.PaperII.Ac
#print axioms Q1Paper.PaperII.L0c
#print axioms Q1Paper.PaperII.Rc
#print axioms Q1Paper.PaperII.Lc
#print axioms Q1Paper.PaperII.fromRows_Lc
#print axioms Q1Paper.PaperII.TR
#print axioms Q1Paper.PaperII.W0
#print axioms Q1Paper.PaperII.WR
#print axioms Q1Paper.PaperII.W0_eq_map
#print axioms Q1Paper.PaperII.TR_eq_map
#print axioms Q1Paper.PaperII.WR_eq_map
#print axioms Q1Paper.PaperII.decC_to_feasible

-- Saturate.lean
#print axioms Q1Paper.PaperII.DEC_to_feasible_c
#print axioms Q1Paper.PaperII.t_le_t_of_le
#print axioms Q1Paper.PaperII.dec_saturates
#print axioms Q1Paper.PaperII.dec_mono_complex

