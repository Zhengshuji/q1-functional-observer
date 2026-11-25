/-
Q1Paper/PaperII/ClaimsCheck.lean

Machine-checked index: one `#check` per item of `Claims.lean`.  A rename breaks
this build instead of silently invalidating the claims table.
-/

import Q1Paper.PaperII.MainTheorems

-- §II  Standing results (from Paper I, reused)
#check @Q1Paper.claim4_sandwich
#check @Q1Paper.claim4_converse
#check @Q1Paper.claim5_conditions_depend_on_W
#check @Q1Paper.claim6_struct

-- §II  Paper II's own interface
#check @Q1Paper.PaperII.t
#check @Q1Paper.PaperII.t_eq_finrank_sub
#check @Q1Paper.PaperII.t_le_iff
#check @Q1Paper.PaperII.map_rowSpace_Mcol
#check @Q1Paper.PaperII.isFeasible_pairRowSpace_iff

-- §III  The sandwich in Paper II's form
#check @Q1Paper.PaperII.decC_to_feasible
#check @Q1Paper.PaperII.DEC_to_feasible_c
#check @Q1Paper.PaperII.feasible_to_DEC

-- §III  Monotonicity and saturation
#check @Q1Paper.PaperII.decC_mono
#check @Q1Paper.PaperII.dec_mono_complex
#check @Q1Paper.PaperII.dec_saturates

-- §III  Minimum order
#check @Q1Paper.PaperII.tMin_le_iff_dec
#check @Q1Paper.PaperII.tMin_le_two_ell
#check @Q1Paper.PaperII.dec_sInf_tMinSet
#check @Q1Paper.PaperII.exists_least_of_monotone
#check @Q1Paper.PaperII.omega_le_ell
#check @Q1Paper.PaperII.t_le_two_ell

-- §III  The spectral lower bound
#check @Q1Paper.PaperII.lowerBound_core
#check @Q1Paper.PaperII.lowerBound_sub
