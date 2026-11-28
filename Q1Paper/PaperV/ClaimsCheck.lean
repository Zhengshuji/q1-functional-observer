import Q1Paper.PaperV.MainTheorems

/-!
Q1Paper/PaperV/ClaimsCheck.lean

Machine-checked index: one `#check` per formalised item of `Claims.lean`.  A rename
breaks this build instead of silently invalidating the claims table.
-/

-- 鎼侷I  The fibre (Theorem 1)
#check @Q1Paper.PaperV.fibre
#check @Q1Paper.PaperV.mem_fibre
#check @Q1Paper.PaperV.fibre_nonempty_iff
#check @Q1Paper.PaperV.fibre_eq_coset
#check @Q1Paper.PaperV.fibre_prod_nonempty_iff

-- 鎼侷II  Lemma 2 and its corollary
#check @Q1Paper.PaperV.natDegree_map_eval_of_leadingCoeff_const
#check @Q1Paper.PaperV.map_dvd_of_dvd
#check @Q1Paper.PaperV.specialized_common_factor
