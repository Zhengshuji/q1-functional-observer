import Q1Paper.PaperV.MainTheorems

/-!
Q1Paper/PaperV/ClaimsCheck.lean

Machine-checked index: one `#check` per formalised item of `Claims.lean`.  A rename
breaks this build instead of silently invalidating the claims table.  The eleven
declarations here are exactly the eleven `#print axioms` lines of `Audit.lean`.
-/

-- §II  The fibre (Theorem 1)
#check @Q1Paper.PaperV.fibre
#check @Q1Paper.PaperV.mem_fibre
#check @Q1Paper.PaperV.fibre_nonempty_iff
#check @Q1Paper.PaperV.fibre_eq_coset
#check @Q1Paper.PaperV.fibre_prod_nonempty_iff

-- §III  Lemma 2 and its corollary
#check @Q1Paper.PaperV.natDegree_map_eval_of_leadingCoeff_const
#check @Q1Paper.PaperV.map_dvd_of_dvd
#check @Q1Paper.PaperV.specialized_common_factor

-- §III  The λ-leading coefficient of a d'-minor (Theorem 4's hypothesis)
#check @Q1Paper.PaperV.coeff_det_smul_sub_X
#check @Q1Paper.PaperV.coeff_det_smul_sub_X_ne_zero

-- §IV  Proposition 14, rank step
#check @Q1Paper.PaperV.rank_le_card_compl_of_cols_zero

-- §III  gcd is a unit ⟺ no common root (Theorem 4's algebraic core)
#check @Q1Paper.PaperV.gcd_ne_zero
#check @Q1Paper.PaperV.exists_root_of_not_isUnit
#check @Q1Paper.PaperV.isCoprime_iff_no_common_root
#check @Q1Paper.PaperV.gcd_eq_one_iff_no_common_root
