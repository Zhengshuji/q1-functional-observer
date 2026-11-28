import Q1Paper.PaperV.MainTheorems

/-!
Q1Paper/PaperV/ClaimsCheck.lean

Machine-checked index: one `#check` per formalised item of `Claims.lean`.  A rename
breaks this build instead of silently invalidating the claims table.  The twenty-eight
declarations here are exactly the twenty-eight `#print axioms` lines of `Audit.lean`.
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

-- §IV  Proposition 14, conclusion step
#check @Q1Paper.PaperV.rank_lt_of_cols_zero
#check @Q1Paper.PaperV.column_zero_of_mem

-- §V  Theorem 17, structure step
#check @Q1Paper.PaperV.map_mem_of_le_sup
#check @Q1Paper.PaperV.invariant_iff_compat_of_le

-- §IV  Proposition 15 (coefficient test)
#check @Q1Paper.PaperV.evalRingHom_apply
#check @Q1Paper.PaperV.eval_zero_iff_coeff_eval_zero
#check @Q1Paper.PaperV.forall_eval_zero_iff_forall_coeff
#check @Q1Paper.PaperV.exists_forall_eval_zero_iff_exists_forall_coeff

-- §IV  Proposition 18 (column dependence, rank kernel)
#check @Q1Paper.PaperV.rank_lt_of_le_ker
#check @Q1Paper.PaperV.matrix_rank_lt_of_le_ker

-- §II  Theorem 1, product dimension
#check @Q1Paper.PaperV.mem_pi_const
#check @Q1Paper.PaperV.finrank_pi_const
#check @Q1Paper.PaperV.finrank_iInf_comap_proj
#check @Q1Paper.PaperV.le_of_finrank_eq_one

-- UnitIdeal.lean (Bezout step)
#check @Q1Paper.PaperV.exists_combination_eq_one_of_gcd_eq_one
#check @Q1Paper.PaperV.ideal_span_eq_top_of_gcd_eq_one
#check @Q1Paper.PaperV.exists_combination_eq_one
#check @Q1Paper.PaperV.exists_common_root_of_not_isUnit
#check @Q1Paper.PaperV.isUnit_gcd_iff_no_common_root
#check @Q1Paper.PaperV.eval_det_submatrix
#check @Q1Paper.PaperV.exists_eval_ne_zero_of_isUnit_gcd
#check @Q1Paper.PaperV.exists_submatrix_det_ne_zero_of_le_rank
#check @Q1Paper.PaperV.le_rank_of_det_submatrix_ne_zero
#check @Q1Paper.PaperV.le_rank_map_of_isUnit_gcd_minor
