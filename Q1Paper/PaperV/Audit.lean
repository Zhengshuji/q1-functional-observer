import Q1Paper.PaperV.MainTheorems

/-!
Q1Paper/PaperV/Audit.lean

The axiom footprint of every declaration of Paper V's Lean development.

Hand-written (the Paper V tree is small; `scripts/generate_audit.py` generates the
Paper II counterpart).  Every audited declaration must depend only on `propext`,
`Classical.choice` and `Quot.sound`; `scripts/check_paperI_axioms.py` enforces this on
the output of `lake env lean Q1Paper/PaperV/Audit.lean`.  The fifty-two lines here are
exactly the fifty-two `#check`s of `ClaimsCheck.lean`.
-/

-- Fibre.lean
#print axioms Q1Paper.PaperV.fibre
#print axioms Q1Paper.PaperV.mem_fibre
#print axioms Q1Paper.PaperV.fibre_nonempty_iff
#print axioms Q1Paper.PaperV.fibre_eq_coset
#print axioms Q1Paper.PaperV.fibre_prod_nonempty_iff

-- Specialize.lean
#print axioms Q1Paper.PaperV.natDegree_map_eval_of_leadingCoeff_const
#print axioms Q1Paper.PaperV.map_dvd_of_dvd
#print axioms Q1Paper.PaperV.specialized_common_factor

-- LeadingCoeff.lean
#print axioms Q1Paper.PaperV.coeff_det_smul_sub_X
#print axioms Q1Paper.PaperV.coeff_det_smul_sub_X_ne_zero

-- ColumnDrop.lean
#print axioms Q1Paper.PaperV.rank_le_card_compl_of_cols_zero

-- GcdRoot.lean
#print axioms Q1Paper.PaperV.gcd_ne_zero
#print axioms Q1Paper.PaperV.exists_root_of_not_isUnit
#print axioms Q1Paper.PaperV.isCoprime_iff_no_common_root
#print axioms Q1Paper.PaperV.gcd_eq_one_iff_no_common_root

-- ColumnDrop.lean (conclusion step)
#print axioms Q1Paper.PaperV.rank_lt_of_cols_zero
#print axioms Q1Paper.PaperV.column_zero_of_mem

-- Invariant.lean
#print axioms Q1Paper.PaperV.map_mem_of_le_sup
#print axioms Q1Paper.PaperV.invariant_iff_compat_of_le

-- CoeffTest.lean
#print axioms Q1Paper.PaperV.evalRingHom_apply
#print axioms Q1Paper.PaperV.eval_zero_iff_coeff_eval_zero
#print axioms Q1Paper.PaperV.forall_eval_zero_iff_forall_coeff
#print axioms Q1Paper.PaperV.exists_forall_eval_zero_iff_exists_forall_coeff

-- KerRank.lean (Proposition 17, rank kernel)
#print axioms Q1Paper.PaperV.rank_lt_of_le_ker
#print axioms Q1Paper.PaperV.matrix_rank_lt_of_le_ker

-- FibreDim.lean (Theorem 2, product dimension)
#print axioms Q1Paper.PaperV.mem_pi_const
#print axioms Q1Paper.PaperV.finrank_pi_const
#print axioms Q1Paper.PaperV.finrank_iInf_comap_proj
#print axioms Q1Paper.PaperV.le_of_finrank_eq_one

-- UnitIdeal.lean (Bezout step)
#print axioms Q1Paper.PaperV.exists_combination_eq_one_of_gcd_eq_one
#print axioms Q1Paper.PaperV.ideal_span_eq_top_of_gcd_eq_one
#print axioms Q1Paper.PaperV.exists_combination_eq_one
#print axioms Q1Paper.PaperV.exists_common_root_of_not_isUnit
#print axioms Q1Paper.PaperV.isUnit_gcd_iff_no_common_root
#print axioms Q1Paper.PaperV.eval_det_submatrix
#print axioms Q1Paper.PaperV.exists_eval_ne_zero_of_isUnit_gcd
#print axioms Q1Paper.PaperV.exists_submatrix_det_ne_zero_of_le_rank
#print axioms Q1Paper.PaperV.le_rank_of_det_submatrix_ne_zero
#print axioms Q1Paper.PaperV.le_rank_map_of_isUnit_gcd_minor
#print axioms Q1Paper.PaperV.not_isUnit_gcd_of_forall_eval_eq_zero

-- UnionZeros.lean (Theorem 13 covering step)
#print axioms Q1Paper.PaperV.eq_zero_of_forall_eval_eq_zero
#print axioms Q1Paper.PaperV.exists_forall_eval_ne_zero
#print axioms Q1Paper.PaperV.exists_eq_zero_of_forall_exists_eval_eq_zero

-- Fibre.lean / FibreDim.lean (Theorem 2, assembled)
#print axioms Q1Paper.PaperV.fibre_prod_coset
#print axioms Q1Paper.PaperV.fibre_dir_finrank
#print axioms Q1Paper.PaperV.exists_minor_ne_zero_of_det_ne_zero

-- RootBound.lean (Theorem 8 counting step)
#print axioms Q1Paper.PaperV.card_roots_le_natDegree
#print axioms Q1Paper.PaperV.exists_ne_root_of_card
#print axioms Q1Paper.PaperV.rank_mul_of_det_ne_zero
#print axioms Q1Paper.PaperV.rank_smul_sub_mul_of_det_ne_zero

-- CriticalSet.lean (Theorem 13, finiteness of the critical set)
#print axioms Q1Paper.PaperV.natDegree_det_smul_sub_X_le
#print axioms Q1Paper.PaperV.card_roots_le_of_coeff_ne_zero
