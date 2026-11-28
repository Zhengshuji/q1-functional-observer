import Q1Paper.PaperV.MainTheorems

/-!
Q1Paper/PaperV/Audit.lean

The axiom footprint of every declaration of Paper V's Lean development.

Hand-written (the Paper V tree is small; `scripts/generate_audit.py` generates the
Paper II counterpart).  Every audited declaration must depend only on `propext`,
`Classical.choice` and `Quot.sound`; `scripts/check_paperI_axioms.py` enforces this on
the output of `lake env lean Q1Paper/PaperV/Audit.lean`.  The twenty-four lines here are
exactly the twenty-four `#check`s of `ClaimsCheck.lean`.
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

-- KerRank.lean (Proposition 18, rank kernel)
#print axioms Q1Paper.PaperV.rank_lt_of_le_ker
#print axioms Q1Paper.PaperV.matrix_rank_lt_of_le_ker

-- FibreDim.lean (Theorem 1, product dimension)
#print axioms Q1Paper.PaperV.mem_pi_const
#print axioms Q1Paper.PaperV.finrank_pi_const
#print axioms Q1Paper.PaperV.finrank_iInf_comap_proj
