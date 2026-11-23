/-
Q1Paper/PaperI/Audit.lean

Axiom audit for the Paper I formalization.  It prints, for every declaration
that the Paper I map records as formalized, the axioms its proof depends on.
The allowed ones are `propext`, `Classical.choice` and `Quot.sound`; the check
that nothing else occurs is done by `scripts/check_paperI_axioms.py`.

This file is not imported by `PaperI.lean`: it is a build-time report.
-/

import Q1Paper.PaperI.MainTheorems

-- compression: rank identity, compression criterion, row spaces
#print axioms Q1Paper.pairMap_apply
#print axioms Q1Paper.finrank_range_pairMap_common
#print axioms Q1Paper.rank_vstack_add_rank_mul
#print axioms Q1Paper.ker_compressed_iff
#print axioms Q1Paper.G_form_iff
#print axioms Q1Subspace.rank_fromRows_eq_rank_iff
#print axioms Q1Subspace.rowSpace_eq

-- free rows and the effective dimension
#print axioms Q1Paper.finrank_freePairSpace_add_ker
#print axioms Q1Paper.finrank_domain_le_freePairSpace
#print axioms Q1Paper.kappaObs_eq_mul_freePairSpace
#print axioms KappaObs.kappaObs_eq_row_count

-- subspace reduction, projections, structure
#print axioms Q1Subspace.mem_rowSpan_iff_exists_vecMul
#print axioms Q1Subspace.rowSpan_fromRows_left
#print axioms Q1Subspace.pi1_eq_pi2_of_le_of_finrank_eq
#print axioms Q1Subspace.hasConstantRank_iff_rankIndependent
#print axioms Q1Subspace.finrank_le_two_mul_of_pi1_eq_pi2
#print axioms Q1Subspace.finrank_add_one_le_of_spectral

-- monotonicity
#print axioms Q1Paper.rank_fromRows_zero
#print axioms Q1Paper.conditions_fromRows_zero
#print axioms Q1Paper.spectralCondition_append_zero_rows

-- rank consistency and the Gram criterion
#print axioms Q1Paper.exists_mulVec_eq_iff_rank_gram
#print axioms Q1Paper.exists_solution_iff_mem_range
#print axioms Q1Paper.sum_sq_eq_zero_iff

-- Bezout with degree bound (real coefficients)
#print axioms Q1Paper.exists_bezout_family
#print axioms Q1Paper.exists_bezout_family_real
#print axioms Q1Paper.exists_avoid_complex_roots

-- degree-windowed relations (the window matrix)
#print axioms Q1Paper.windowMatrix
#print axioms Q1Paper.rowSpace_windowMatrix_eq_windowSet
#print axioms Q1Paper.mem_rowSpace_iff_exists_window
#print axioms Q1Paper.toFn_injOn_degree_lt_two_mul

-- rectangular left inverse and its degree bound
#print axioms Q1Paper.exists_leftInverse_linear
#print axioms Q1Paper.natDegree_det_le
#print axioms Q1Paper.natDegree_adjugate_le
#print axioms Q1Paper.natDegree_adjRowInverse_le
#print axioms Q1Paper.spoly_mul_pencil_eq_one

-- the statement layer of the decision problem
#print axioms Q1Paper.PaperI.rawAlgebraic
#print axioms Q1Paper.PaperI.rawSpectral
#print axioms Q1Paper.PaperI.compressedAlgebraic
#print axioms Q1Paper.PaperI.compressedSpectral
#print axioms Q1Paper.PaperI.DEC
#print axioms Q1Paper.PaperI.MINDEC

-- Claim 2 at the matrix level: raw <=> compressed
#print axioms Q1Paper.PaperI.rank_fromRows_comm
#print axioms Q1Paper.PaperI.rank_fromRows_add_map
#print axioms Q1Paper.PaperI.rank_vstack_add_rank_mul'
#print axioms Q1Paper.PaperI.rank_fromRows_eq_rank_add_mul
#print axioms Q1Paper.PaperI.ker_fromRows_eq_map
#print axioms Q1Paper.PaperI.map_ker_eq
#print axioms Q1Paper.PaperI.rawAlgebraic_iff_compressed
#print axioms Q1Paper.PaperI.rawAlgebraic_iff_rowSpace
#print axioms Q1Paper.PaperI.rawSpectral_iff_compressed
#print axioms Q1Paper.PaperI.DEC_iff_compressed
#print axioms Q1Paper.PaperI.DECℂ
#print axioms Q1Paper.PaperI.MINDECℂ
#print axioms Q1Paper.PaperI.DEC_complex_iff_compressed

-- Claim 11, the Gram step
#print axioms Q1Paper.PaperI.rowSpace_eq_range_transpose
#print axioms Q1Paper.PaperI.range_transpose_mul_self
#print axioms Q1Paper.PaperI.mem_range_transpose_iff_exists_gram
#print axioms Q1Paper.PaperI.gram_certificate

-- Claim 11, the Bezout/window step
#print axioms Q1Paper.PaperI.windowOne
#print axioms Q1Paper.PaperI.windowOne_eq_toFn
#print axioms Q1Paper.PaperI.exists_bezout_iff_mem_rowSpace_window
#print axioms Q1Paper.PaperI.mem_rowSpace_window_of_no_common_complex_root
#print axioms Q1Paper.PaperI.no_common_complex_root_of_mem_rowSpace_window
#print axioms Q1Paper.PaperI.mem_rowSpace_window_iff_no_common_complex_root

-- Claim 11, rank/minors bridge (partial: evaluation and each easy direction)
#print axioms Q1Paper.PaperI.maximalMinor
#print axioms Q1Paper.PaperI.eval_maximalMinor
#print axioms Q1Paper.PaperI.rank_le_of_det_maximalMinor_ne_zero
#print axioms Q1Paper.PaperI.exists_det_submatrix_ne_zero_of_rank_pos
#print axioms Q1Paper.PaperI.exists_injective_linearIndependent
#print axioms Q1Paper.PaperI.exists_invertible_cols
#print axioms Q1Paper.PaperI.exists_det_submatrix_ne_zero_of_rank
#print axioms Q1Paper.PaperI.rank_eq_iff_exists_det_submatrix_ne_zero

-- Claim 11, pencil level
#print axioms Q1Paper.PaperI.pencil
#print axioms Q1Paper.PaperI.pencil_map_eval
#print axioms Q1Paper.PaperI.spectral_iff_minors
#print axioms Q1Paper.PaperI.exists_factor_of_rowSpace_le
#print axioms Q1Paper.PaperI.exists_factor_of_rawAlgebraic
#print axioms Q1Paper.PaperI.rank_neg_eq
#print axioms Q1Paper.PaperI.rank_eq_of_compressedSpectral
#print axioms Q1Paper.PaperI.rank_HA_eq_rank_H_of_rawSpectral
-- Claim 11, real-to-complex bridge
#print axioms Q1Paper.PaperI.map_submatrix_ofReal
#print axioms Q1Paper.PaperI.det_map_ofReal
#print axioms Q1Paper.PaperI.rank_map_ofReal_le
#print axioms Q1Paper.PaperI.rank_le_map_ofReal
#print axioms Q1Paper.PaperI.rank_map_ofReal
-- Claim 11, final assembly
#print axioms Q1Paper.PaperI.maximalMinor_map
#print axioms Q1Paper.PaperI.natDegree_det_le
#print axioms Q1Paper.PaperI.pencil_natDegree_le
#print axioms Q1Paper.PaperI.natDegree_maximalMinor_le
#print axioms Q1Paper.PaperI.spectral_real_iff_minors
#print axioms Q1Paper.PaperI.minorIndex
#print axioms Q1Paper.PaperI.minorFamily
#print axioms Q1Paper.PaperI.claim11_iff_gram

-- Claim 12
#print axioms Q1Paper.PaperI.exists_left_inverse_of_rank_eq
#print axioms Q1Paper.PaperI.claim12_iff_gram

-- Section III-D: square Cauchy-Binet (ported, Apache-2.0, Ralf Stephan)
#print axioms exteriorPower.plucker
#print axioms exteriorPower.plucker_apply
#print axioms Matrix.plucker_row_eq_det_submatrix
#print axioms exteriorPower.sum_plucker_mul_plucker
#print axioms Matrix.det_mul_eq_sum_plucker
#print axioms Matrix.det_mul_eq_sum_det_submatrix

-- Section III-D: Gram kernel
#print axioms Q1Paper.PaperI.selectedCols
#print axioms Q1Paper.PaperI.gramKernelEval
#print axioms Q1Paper.PaperI.gramKernelEval_eq_double_sum
#print axioms Q1Paper.PaperI.gramKernelEval_eq_zero_of_lt

-- Section III-D: coefficient identity
#print axioms Q1Paper.PaperI.eval_eq_sum_fin_coeff
#print axioms Q1Paper.PaperI.minorCoeff
#print axioms Q1Paper.PaperI.coeffGram
#print axioms Q1Paper.PaperI.gramKernelEval_eq_coeff_sum

-- Section III-D: window Gram entry identity
#print axioms Q1Paper.PaperI.windowMinorFamily
#print axioms Q1Paper.PaperI.windowGram_entry
#print axioms Q1Paper.PaperI.compressedGram
#print axioms Q1Paper.PaperI.windowGram_eq_compressed
#print axioms Q1Paper.PaperI.gramKernelEval_pencil_eq_coeff_sum
#print axioms Q1Paper.PaperI.det_submatrix_perm

-- Claim 13: bit-length base
#print axioms Q1Paper.PaperI.bitLenInt
#print axioms Q1Paper.PaperI.bitLenInt_abs_lt
#print axioms Q1Paper.PaperI.bitLenInt_mul
#print axioms Q1Paper.PaperI.bitLenInt_add
#print axioms Q1Paper.PaperI.bitLenRat
#print axioms Q1Paper.PaperI.bitLenRat_abs_lt
#print axioms Q1Paper.PaperI.bitLenRat_mul
#print axioms Q1Paper.PaperI.bitLenMat
#print axioms Q1Paper.PaperI.mat_abs_num_lt_two_pow_bitLenMat
#print axioms Q1Paper.PaperI.mat_num_entries_bounded
#print axioms Q1Paper.PaperI.imageFin
#print axioms Q1Paper.PaperI.imageEquiv
#print axioms Q1Paper.PaperI.permOfInjective
#print axioms Q1Paper.PaperI.rowEmb_permOfInjective
#print axioms Q1Paper.PaperI.bitLenInt_natCast
#print axioms Q1Paper.PaperI.rat_add_num_natAbs_le
#print axioms Q1Paper.PaperI.rat_add_den_le
#print axioms Q1Paper.PaperI.bitLenRat_add
#print axioms Q1Paper.PaperI.abs_det_le_factorial_mul_pow
#print axioms Q1Paper.PaperI.bitLenInt_det_le
#print axioms Q1Paper.PaperI.bitLenInt_det_num_le_bitLenMat
#print axioms Q1Paper.PaperI.embOfFinset
#print axioms Q1Paper.PaperI.imageFinset
#print axioms Q1Paper.PaperI.imageFinset_card
#print axioms Q1Paper.PaperI.imageEquivFinset
#print axioms Q1Paper.PaperI.permOfImage
#print axioms Q1Paper.PaperI.embOfFinset_permOfImage
#print axioms Q1Paper.PaperI.det_submatrix_comp
#print axioms Q1Paper.PaperI.maximalMinor_injective_eq_signed_image
#print axioms Q1Paper.PaperI.sum_comp_eq_card_smul_sum
#print axioms Q1Paper.PaperI.sum_sign_mul_sq_eq_card_smul_sum
#print axioms Q1Paper.PaperI.injective_of_imageFinset_eq
#print axioms Q1Paper.PaperI.fibreEquiv
#print axioms Q1Paper.PaperI.card_fibre_imageFinset
#print axioms Q1Paper.PaperI.card_fibre_imageFin
#print axioms Q1Paper.PaperI.card_fibre_pair
#print axioms Q1Paper.PaperI.rowEmb_imageFin
#print axioms Q1Paper.PaperI.colEmb_imageFin
#print axioms Q1Paper.PaperI.maximalMinor_injective_eq_signed_subset
#print axioms Q1Paper.PaperI.maximalMinor_injective_coeff_eq
#print axioms Q1Paper.PaperI.maximalMinor_injective_coeff_eq_subset
#print axioms Q1Paper.PaperI.pairSign
#print axioms Q1Paper.PaperI.pairSign_sq
#print axioms Q1Paper.PaperI.windowRow_inj_eq_sign_mul
#print axioms Q1Paper.PaperI.windowInj
#print axioms Q1Paper.PaperI.windowSub
#print axioms Q1Paper.PaperI.sum_prod_snd
#print axioms Q1Paper.PaperI.sum_snd_prod
#print axioms Q1Paper.PaperI.gram_entry_inj_eq
#print axioms Q1Paper.PaperI.gram_inj_eq_factorial_smul
#print axioms Q1Paper.PaperI.gram_solvable_iff_smul
#print axioms Q1Paper.PaperI.gram_certificate_iff_subset
#print axioms Q1Paper.PaperI.rowSpan
#print axioms Q1Paper.PaperI.preimagePair
#print axioms Q1Paper.PaperI.imagePair_preimagePair
#print axioms Q1Paper.PaperI.rowSpan_windowInj_eq
#print axioms Q1Paper.PaperI.nat_size_prod_le
#print axioms Q1Paper.PaperI.mat_den_size_le_sum
#print axioms Q1Paper.PaperI.inputLen
#print axioms Q1Paper.PaperI.bitLenMat_le_inputLen
#print axioms Q1Paper.PaperI.bStepNum_zero_eq_minor2
#print axioms Q1Paper.PaperI.sylvester_two
#print axioms Q1Paper.PaperI.bareiss_step_one_exact
#print axioms Q1Paper.PaperI.bitLenInt_bMinor_le
#print axioms Q1Paper.PaperI.bBorder
#print axioms Q1Paper.PaperI.dj_block
#print axioms Q1Paper.PaperI.desnanot_jacobi_minors
#print axioms Q1Paper.PaperI.desnanot_jacobi_prefix
#print axioms Q1Paper.PaperI.BareissTableau.bord_dj
#print axioms Q1Paper.PaperI.BareissTableau.bord_self
#print axioms Q1Paper.PaperI.BareissTableau.tableau_eq_bord
#print axioms Q1Paper.PaperI.BareissTableau.pivot_eq_delta
#print axioms Q1Paper.PaperI.BareissTableau.last_entry_eq_det
#print axioms Q1Paper.PaperI.BareissAssemble.tab
#print axioms Q1Paper.PaperI.BareissAssemble.tab_eq_bord
#print axioms Q1Paper.PaperI.BareissAssemble.tab_pivot
#print axioms Q1Paper.PaperI.BareissAssemble.tab_last
#print axioms Q1Paper.PaperI.BareissAssemble.tab_entry_eq_bMinor
#print axioms Q1Paper.PaperI.BareissAssemble.tab_entry_num_bitLen
#print axioms Q1Paper.PaperI.BareissAssemble.tab_entry_bitLen_inputLen
#print axioms Q1Paper.iv_implies_v
#print axioms Q1Paper.v_implies_iv
#print axioms Q1Paper.claim16_iv_iff_v
#print axioms Q1Paper.v_implies_i
#print axioms Q1Paper.claim16_iv_implies_i
#print axioms Q1Paper.claim16_ii_implies_iv
#print axioms Q1Paper.claim16_iii_implies_iv
#print axioms Q1Paper.claim16_iii_implies_i
#print axioms Q1Paper.Thm5.encodes
#print axioms Q1Paper.Thm5.DEC_of_encodes
#print axioms Q1Paper.Thm5.v_implies_i_self
#print axioms Q1Paper.Thm5.v_implies_i_real
#print axioms Q1Paper.Thm5.no_common_root_of_spectral
#print axioms Q1Paper.Thm5.exists_coeff_left_inverse_real
#print axioms Q1Paper.Thm5.coeff_iff_spectral
#print axioms Q1Paper.PaperI.RankFactorization.exists_factor_through_cols
#print axioms Q1Paper.PaperI.RankFactorization.exists_rank_factorization_of_rank
#print axioms Q1Paper.PaperI.RankFactorization.exists_rank_factorization
#print axioms Q1Paper.PaperI.RankFactorization.exists_rank_factorization_arb
#print axioms Q1Paper.PaperI.tauM
#print axioms Q1Paper.PaperI.exists_kernel_basis_bounded
#print axioms Q1Paper.PaperI.exists_row_basis_bounded
#print axioms Q1Paper.PaperI.exists_annihilator_bounded
#print axioms Q1Paper.PaperI.exists_rational_bases_bounded
#print axioms Q1Paper.Claim15iv.bitLenInt_mul_le
#print axioms Q1Paper.Claim15iv.minorBound_22
#print axioms Q1Paper.Claim15iv.minorBound_24_of_twenty
#print axioms Q1Paper.Claim15iv.gramBound_47
#print axioms Q1Paper.Claim15iv.coeffBound_240
#print axioms Q1Paper.Claim15iv.bMinor_bitLen_le_22
#print axioms Q1Paper.Claim15iv.gramEntry_bitLen_le_47
#print axioms Q1Paper.Claim15iv.coefficient_bitLen_le_240
#print axioms Q1Paper.Claim15iv.coefficient_of_minor_gram_le_240
#print axioms Q1Paper.PaperI.Claim14.map_comp_fst_K0_eq_inf
#print axioms Q1Paper.PaperI.Claim14.span_image_basis_eq_inf
#print axioms Q1Paper.PaperI.Claim14.linearIndependent_image_basis_iff
#print axioms Q1Paper.PaperI.Claim14.ker_restrictFst_eq_bot_iff
#print axioms Q1Paper.PaperI.Claim14.matrix_map_comp_fst_K0_eq_inf
#print axioms Q1Paper.Thm5.exists_encodes_of_blocks
#print axioms Q1Paper.Thm5.exists_encodes_of_compressed
#print axioms Q1Paper.Thm5.exists_encodes_of_exists_compressed
#print axioms Q1Paper.Thm5.exists_compressed_complex_of_encodes
#print axioms Q1Paper.Thm5.exists_encodes_iff
#print axioms Q1Paper.Thm5.exists_coeff_left_inverse_arb
#print axioms Q1Paper.pencilMinors
#print axioms Q1Paper.FamilyGcdIsConst
#print axioms Q1Paper.NoCommonComplexRoot
#print axioms Q1Paper.gcd_isConst_iff_no_common_complex_root
#print axioms Q1Paper.pencilMinors_gcd_isConst_iff_no_common_complex_root
#print axioms Q1Paper.rank_eq_iff_no_common_complex_root
#print axioms Q1Paper.claim16_i_iff_iii
#print axioms Q1Paper.exists_sum_mul_eq_one_of_gcd_isConst
#print axioms Q1Paper.exists_leftInverse_pencil_of_gcd_isConst
#print axioms Q1Paper.claim16_iii_implies_i_of_gcd_isConst
#print axioms Q1Paper.claim3_attainable
#print axioms Q1Paper.claim4_sandwich
#print axioms Q1Paper.claim5_conditions_depend_on_W
#print axioms Q1Paper.claim6_struct
#print axioms Q1Paper.claim7_DEC_succ
#print axioms Q1Paper.claim8_rank_consistency
#print axioms Q1Paper.Thm5.rank_map_ofReal_arb
#print axioms Q1Paper.Thm5.range_map_ofReal_of_ker
#print axioms Q1Paper.Thm5.DECℂ_iff_exists_compressed
#print axioms Q1Paper.Thm5.DECℂ_iff_exists_encodes
#print axioms Q1Paper.Thm5.encodesD_iff_encodes
#print axioms Q1Paper.Thm5.encodes_of_rank_zero
#print axioms Q1Paper.Thm5.encodes_of_rank_zero_compressed
#print axioms Q1Paper.Thm5.exists_compressed_zero_of_encodes_zero
#print axioms Q1Complexity.ratBitCost_le_fieldOpBitCost
#print axioms Q1Complexity.fieldOpBitCost_not_lower_bound
#print axioms Q1Complexity.run_bind
#print axioms Q1Complexity.run_forFin_bit_eq_sum
#print axioms Q1Complexity.run_alg_eq_primitiveCount
#print axioms Q1Complexity.run_bit_le_sum
#print axioms Q1Complexity.evalPrimitive_cost
#print axioms Q1Complexity.sumProg_cost_two
#print axioms Q1Subspace.exists_mulVec_eq_iff_mem_rowSpace
#print axioms Q1Subspace.exists_mulVec_eq_iff_rank_fromRows
#print axioms Q1Subspace.rank_fromRows_eq_rank_iff_mem
#print axioms Q1Subspace.not_exists_mulVec_iff_rank_lt
#print axioms Q1Subspace.rank_le_rank_fromRows_right
#print axioms Matrix.norm_det_le_prod_norm_column
#print axioms Matrix.det_natAbs_le_of_entry_bound
#print axioms Matrix.bitLenInt_det_le_hadamard
#print axioms Matrix.bitLenInt_det_le_n_mul
#print axioms Matrix.bitLenInt_det_le_n_mul_size_succ
#print axioms Q1Complexity.BareissCost.bstep2Prog_value_eq_det
#print axioms Q1Complexity.BareissCost.bstep2Prog_alg
#print axioms Q1Complexity.BareissCost.bstep2Prog_bit
#print axioms Q1Complexity.BareissCost.bstep2Prog_bit_le
#print axioms Q1Complexity.BareissCost.batchProg_bit_eq_sum
#print axioms Q1Complexity.BareissCost.batchProg_alg
#print axioms Q1Complexity.BareissCost.batchProg_bit_le_uniform
#print axioms exists_rat_solution_of_exists_real_solution
#print axioms exists_rat_solution_of_exists_real_solution_arb
#print axioms exists_mulVec_rat_solution_of_exists_mulVec_real_solution
#print axioms rank_map_ratReal_arb
#print axioms Q1Paper.exists_basis_matrix_of_submodule
#print axioms Q1Paper.exists_kernel_basis_matrix
#print axioms Q1Paper.exists_kernel_basis_matrix_of_finrank
#print axioms Q1Paper.exists_rat_bounded_bezout_of_real_bounded_bezout
#print axioms Q1Paper.exists_rat_bounded_bezout_of_no_common_root
#print axioms Q1Paper.claim16_iii_implies_iv_of_gcd_isConst
#print axioms Q1Paper.claim16_ii_implies_iv_rat
#print axioms Q1Paper.Thm5.DECℂ_iff_exists_compressed_auto
#print axioms Q1Paper.Thm5.DECℂ_iff_exists_encodes_auto
#print axioms Q1Paper.PaperI.Chart14.exists_chart_bases
#print axioms Q1Paper.PaperI.Chart14.inf_eq_map_K0
#print axioms Q1Paper.PaperI.Chart14.exists_inf_basis_matrix
#print axioms Q1Paper.PaperI.Chart14.exists_chart_completion
#print axioms Q1Paper.PaperI.Chart14.image_basis_not_basis
#print axioms Q1Paper.PaperI.ComplexityCounts.bareiss_update_count_le_cube
#print axioms Q1Paper.PaperI.ComplexityCounts.bareiss_field_op_count_le
#print axioms Q1Paper.PaperI.ComplexityCounts.bareissUpdateCount_eq_div
#print axioms Q1Paper.PaperI.ComplexityCounts.factorial_bitlen_le
#print axioms Q1Paper.PaperI.ComplexityCounts.bareiss_entry_den_eq_one
#print axioms Q1Paper.PaperI.ComplexityCounts.bareiss_entry_bitLenRat_le_tauM
#print axioms Q1Paper.PaperI.ComplexityCounts.bareiss_steps_cost_le
#print axioms Q1Paper.PaperI.bitLenMat_mul_le
#print axioms Q1Paper.PaperI.bitLenMatAny_fromRows_le
#print axioms Q1Paper.PaperI.bitLenMat_submatrix_le
#print axioms Q1Paper.PaperI.bitLenMat_transpose_le
#print axioms Q1Paper.PaperI.bitLenMat_map_intCast
#print axioms Q1Paper.PaperI.bitLenMat_chain_le
#print axioms Q1Paper.PaperI.bitLenMat_chain_inputLen_le
#print axioms Q1Paper.Claim15.bitLenMat_L0_mul_N
#print axioms Q1Paper.Claim15.bitLenMat_L0_mul_N_of_entries
#print axioms Q1Paper.Claim15.bitLenMat_L0_mul_A_mul_N
#print axioms Q1Paper.Claim15.bitLenMat_L0_mul_A_mul_N_of_entries
#print axioms Q1Paper.Claim15.bitLenMat_mul_of_entries
#print axioms Q1Paper.Claim15.inputLen_le_of_entry_bound
#print axioms Q1Paper.chart_count_le
#print axioms Q1Paper.chart_count_le_pow
#print axioms Q1Paper.exp_compose
#print axioms Q1Paper.beta_le_L_pow
#print axioms Q1Paper.PaperI.tauM_le_of_bounds
#print axioms Q1Paper.PaperI.tauM_le_paper_constant
#print axioms Q1Paper.PaperI.bitLenMatAny_fromCols_le
#print axioms Q1Paper.PaperI.bitLenMat_fromCols_le
#print axioms Q1Paper.PaperI.bitLenMatAny_matrixFromCols_le
#print axioms Q1Paper.PaperI.bitLenMatAny_fromCols_mul_le
#print axioms Q1Paper.PaperI.bitLenMatAny_pairMatrix_le
#print axioms Q1Paper.PaperI.bitLenMatAny_pairMatrix_le'
#print axioms Q1Paper.PaperI.ComplexityCounts.fieldOpBitCost_div_eq
#print axioms Q1Paper.PaperI.ComplexityCounts.fieldOpBitCost_div_le_quartic
#print axioms Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le
#print axioms Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_tauM
#print axioms Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_n21_L2_false
#print axioms Q1Paper.PaperI.ComplexityCounts.exactDivCost_le_add_envelope
#print axioms Q1Paper.PaperI.ComplexityCounts.exactDivCost_le_quadratic
#print axioms Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_quadratic
#print axioms Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_n21_L2
#print axioms Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_quadratic_one_million_false
#print axioms Q1Paper.theorem1_conditional
#print axioms Q1Paper.theorem1_conditional_beta_zero
