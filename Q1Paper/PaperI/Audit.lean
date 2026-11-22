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
