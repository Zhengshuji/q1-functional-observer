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
