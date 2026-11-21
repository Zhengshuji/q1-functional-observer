import Q1Paper.Basic
import Q1Paper.RankIdentity
import Q1Paper.HyperplaneAvoid
import Q1Paper.BezoutDeg
import Q1Paper.G2Assembly
import Q1Paper.G3Adjugate
import Q1Paper.G3LeftInverse
import Q1Paper.DegreeBounds
import Q1Paper.G3Coeff
import Q1Paper.G5GramRank
import Q1Paper.Q1Compression
import Q1Paper.Q1Subspace
import Q1Paper.Monotone
import Q1Paper.Q1RowSpace
import Q1Paper.Q1Projection
import Q1Paper.Q1Pencil
import Q1Paper.Q1Step3
import Q1Paper.G4RankIdentity
import Q1Paper.KappaObs
import Q1Paper.Compression
import Q1Paper.FreeRows
import Q1Paper.RankConsistency
import Q1Paper.SpectralCertificate
import Q1Paper.FixedOrder
import Q1Paper.FPT
import Q1Paper.HyperplaneDirection
import Q1Paper.HyperplanePrescribed
import Q1Paper.HyperplaneFibre
import Q1Paper.TightDim
import Q1Paper.BoundLower

#print axioms Q1Paper.pairMap_apply
#print axioms Q1Paper.ker_pairMap
#print axioms Q1Paper.finrank_range_pairMap
#print axioms Q1Paper.finrank_range_pairMap_common
#print axioms Q1Paper.G_form_iff
#print axioms Q1Paper.injective_of_leftInverse
#print axioms Q1Paper.finrank_le_of_leftInverse
#print axioms Q1Paper.kappaObs_zero
#print axioms Q1Paper.freePairDim_le_kappaObs
#print axioms Q1Paper.finrank_range_prod
#print axioms Q1Paper.exists_forall_apply_ne_zero
#print axioms Q1Paper.exists_ne_zero_with_finite_roots
#print axioms Q1Paper.isCoprime_of_no_common_root
#print axioms Q1Paper.exists_bezout_deg_lt
#print axioms Q1Paper.exists_bezout_family
#print axioms Q1Paper.adjRowInverse_mul
#print axioms Q1Paper.exists_leftInverse
#print axioms Q1Paper.natDegree_intCast_le
#print axioms Q1Paper.natDegree_det_le
#print axioms Q1Paper.natDegree_det_le_sum
#print axioms Q1Paper.sum_ite_eq_zero_one
#print axioms Q1Paper.natDegree_adjugate_le
#print axioms Q1Paper.natDegree_adjRowInverse_le
#print axioms Q1Paper.exists_leftInverse_linear
#print axioms Q1Paper.spoly_mul_pencil
#print axioms Q1Paper.spoly_mul_pencil_zero
#print axioms Q1Paper.spoly_mul_pencil_eq_one
#print axioms Q1Paper.coeff_mul_apply
#print axioms Q1Paper.augment_mul_transpose
#print axioms Q1Paper.exists_mulVec_eq_iff_rank_gram
#print axioms Q1Paper.rank_vstack_add_rank_mul
#print axioms Q1Paper.ker_compressed_iff
#print axioms Q1Paper.mem_freePairSpace_iff
#print axioms Q1Paper.finrank_domain_le_freePairSpace
#print axioms Q1Paper.finrank_freePairSpace_add_ker
#print axioms Q1Paper.kappaObs_eq_mul_freePairSpace
#print axioms Q1Paper.exists_solution_iff_mem_range
#print axioms Q1Paper.exists_solution_iff_span_le_range
#print axioms Q1Paper.exists_solution_iff_range_eq_sup_span
#print axioms Q1Paper.bezout_of_gcd_eq_one
#print axioms Q1Paper.sum_sq_eq_zero_iff
#print axioms Q1Subspace.range_eq_rowSpan
#print axioms Q1Subspace.mem_rowSpan_iff_exists_vecMul
#print axioms Q1Subspace.rowSpan_fromRows_left
#print axioms Q1Subspace.rank_fromRows_eq_rank_iff
#print axioms Q1Subspace.pi1_eq_pi2_of_le_of_finrank_eq
#print axioms Q1Subspace.hasConstantRank_iff_rankIndependent
#print axioms Q1Subspace.rowSpace_eq
#print axioms KappaObs.kappaObs_eq_row_count
#print axioms Q1Subspace.finrank_le_pi1_add_pi2
#print axioms Q1Subspace.finrank_le_two_mul_of_pi1_eq_pi2
#print axioms Q1Paper.rank_fromRows_zero
#print axioms Q1Paper.rowSpan_fromRows_zero

#print axioms Q1Paper.compression_eq_of_proportional
#print axioms Q1Paper.proportional_of_compression
#print axioms Q1Paper.direction_iff
#print axioms Q1Paper.le_orthogonal_span_pair
#print axioms Q1Paper.inf_inf_orthogonal_eq

#print axioms Q1Paper.mem_orthogonal_span_pair_iff
#print axioms Q1Paper.Dv_eq_ker
#print axioms Q1Paper.finrank_Dv

#print axioms Q1Subspace.finrank_sup_pi_le
#print axioms Q1Subspace.finrank_pi1_mono
#print axioms Q1Subspace.finrank_add_one_le_of_spectral
