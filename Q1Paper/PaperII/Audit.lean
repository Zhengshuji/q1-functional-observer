/-
Q1Paper/PaperII/Audit.lean

The axiom footprint of every declaration of Paper II's Lean development.

Generated from the `PaperII/` sources (declaration names only) by
`scripts/generate_audit.py`; do not edit by hand.  Every audited declaration must
depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

import Q1Paper.PaperII.Interface
import Q1Paper.PaperII.Sandwich
import Q1Paper.PaperII.Monotone
import Q1Paper.PaperII.LowerBound
import Q1Paper.PaperII.Converse
import Q1Paper.PaperII.Saturate
import Q1Paper.PaperII.MinOrder
import Q1Paper.PaperII.GraphExtension
import Q1Paper.PaperII.GraphExtract
import Q1Paper.PaperII.Realification
import Q1Paper.PaperII.Tightness
import Q1Paper.PaperII.RealGraph
import Q1Paper.PaperII.Complexity

-- Complexity.lean
#print axioms Q1Paper.PaperII.lt_two_pow_log2_succ
#print axioms Q1Paper.PaperII.div_two_pow_log2_succ_eq_zero
#print axioms Q1Paper.PaperII.bisect_steps_le
#print axioms Q1Paper.PaperII.log2_mono_le
#print axioms Q1Paper.PaperII.half_width
#print axioms Q1Paper.PaperII.bisectGo
#print axioms Q1Paper.PaperII.bisectGo_spec
#print axioms Q1Paper.PaperII.bisectGo_collapses

-- Converse.lean
#print axioms Q1Paper.PaperII.WRc
#print axioms Q1Paper.PaperII.WRc_eq_map
#print axioms Q1Paper.PaperII.map_symm_map
#print axioms Q1Paper.PaperII.feasible_to_DEC

-- GraphExtension.lean
#print axioms Q1Paper.PaperII.graphMap
#print axioms Q1Paper.PaperII.graphExt
#print axioms Q1Paper.PaperII.mem_graphExt
#print axioms Q1Paper.PaperII.graphExt_pi1
#print axioms Q1Paper.PaperII.graphExt_pi2_le
#print axioms Q1Paper.PaperII.graphExt_finrank
#print axioms Q1Paper.PaperII.graphPencil
#print axioms Q1Paper.PaperII.graphPencil_apply
#print axioms Q1Paper.PaperII.graphExt_piLam
#print axioms Q1Paper.PaperII.graphExt_feasible
#print axioms Q1Paper.PaperII.t_eq_of_graph

-- GraphExtract.lean
#print axioms Q1Paper.PaperII.projW
#print axioms Q1Paper.PaperII.projW_range
#print axioms Q1Paper.PaperII.projU
#print axioms Q1Paper.PaperII.projU_surjective
#print axioms Q1Paper.PaperII.ker_finrank_eq_one
#print axioms Q1Paper.PaperII.exists_kernel_direction
#print axioms Q1Paper.PaperII.exists_kernel_b
#print axioms Q1Paper.PaperII.exists_graph_representation

-- Interface.lean
#print axioms Q1Paper.PaperII.Mcol
#print axioms Q1Paper.PaperII.Φ
#print axioms Q1Paper.PaperII.Mcol_left
#print axioms Q1Paper.PaperII.Mcol_right
#print axioms Q1Paper.PaperII.Φ_apply
#print axioms Q1Paper.PaperII.Φ_vecMul
#print axioms Q1Paper.PaperII.map_rowSpace_Mcol
#print axioms Q1Paper.PaperII.t
#print axioms Q1Paper.PaperII.t_eq_finrank_sub
#print axioms Q1Paper.PaperII.t_le_iff
#print axioms Q1Paper.PaperII.DecOrder
#print axioms Q1Paper.PaperII.IsFeasible
#print axioms Q1Paper.PaperII.isFeasible_pairRowSpace_iff

-- LowerBound.lean
#print axioms Q1Paper.PaperII.finrank_sup_pi_le
#print axioms Q1Paper.PaperII.finrank_pi1_mono
#print axioms Q1Paper.PaperII.lowerBound_core
#print axioms Q1Paper.PaperII.lowerBound_sub
#print axioms Q1Paper.PaperII.t_eq_of_finrank

-- MinOrder.lean
#print axioms Q1Paper.PaperII.tMinSet
#print axioms Q1Paper.PaperII.tMin
#print axioms Q1Paper.PaperII.tMin_le_iff_dec
#print axioms Q1Paper.PaperII.ell
#print axioms Q1Paper.PaperII.omega_le_ell
#print axioms Q1Paper.PaperII.t_le_two_ell
#print axioms Q1Paper.PaperII.tMin_le_two_ell
#print axioms Q1Paper.PaperII.dec_sInf_tMinSet
#print axioms Q1Paper.PaperII.exists_least_of_monotone
#print axioms Q1Paper.PaperII.le_tMin_of_lowerBound
#print axioms Q1Paper.PaperII.le_tMin_of_lowerBound_max

-- Monotone.lean
#print axioms Q1Paper.PaperII.pairRowSpace_fromRows
#print axioms Q1Paper.PaperII.pairRowSpace_pad
#print axioms Q1Paper.PaperII.decC_mono_add
#print axioms Q1Paper.PaperII.decC_mono

-- RealGraph.lean
#print axioms Q1Paper.PaperII.phi_apply
#print axioms Q1Paper.PaperII.phi_eq_zero
#print axioms Q1Paper.PaperII.map_mulVec_phi
#print axioms Q1Paper.PaperII.Gfun
#print axioms Q1Paper.PaperII.Gfun_mem_UC
#print axioms Q1Paper.PaperII.GcU
#print axioms Q1Paper.PaperII.GcU_phi
#print axioms Q1Paper.PaperII.GR
#print axioms Q1Paper.PaperII.GR_apply
#print axioms Q1Paper.PaperII.phiPair
#print axioms Q1Paper.PaperII.phiPair_apply
#print axioms Q1Paper.PaperII.phiPair_mem_graphExt
#print axioms Q1Paper.PaperII.phiU
#print axioms Q1Paper.PaperII.phiU_apply
#print axioms Q1Paper.PaperII.phiU_eq
#print axioms Q1Paper.PaperII.phiDom
#print axioms Q1Paper.PaperII.phiDom_apply
#print axioms Q1Paper.PaperII.graphMap_phiDom
#print axioms Q1Paper.PaperII.range_phiU_val
#print axioms Q1Paper.PaperII.span_phiU
#print axioms Q1Paper.PaperII.span_phiDom
#print axioms Q1Paper.PaperII.graphExt_span_phiPair
#print axioms Q1Paper.PaperII.WRreal
#print axioms Q1Paper.PaperII.Lc_mul
#print axioms Q1Paper.PaperII.Lc_mul_A
#print axioms Q1Paper.PaperII.WR_eq_span_phiPair_WRreal
#print axioms Q1Paper.PaperII.W0real
#print axioms Q1Paper.PaperII.TRreal
#print axioms Q1Paper.PaperII.W0real_eq
#print axioms Q1Paper.PaperII.TRreal_eq
#print axioms Q1Paper.PaperII.exists_design_of_encoded
#print axioms Q1Paper.PaperII.exists_design_of_pairRowSpace
#print axioms Q1Paper.PaperII.tMinC_le_of_graph_real
#print axioms Q1Paper.PaperII.tMinC_le_of_mem
#print axioms Q1Paper.PaperII.exists_graph_of_tMinC_eq
#print axioms Q1Paper.PaperII.phiPair_eq
#print axioms Q1Paper.PaperII.finrank_span_phiPair
#print axioms Q1Paper.PaperII.pi1_span_phiPair
#print axioms Q1Paper.PaperII.pi2_span_phiPair
#print axioms Q1Paper.PaperII.piLam_span_phiPair
#print axioms Q1Paper.PaperII.reFun
#print axioms Q1Paper.PaperII.imFun
#print axioms Q1Paper.PaperII.reFun_phi
#print axioms Q1Paper.PaperII.imFun_phi
#print axioms Q1Paper.PaperII.re_im_mem_of_mem_span
#print axioms Q1Paper.PaperII.mem_of_phi_mem_span
#print axioms Q1Paper.PaperII.isFeasible_real_of_span_phiPair
#print axioms Q1Paper.PaperII.exists_real_graph_of_tMinC_eq
#print axioms Q1Paper.PaperII.tMinC_eq_of_real_graph
#print axioms Q1Paper.PaperII.L0c_mul
#print axioms Q1Paper.PaperII.L0c_mul_A
#print axioms Q1Paper.PaperII.W0_eq_span_phiPair_W0real
#print axioms Q1Paper.PaperII.W0_le_span_phiPair
#print axioms Q1Paper.PaperII.W0_le_of_WRreal_le
#print axioms Q1Paper.PaperII.span_phiPair_eq_map
#print axioms Q1Paper.PaperII.mem_of_phiPair_mem_span
#print axioms Q1Paper.PaperII.TR_eq_span_phiPair_TRreal
#print axioms Q1Paper.PaperII.W0real_le_of_W0_le
#print axioms Q1Paper.PaperII.WRreal_le_of_WR_le
#print axioms Q1Paper.PaperII.tMinC_le_of_graph_real_pure
#print axioms Q1Paper.PaperII.tMinC_eq_iff_real_graph

-- Realification.lean
#print axioms Q1Paper.PaperII.pairRows
#print axioms Q1Paper.PaperII.Φ_pairRows
#print axioms Q1Paper.PaperII.pairRowSpace_eq_map_pairRows
#print axioms Q1Paper.PaperII.finrank_pairRowSpace_eq_rank
#print axioms Q1Paper.PaperII.pairRows_map
#print axioms Q1Paper.PaperII.mul_pairRows
#print axioms Q1Paper.PaperII.WR_eq_map_complex
#print axioms Q1Paper.PaperII.finrank_WR_eq
#print axioms Q1Paper.PaperII.finrank_W0_eq
#print axioms Q1Paper.PaperII.phi
#print axioms Q1Paper.PaperII.rowSpace_map_complex
#print axioms Q1Paper.PaperII.real_compress
#print axioms Q1Paper.PaperII.feasible_to_decC
#print axioms Q1Paper.PaperII.decC_to_feasible_design
#print axioms Q1Paper.PaperII.decC_saturates
#print axioms Q1Paper.PaperII.tMinCSet
#print axioms Q1Paper.PaperII.tMinC
#print axioms Q1Paper.PaperII.tMinC_le_iff_decC
#print axioms Q1Paper.PaperII.decC_sInf_tMinCSet
#print axioms Q1Paper.PaperII.tMinC_le_two_ell
#print axioms Q1Paper.PaperII.UC
#print axioms Q1Paper.PaperII.finrank_UC
#print axioms Q1Paper.PaperII.WR_le_TR
#print axioms Q1Paper.PaperII.tMin_le_tMinC
#print axioms Q1Paper.PaperII.le_tMinC_of_lowerBound

-- Sandwich.lean
#print axioms Q1Paper.PaperII.Ac
#print axioms Q1Paper.PaperII.L0c
#print axioms Q1Paper.PaperII.Rc
#print axioms Q1Paper.PaperII.Lc
#print axioms Q1Paper.PaperII.fromRows_Lc
#print axioms Q1Paper.PaperII.TR
#print axioms Q1Paper.PaperII.W0
#print axioms Q1Paper.PaperII.WR
#print axioms Q1Paper.PaperII.W0_eq_map
#print axioms Q1Paper.PaperII.TR_eq_map
#print axioms Q1Paper.PaperII.WR_eq_map
#print axioms Q1Paper.PaperII.decC_to_feasible

-- Saturate.lean
#print axioms Q1Paper.PaperII.DEC_to_feasible_c
#print axioms Q1Paper.PaperII.t_le_t_of_le
#print axioms Q1Paper.PaperII.dec_saturates
#print axioms Q1Paper.PaperII.dec_mono_complex

-- Tightness.lean
#print axioms Q1Paper.PaperII.omega_pos_of_nonzero
#print axioms Q1Paper.PaperII.W0_ne_bot_of_pos
#print axioms Q1Paper.PaperII.pi1_eq_sup_of_finrank
#print axioms Q1Paper.PaperII.tMin_eq_of_graph
#print axioms Q1Paper.PaperII.exists_graph_of_tMin_eq
#print axioms Q1Paper.PaperII.UV
#print axioms Q1Paper.PaperII.UV_eq
#print axioms Q1Paper.PaperII.mem_tMinSet
#print axioms Q1Paper.PaperII.tMin_le_of_feasible
#print axioms Q1Paper.PaperII.tMin_eq_iff_graph

