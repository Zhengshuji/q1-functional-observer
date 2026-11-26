import Q1Paper.PaperII.MainTheorems

/-!
Q1Paper/PaperII/Read/S06_RealDesigns.lean

§III  The paper's real-design specification `DECℂ`.

This file contains **no proofs**: a reading entry in proof order, one `#check` per step.

## What it consumes

The complex-design development (`S02`–`S05`).

## What it proves

1. **The pair encoding of a real design.**  `row[H  H_A]` is encoded by `pairRows`; the
   encoding commutes with complexification (`pairRows_map`, `mul_pairRows`) and
   `dim_ℂ W = dim_ℝ V` (`finrank_pairRowSpace_eq_rank`, `finrank_WR_eq`, `WR_eq_map_complex`).
2. **The real-compression lemma** — `real_compress`: a real design of `r` rows is compressed to
   `t = dim(W/W₀)` rows keeping the same `W`.
3. **The converse sandwich for real designs** — `feasible_to_decC`: a feasible real `W`
   produces `DECℂ` at the order `t`.
4. **Saturation for real designs** — `decC_saturates`.
5. **The real-design minimum order** — `tMinC`, `tMinC_le_iff_decC` (`t_min^ℝ ≤ r ↔ DECℂ r`),
   the least real order is feasible (`decC_sInf_tMinCSet`), the a priori bound
   `t_min^ℝ ≤ 2ℓ` (`tMinC_le_two_ell`), the spectral lower bound `a + 1 − s₀ ≤ t_min^ℝ`
   (`le_tMinC_of_lowerBound`), and `t_min ≤ t_min^ℝ` (`tMin_le_tMinC`).
6. **The complexification bridge** — `UC` and `finrank_UC` (`dim_ℂ = dim_ℝ` for a real
   subspace).
7. **The complexification bridges for pair spaces** — `graphExt_span_phiPair` (the complex
   graph of a real graph `W(G,b)` is the `ℂ`-span of its `phiPair`-image),
   `finrank_span_phiPair` (`dim_ℂ` of that span equals `dim_ℝ` of the real subspace), and the
   commutation of the projections and the pencil with complexification
   (`pi1_span_phiPair`, `pi2_span_phiPair`, `piLam_span_phiPair`).
8. **The real points of a complex span** — `re_im_mem_of_mem_span`, `mem_of_phi_mem_span`;
   consequently complex feasibility descends to the real pair space
   (`isFeasible_real_of_span_phiPair`).
9. **The real sandwich converse** — `exists_design_of_pairRowSpace`: a real subspace between
   `W₀` and `T` of quotient dimension at most `r` is realised by a real design of `r` rows.
10. **Proposition 3 for the paper's real designs** — `tMinC_le_of_graph_real` (real data give
    `t_min^ℝ ≤ dim_ℝ U + 1 − s₀`), `tMinC_eq_of_real_graph`, the extraction of the tightness
    data `exists_real_graph_of_tMinC_eq`, and the packaged criterion `tMinC_eq_iff_real_graph`.

## The result

- `Q1Paper.PaperII.pairRows`, `pairRowSpace_eq_map_pairRows`, `finrank_pairRowSpace_eq_rank`,
  `pairRows_map`, `mul_pairRows`, `WR_eq_map_complex`, `finrank_WR_eq`
- `Q1Paper.PaperII.real_compress`, `feasible_to_decC`, `decC_saturates`
- `Q1Paper.PaperII.tMinC`, `tMinC_le_iff_decC`, `decC_sInf_tMinCSet`
- `Q1Paper.PaperII.tMinC_le_two_ell`, `WR_le_TR`, `tMin_le_tMinC`, `le_tMinC_of_lowerBound`
- `Q1Paper.PaperII.UC`, `finrank_UC`
- `Q1Paper.PaperII.graphExt_span_phiPair`, `finrank_span_phiPair`, `pi1_span_phiPair`,
  `pi2_span_phiPair`, `piLam_span_phiPair`
- `Q1Paper.PaperII.re_im_mem_of_mem_span`, `mem_of_phi_mem_span`,
  `isFeasible_real_of_span_phiPair`
- `Q1Paper.PaperII.exists_design_of_pairRowSpace`
- `Q1Paper.PaperII.tMinC_le_of_graph_real`, `tMinC_eq_of_real_graph`,
  `exists_real_graph_of_tMinC_eq`, `tMinC_eq_iff_real_graph`
-/

#check @Q1Paper.PaperII.pairRows
#check @Q1Paper.PaperII.pairRowSpace_eq_map_pairRows
#check @Q1Paper.PaperII.finrank_pairRowSpace_eq_rank
#check @Q1Paper.PaperII.pairRows_map
#check @Q1Paper.PaperII.mul_pairRows
#check @Q1Paper.PaperII.WR_eq_map_complex
#check @Q1Paper.PaperII.finrank_WR_eq
#check @Q1Paper.PaperII.real_compress
#check @Q1Paper.PaperII.feasible_to_decC
#check @Q1Paper.PaperII.decC_saturates
#check @Q1Paper.PaperII.tMinC
#check @Q1Paper.PaperII.tMinC_le_iff_decC
#check @Q1Paper.PaperII.decC_sInf_tMinCSet
#check @Q1Paper.PaperII.tMinC_le_two_ell
#check @Q1Paper.PaperII.WR_le_TR
#check @Q1Paper.PaperII.tMin_le_tMinC
#check @Q1Paper.PaperII.le_tMinC_of_lowerBound
#check @Q1Paper.PaperII.UC
#check @Q1Paper.PaperII.finrank_UC
#check @Q1Paper.PaperII.graphExt_span_phiPair
#check @Q1Paper.PaperII.finrank_span_phiPair
#check @Q1Paper.PaperII.pi1_span_phiPair
#check @Q1Paper.PaperII.pi2_span_phiPair
#check @Q1Paper.PaperII.piLam_span_phiPair
#check @Q1Paper.PaperII.re_im_mem_of_mem_span
#check @Q1Paper.PaperII.mem_of_phi_mem_span
#check @Q1Paper.PaperII.isFeasible_real_of_span_phiPair
#check @Q1Paper.PaperII.exists_design_of_pairRowSpace
#check @Q1Paper.PaperII.tMinC_le_of_graph_real
#check @Q1Paper.PaperII.tMinC_eq_of_real_graph
#check @Q1Paper.PaperII.exists_real_graph_of_tMinC_eq
#check @Q1Paper.PaperII.tMinC_eq_iff_real_graph
