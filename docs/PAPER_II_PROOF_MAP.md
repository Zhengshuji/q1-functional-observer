# Paper II: paper item → Lean declaration

One row per item of `paper/paper_II_minorder.tex`, with the declaration that proves
it and where it lives.  Line numbers refer to the files at commit `feb5b06` (they
move when a file is edited above them; the declaration names and their
`#check`s in `Q1Paper/PaperII/ClaimsCheck.lean` are stable).

**Scope.**  Items marked *reused* are proved in the Paper I tree and enter Paper II
through the column split `Φ`.  Most items are stated twice: for the field-generic
predicate over `ℂ` (complex free blocks) and for the paper's real-design
specification `DECℂ`.  The bridge between them is the real-compression lemma
`real_compress` (`PaperII/Realification.lean`); for `DECℂ` the minimum order is
`tMinC ≤ r ↔ DECℂ r`, the least quotient dimension over feasible *real* designs.

## §II Standing results (from Paper I)

| paper item | declaration | file | status |
|---|---|---|---|
| Claim 4, forward (`lem:sandwich`) | `Q1Paper.claim4_sandwich` | `Q1Paper/PaperI/S02_Subspace/Claims38.lean` | reused |
| Claim 4, converse (`lem:sandwich`) | `Q1Paper.claim4_converse` | `Q1Paper/PaperI/S02_Subspace/Claim4Converse.lean:52` | reused |
| Claim 5 (`lem:W-conditions`) | `Q1Paper.claim5_conditions_depend_on_W` | `Q1Paper/PaperI/S02_Subspace/Claims38.lean:280` | reused |
| Claim 6 (`lem:struct`) | `Q1Paper.claim6_struct` | `Q1Paper/PaperI/S02_Subspace/Claims38.lean:325` | reused |

## §II Paper II's interface

| paper item | declaration | file:line | status |
|---|---|---|---|
| `W = row[L N  L A N]`, `W₀`, `T` | `W0`, `TR`, `WR` | `PaperII/Sandwich.lean:64,69,74` | literal |
| the two encodings agree (row(`[N AN]`) ↔ pairs) | `map_rowSpace_Mcol` | `PaperII/Interface.lean:91` | literal |
| `t = dim (W/W₀)` | `t`, `t_eq_finrank_sub`, `t_le_iff` | `PaperII/Interface.lean:121,125,136` | literal |
| feasibility = the two compressed conditions | `IsFeasible`, `isFeasible_pairRowSpace_iff` | `PaperII/Interface.lean:163,168` | literal |

## §III The sandwich in Paper II's form

| paper item | declaration | file:line | status |
|---|---|---|---|
| forward, `DECℂ` (real design) | `decC_to_feasible` | `PaperII/Sandwich.lean:112` | literal |
| forward, `DEC` (complex designs) | `DEC_to_feasible_c` | `PaperII/Saturate.lean:37` | literal |
| converse, `DEC` | `feasible_to_DEC` | `PaperII/Converse.lean:71` | literal |
| converse, `DECℂ` | `feasible_to_decC` (via `real_compress`) | `PaperII/Realification.lean` | literal |

## §III Monotonicity and saturation

| paper item | declaration | file:line | status |
|---|---|---|---|
| Claim 5, monotone, `DECℂ` | `decC_mono` | `PaperII/Monotone.lean:154` | literal |
| Claim 5, monotone, `DEC` | `dec_mono_complex` | `PaperII/Saturate.lean:107` | literal |
| Claim 5, saturation, `DEC` | `dec_saturates` | `PaperII/Saturate.lean:87` | literal |
| Claim 5, saturation, `DECℂ` | `decC_saturates` (via `real_compress`, `feasible_to_decC`) | `PaperII/Realification.lean` | literal |

## §III Minimum order

| paper item | declaration | file:line | status |
|---|---|---|---|
| Prop 1: `q_min = r₀ + t_min` (`t_min ≤ r ↔ DEC (r₀+r)`) | `tMin_le_iff_dec` | `PaperII/MinOrder.lean:59` | literal (`DEC`) |
| Prop 1: `t_min ≤ 2ℓ` | `tMin_le_two_ell` (via `omega_le_ell`, `t_le_two_ell`) | `PaperII/MinOrder.lean:126,90,109` | literal (`DEC`) |
| Prop 1 with `t_min = ⊤` when infeasible | `tMin`, `tMinSet` | `PaperII/MinOrder.lean:50,43` | literal |
| Theorem 4, correctness half: the least feasible order is feasible | `dec_sInf_tMinSet` | `PaperII/MinOrder.lean:146` | literal (`DEC`) |
| Prop 1, minimum order, real designs: `t_min^ℝ ≤ r ↔ DECℂ r` | `tMinC_le_iff_decC` | `PaperII/Realification.lean` | literal (`DECℂ`) |
| the least feasible real order is feasible | `decC_sInf_tMinCSet` | `PaperII/Realification.lean` | literal (`DECℂ`) |
| the abstract least feasible order (monotone predicate) | `exists_least_of_monotone` | `PaperII/MinOrder.lean:157` | literal |

## §III The spectral lower bound

| paper item | declaration | file:line | status |
|---|---|---|---|
| Prop 2: `rank[U₀;V₀] + 1 ≤ s₀ + t` | `lowerBound_core` | `PaperII/LowerBound.lean:57` | literal |
| Prop 2: `rank[U₀;V₀] − s₀ + 1 ≤ t` | `lowerBound_sub` | `PaperII/LowerBound.lean:76` | literal |
| Prop 2 as a bound on the minimum order: `a − s₀ + 1 ≤ t_min` | `le_tMin_of_lowerBound` | `PaperII/MinOrder.lean` | literal |
| `rank[U₀;V₀] ≤ ω` | `finrank_sup_pi_le` | `PaperII/LowerBound.lean:40` | literal |
| Prop 3, numerical half: `dim W = a+1 ⇒ t = a−s₀+1` | `t_eq_of_finrank` | `PaperII/LowerBound.lean:86` | literal |
| Prop 3, graph extension: `π₁W(G,b) = U`, `π₂ ⊆ U`, `dim = dim U + 1` | `graphExt`, `graphExt_pi1`, `graphExt_pi2_le`, `graphExt_finrank` | `PaperII/GraphExtension.lean` | literal |
| Prop 3, pencil: `πλ W(G,b) = (λI−G)U + span{b}`; rank condition ⇒ feasible | `graphExt_piLam`, `graphExt_feasible` | `PaperII/GraphExtension.lean` | literal |
| Prop 3, `(G,b)` direction: `t = dim U + 1 − s₀` | `t_eq_of_graph` | `PaperII/GraphExtension.lean` | literal |
| Prop 3, converse: `W = W(G,b)` for a feasible `W` with `dim W = dim π₁W + 1` | `exists_graph_representation` | `PaperII/GraphExtract.lean` | literal |

## Not formalised

| paper item | reason |
|---|---|
| — | (Prop 3 is complete in both directions; see the two rows below and the `(G,b)` rows above) |
| Theorem 4, the `O(log(ℓ+2))` call count | the ordering is `tMin_le_iff_dec` and the least element is `dec_sInf_tMinSet`; the arithmetic of the call count is not formalised |
| Corollary 5 (OPT), Corollary 6 (FIND) | complexity statements inherited from Paper I; FIND's bit model is open in the paper |
| the appendix instance (`q_min = 4`) | exact rational certificate; belongs to the Python verification layer |

## Verification

`lake build Q1Paper.PaperII.MainTheorems` (9174 jobs) and
`lake env lean Q1Paper/PaperII/ClaimsCheck.lean`; the axiom audit is
`Q1Paper/PaperII/Audit.lean` checked by `scripts/check_paperI_axioms.py`
(48 declarations, only `propext`, `Classical.choice`, `Quot.sound`).
