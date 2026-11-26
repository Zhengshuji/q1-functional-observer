# Paper II: paper item → Lean declaration

One row per item of `paper/paper_II_minorder.tex`, with the declaration that proves
it and where it lives.  Line numbers are indicative and move when a file is edited above them; the
declaration names and their `#check`s in `Q1Paper/PaperII/ClaimsCheck.lean` are the
stable reference (use them, not the line numbers, to locate a claim).

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
| Prop 3, the minimum saturates from a `(G,b)` pair: `t_min = a + 1 − s₀` | `tMin_eq_of_graph` | `PaperII/Tightness.lean` | literal |
| Prop 3, the data extracted from an attaining `W` | `exists_graph_of_tMin_eq` | `PaperII/Tightness.lean` | literal |
| Prop 3, `π₁W = U₀+V₀` at an attaining `W` | `pi1_eq_sup_of_finrank` | `PaperII/Tightness.lean` | literal |
| Prop 3, converse: `W = W(G,b)` for a feasible `W` with `dim W = dim π₁W + 1` | `exists_graph_representation` | `PaperII/GraphExtract.lean` | literal |

## Not formalised

| paper item | status / reason |
|---|---|
| Corollary 6 (FIND) | *within Paper II* the mathematical content of `Ψ_{t,ω}` is already formalised: items (iii)–(v) of the system (the sandwich and the pencil condition) are `isFeasible_pairRowSpace_iff` together with `claim5_conditions_depend_on_W`, and the equivalence ``a real solution of `Ψ_{t,ω}` exists iff the feasible `W` of that order exists'' is exactly that pair of statements.  What is *not* formalised is the chart parametrisation of items (i)–(ii) (`W = row[XB GB]` with `B` read off `X` on the pivot set), the sampling-point algorithm and the bit-cost bound — the paper states all three as citations to the companion paper (`Remark rem:find-bit`), not as results of this paper |
| FIND: the witness system `Ψ_{t,ω}`, the real-solution/feasible-`W` equivalence, and the sampling step | not formalised; the paper presents it as an algorithmic certificate scheme |
| the appendix instance (`q_min = 4`) | the full certificate is the Python layer (`scripts/verify_paperII_example.py`: (5a), vanishing pencil determinant, gcd of the 7×7 minors); `PaperII/Appendix.lean` re-checks in Lean the λ = 0 slice — the pencil `[−LA; CA; C]` is singular with the explicit integer kernel vector `appendix_pencil_kernel` |
| Theorem 4, the `O(log(ℓ+2))` call count | **formalised**: the bisection `bisectGo` with `bisectGo_spec` (length `≤ (hi−lo)/2^k`) and `bisectGo_collapses` (a single point after `log2(hi−lo)+1` halvings), on top of `half_width`, `lt_two_pow_log2_succ`, `div_two_pow_log2_succ_eq_zero`, `bisect_steps_le`, `log2_mono_le` (`PaperII/Complexity.lean`) |

## Resolved (previously listed as not formalised)

| paper item | now formalised by |
|---|---|
| Prop 3, single `↔` packaging (complex designs) | `tMin_eq_iff_graph` |
| Prop 3 over the real designs | `tMinC_eq_iff_real_graph`, with `tMinC_le_of_graph_real`, `tMinC_eq_of_real_graph` and `exists_real_graph_of_tMinC_eq`; the bridges are `exists_design_of_pairRowSpace`, `WR_eq_span_phiPair_WRreal`, `graphExt_span_phiPair`, `finrank_span_phiPair`, the projection commutations, the real points `re_im_mem_of_mem_span`/`mem_of_phi_mem_span` and `isFeasible_real_of_span_phiPair` |
| Theorem 4, the construction part | `claim4_converse` plus the real sandwich converse `exists_design_of_pairRowSpace` (recovering the design from a given `W`) |
| Prop 1 for real designs (`2ℓ`, spectral bound, `t_min ≤ t_min^ℝ`) | `tMinC_le_two_ell`, `le_tMinC_of_lowerBound`, `tMin_le_tMinC` |
| Corollary 5 (OPT) | `tMin_eq_bisectGo` (complex designs) and `tMinC_eq_bisectGo` (real designs): bisection on the decision predicate over `[0, 2ℓ]` returns the minimum order in `log₂(2ℓ)+1` calls, with the algorithm `bisectGo` formalised |
| Prop 2's non-degeneracy `ω > 0` | `omega_pos_of_nonzero` under `W₀ ≠ 0`, which is exactly the hypothesis added to Prop 3 in the paper |

## Verification

`lake build Q1Paper.PaperII.MainTheorems Q1Paper.PaperII.Read.All` (about 9.2k jobs; CI builds it) and
`lake env lean Q1Paper/PaperII/ClaimsCheck.lean`; the axiom audit is
`Q1Paper/PaperII/Audit.lean` checked by `scripts/check_paperI_axioms.py`
(106 declarations, only `propext`, `Classical.choice`, `Quot.sound`).
