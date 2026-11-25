# Paper II: paper item → Lean declaration

One row per item of `paper/paper_II_minorder.tex`, with the declaration that proves
it and where it lives.  Line numbers refer to the files at commit `feb5b06` (they
move when a file is edited above them; the declaration names and their
`#check`s in `Q1Paper/PaperII/ClaimsCheck.lean` are stable).

**Scope.**  Items marked *reused* are proved in the Paper I tree and enter Paper II
through the column split `Φ`.  Items concerning `DEC` are the field-generic
predicate over `ℂ` (complex free blocks); the paper's real-design specification
`DECℂ` has its forward direction and monotonicity proved.  The remaining
`DECℂ` items are the open real-compression lemma
(`workspace/paper_split/PAPER_II_LEAN_PLAN.md` §8.5).

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
| converse, `DECℂ` | — | — | **open** (real-compression) |

## §III Monotonicity and saturation

| paper item | declaration | file:line | status |
|---|---|---|---|
| Claim 5, monotone, `DECℂ` | `decC_mono` | `PaperII/Monotone.lean:154` | literal |
| Claim 5, monotone, `DEC` | `dec_mono_complex` | `PaperII/Saturate.lean:107` | literal |
| Claim 5, saturation, `DEC` | `dec_saturates` | `PaperII/Saturate.lean:87` | literal |
| Claim 5, saturation, `DECℂ` | — | — | **open** (real-compression) |

## §III Minimum order

| paper item | declaration | file:line | status |
|---|---|---|---|
| Prop 1: `q_min = r₀ + t_min` (`t_min ≤ r ↔ DEC (r₀+r)`) | `tMin_le_iff_dec` | `PaperII/MinOrder.lean:59` | literal (`DEC`) |
| Prop 1: `t_min ≤ 2ℓ` | `tMin_le_two_ell` (via `omega_le_ell`, `t_le_two_ell`) | `PaperII/MinOrder.lean:126,90,109` | literal (`DEC`) |
| Prop 1 with `t_min = ⊤` when infeasible | `tMin`, `tMinSet` | `PaperII/MinOrder.lean:50,43` | literal |

## §III The spectral lower bound

| paper item | declaration | file:line | status |
|---|---|---|---|
| Prop 2: `rank[U₀;V₀] + 1 ≤ s₀ + t` | `lowerBound_core` | `PaperII/LowerBound.lean:57` | literal |
| Prop 2: `rank[U₀;V₀] − s₀ + 1 ≤ t` | `lowerBound_sub` | `PaperII/LowerBound.lean:76` | literal |
| `rank[U₀;V₀] ≤ ω` | `finrank_sup_pi_le` | `PaperII/LowerBound.lean:40` | literal |

## Not formalised

| paper item | reason |
|---|---|
| Prop 3 (tightness, both directions) | not started; the `(G,b) ⇒` direction is the natural next target |
| Theorem 4 (interface: `O(log(ℓ+2))` DEC calls) | the counting is not formalised; the lifting half is `claim4_converse` |
| Corollary 5 (OPT), Corollary 6 (FIND) | complexity statements inherited from Paper I; FIND's bit model is open in the paper |
| the appendix instance (`q_min = 4`) | exact rational certificate; belongs to the Python verification layer |

## Verification

`lake build Q1Paper.PaperII.MainTheorems` (9174 jobs) and
`lake env lean Q1Paper/PaperII/ClaimsCheck.lean`; the axiom audit is
`Q1Paper/PaperII/Audit.lean` checked by `scripts/check_paperI_axioms.py`
(48 declarations, only `propext`, `Classical.choice`, `Quot.sound`).
