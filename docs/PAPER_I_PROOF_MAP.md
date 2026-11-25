# Paper I: proof map

**Read `Q1Paper/PaperI/S00_Interface/Claims.lean` first.**  It lists the paper's items in the paper's own order, each
with its LaTeX label, its coverage status and the name of the declaration that proves it — and it
contains no proofs at all (zero declarations), so it reads as a checklist rather than as Lean code.
It is generated from `CLAIMS.md`, and `ClaimsCheck.lean` machine-checks that every declaration it
names really exists.

The table below answers the question that file cannot: **where** each proof lives, i.e. the module and
line that define the declaration.

One row per paper item: the Lean declaration that carries it, the file and line that define it, and
its coverage status.  The `label` column is the paper's own LaTeX label, so a claim can be found in
`paper/paper_I_dec.tex` by searching for it.

**How the status column reads**

| status | meaning |
|---|---|
| `[Lean]` | the paper's statement is formalised as stated, and kernel-checked |
| `[Lean-conditional]` | formalised, but relative to a declared hypothesis (currently: the real-algebraic backend for Theorems 1 and 2) |
| `[Paper proof]` | argued in the paper only |

**What the table does not say, and you should know**

* It says *a* declaration carries an item, not that the declaration says exactly what the paper says.
  Where the two differ deliberately, the declaration's docstring records why — the two known cases are
  Claim 15's `22n³L` constant (the paper's `20` bound plus the `n²+1` term) and the FPT specification's
  degree hypothesis `deg ≤ 2·vars + 2`, which the paper's chart system satisfies.
* `ω = 0` is not covered by the completeness theorem; see the "What is *not* established" section of
  `docs/START_HERE.md`.
* A row's status is about the **mathematical** item.  It is not a statement that the corresponding
  algorithm is verified end to end; that is `docs/ALGORITHM_CORRECTNESS_MAP.md`'s subject.

**Beyond the paper's claim list**, these declarations carry the algorithm-side development and are not
rows above: `ChartComplete.phiPoint_of_conditions` / `feasible_of_phiPoint` (the chart equivalence at
the compressed level), `ComplexSoundness.decComplex_of_phiPoint` (soundness against `complexDEC`),
`ComplexCompleteness.phiPoint_of_complexDEC` (completeness, `ω ≥ 1`), and the transfer lemmas
`ReindexAlgebraic.rawAlgebraic_submatrix`, `ReindexSpectral.rawSpectral_submatrix`, `KernelLift.range_mulVecLin_eq_ker_map_complex`.

## Proof routes for the main claims

The table above says *which* declaration carries an item.  This section says *how the proof runs*, at
the granularity of modules — enough to read the argument without following 86 imports.  The order is
the order of the mathematical dependency, which is also the order of the imports.

**Claim 1** (the rank identity).  Single module, `Q1Paper/G4RankIdentity.lean`; both halves are matrix
adaptations of the abstract subspace identity, and nothing else depends on the file.

**Claim 2** (compression).  `CompressionMatrix.lean` is the whole route: the rank bookkeeping
(`rank_fromRows_eq_rank_add_mul`, `rank_vstack_add_rank_mul'`), then the two biconditionals
`rawAlgebraic_iff_rowSpace` and `rawSpectral_iff_compressed`, which are what let every later step work
with the small pair `(H, H_A)` instead of the free block.  `KernelBasis.lean` supplies `N`.

**Claims 3–8** (the subspace picture).  `Claims38.lean` carries 3, 4 (forward), 5, 6, 7 and the rank form
of 8; `Claim4Converse.lean` is the converse of 4 (every admissible `W` is realised by some `R`), which is
what makes the search over subspaces complete rather than merely sound.  Claim 8's combinatorial form is
split across `Claim8_ElemSymm.lean` (the statement in the paper's terms), `Claim8_SumSquares.lean` (the algebraic
core, elementary symmetric functions and the Gram blocks) and `Claim8_Disjunction.lean` (the wiring between
them).

**Claims 9–12** (the certificate).  The route is: `SpectralMinor.lean` and `MinorRank.lean` turn the
pencil condition into a condition on maximal minors; `BezoutReal.lean` (with `BezoutDeg.lean`,
`G2Assembly.lean`) produces the real multipliers; `Window.lean` collects the minors' coefficient
vectors into the window matrix; `GramSystem.lean`, `GramKernel.lean`, `GramCompression.lean`, `GramFamilyBridge.lean`
and `CauchyBinet.lean` assemble the Gram matrix and the `Zᵀ Z x = e₀` system; `Complexify.lean` is the
real-to-complex bridge that the "no common **complex** root" statement needs; `Claim11_MinorsGram.lean` is the
assembly, and `Claim12.lean` repeats it for a full-column-rank pencil `λ X - G`.

**Claims 13–16** (rationality and size).  `RationalBasis.lean` (rational bases), then the coefficient
layer `MinorCoeff.lean` and `CompressedGram.lean` via `BitLen.lean`, `BitLenAdd.lean`,
`BitLenMatMul.lean`; `Claim15_Arithmetic.lean` carries the constant bookkeeping.  `Claim16_Gcd.lean` and
`BezoutBounded.lean` dispose of the zero-free-row case.

**Proposition 4 and Theorems 1–2**.  `Prop4.lean` is the `r = 0` reduction to the system (R0).
`ChartCount.lean` is the chart-count arithmetic; `RenegarParams.lean` declares the backend's parameters
and cost model for Theorem 1 (`ChartSpecFixedDeg`), `FptSpec.lean` for Theorem 2 (`FptChartSpec`); the
theorems are conditional on those structures by construction.

**Theorems 5 and the complexity appendix**.  `T5DecC.lean`, `T5Complete.lean`, `T5Auto.lean` build the
`∃ℝ` encoding; `ExactDiv.lean`, `ComplexityCounts.lean`, `BareissBase.lean`, `BareissTableau.lean`,
`BareissAssemble.lean` are the exact-division / Bareiss layer behind Claims 19 and 21.


<!-- BEGIN GENERATED: claim -> declaration -> file -->

Generated by `scripts/paper_lean_index.py` from `Q1Paper/PaperI/CLAIMS.md`; do not edit by hand.

| paper item | label | Lean declaration | file : line | status |
|---|---|---|---|---|
| Claim 1 | `lem:rankid` | `Q1Paper.rank_vstack_add_rank_mul` | `Q1Paper/G4RankIdentity.lean:75` | [Lean] |
| Claim 2 | `lem:compression` | `Q1Paper.PaperI.DEC_iff_compressed` | `Q1Paper/PaperI/S01_Compression/CompressionMatrix.lean:258` | [Lean] |
| Claim 3 | `lem:attainable` | `Q1Paper.claim3_attainable` | `Q1Paper/PaperI/S02_Subspace/Claims38.lean:110` | [Lean] |
| Claim 4 (forward) | `lem:sandwich` | `Q1Paper.claim4_sandwich` | `Q1Paper/PaperI/S02_Subspace/Claims38.lean:185` | [Lean] |
| Claim 4 (converse) | `lem:sandwich` | `Q1Paper.claim4_converse` | `Q1Paper/PaperI/S02_Subspace/Claim4Converse.lean:52` | [Lean] |
| Claim 5 | `lem:W-conditions` | `Q1Paper.claim5_conditions_depend_on_W` | `Q1Paper/PaperI/S02_Subspace/Claims38.lean:280` | [Lean] |
| Claim 6 | `lem:struct` | `Q1Paper.claim6_struct` | `Q1Paper/PaperI/S02_Subspace/Claims38.lean:325` | [Lean] |
| Claim 7 | `lem:monotone` | `Q1Paper.claim7_DEC_succ` | `Q1Paper/PaperI/S02_Subspace/Claims38.lean:586` | [Lean] |
| Claim 8 (rank form) | `lem:rankcons` | `Q1Paper.claim8_rank_consistency` | `Q1Paper/PaperI/S02_Subspace/Claims38.lean:423` | [Lean] |
| Claim 8 (disjunction) | `lem:rankcons` | `Q1Paper.PaperI.Claim8_ElemSymm.claim8_disjunction` | `Q1Paper/PaperI/S02_Subspace/Claim8_ElemSymm.lean:183` | [Lean] |
| Claim 9 | `lem:bezout` | `Q1Paper.exists_bezout_family_real` | `Q1Paper/BezoutReal.lean:245` | [Lean] |
| Claim 10 | `lem:window` | `Q1Paper.rowSpace_windowMatrix_eq_windowSet` | `Q1Paper/Window.lean:229` | [Lean] |
| Claim 11 | `prop:gram` | `Q1Paper.PaperI.claim11_iff_gram` | `Q1Paper/PaperI/S03_Certificate/Claim11_MinorsGram.lean:138` | [Lean] |
| Claim 12 | `clm:gramQ` | `Q1Paper.PaperI.claim12_iff_gram` | `Q1Paper/PaperI/S03_Certificate/Claim12.lean:47` | [Lean] |
| Claim 13 | `lem:rationalbasis` | `Q1Paper.PaperI.exists_rational_bases_bounded` | `Q1Paper/PaperI/S04_Rationality/RationalBasis.lean:616` | [Lean] |
| Claim 14 | `clm:chartdata` | `Q1Paper.PaperI.Chart14.exists_chart_bases` | `Q1Paper/PaperI/S02_Subspace/Claim14_Bases.lean:296` | [Lean] |
| Claim 15 (coefficients) | `lem:coeff` | `Q1Paper.MinorCoeff.pencilMinor_coeff_bitLen_le` | `Q1Paper/PaperI/S04_Rationality/MinorCoeff.lean:294` | [Lean] |
| Claim 15 (Gram entries) | `lem:coeff` | `Q1Paper.PaperI.compressedGram_entry_bitLen_le` | `Q1Paper/PaperI/S03_Certificate/CompressedGram.lean:164` | [Lean] |
| Claim 16 (i)-(iii) | `lem:zero` | `Q1Paper.claim16_i_iff_iii` | `Q1Paper/PaperI/S03_Certificate/Claim16_Gcd.lean:376` | [Lean] |
| Claim 16 (iii)=>(iv) | `lem:zero` | `Q1Paper.claim16_iii_implies_iv_of_gcd_isConst` | `Q1Paper/PaperI/S03_Certificate/BezoutBounded.lean:349` | [Lean] |
| Claim 19 | `app:zero` | `Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_quadratic` | `Q1Paper/PaperI/S05_Complexity/ExactDiv.lean:179` | [Lean] |
| Claim 21 | `app:r0` | `Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_n21_L2` | `Q1Paper/PaperI/S05_Complexity/ExactDiv.lean:229` | [Lean] |
| Proposition 4 | `prop:zero` | `Q1Paper.prop4_r0_iff_spectral` | `Q1Paper/PaperI/S06_Algorithms/Prop4.lean:64` | [Lean] |
| Theorem 1 | `thm:fixedq` | `Q1Paper.theorem1_conditional_params_fixedDeg` | `Q1Paper/PaperI/S06_Algorithms/RenegarParams.lean:383` | [Lean-conditional] |
| Theorem 2 | `thm:fpt` | `Q1Paper.theorem2_fpt_conditional` | `Q1Paper/PaperI/S06_Algorithms/FptSpec.lean:395` | [Lean-conditional] |
| Theorem 5 | `thm:existsr` | `Q1Paper.Thm5.DECℂ_iff_exists_encodes_auto` | `Q1Paper/PaperI/S07_ExistsReal/T5Auto.lean:82` | [Lean] |

<!-- END GENERATED -->
