import Q1Paper.PaperI.S00_Interface.MainTheorems

/-!
# The chart equivalence: from the certificate to the decision problem

Paper I, label `sec:algorithms`.  This file contains **no proofs**: it is a reading entry that lists the
section's steps in proof order, each with the declaration that carries it.  Every step is a
`#check`, so if a declaration is renamed this file stops compiling — that is what keeps it honest.

## The problem

The paper's condition (5b) quantifies over the **complex** numbers, and the chart argument
returns a witness — a point of `eq:phi` — rather than a truth value.  This section states the
specification those two facts require, and proves that a chart point and the specification
imply each other.  It is the bridge between the certificate of §3.4 and the algorithms of §4.

## What it consumes

The compressed conditions of §3.4 and the chart data of §3.4.

## The result

- `Q1Paper.PaperI.ComplexSoundness.decComplex_of_phiPoint`
- `Q1Paper.PaperI.ComplexCompleteness.phiPoint_of_complexDEC`

Everything else below is scaffolding for those: **tool** = general linear algebra that does not
mention this problem; **bridge** = a translation between two formulations of the same fact;
**core** = mathematical content specific to this paper.

## Steps, in proof order

1. **[bridge]** the real-to-complex spectral bridge, so the paper's data can meet the certificate — `Q1Paper.PaperI.ChartComplex.complex_spectral_implies_real`
2. **[core]** the specification itself: `(5b)` over the complex numbers — `Q1Paper.PaperI.DecComplex.complexDEC`
3. **[bridge]** complex implies real, and that is the only direction that holds — `Q1Paper.PaperI.DecComplex.dec_of_complexDEC`
4. **[core]** a chart point witnesses the (real-lambda) decision problem — `Q1Paper.PaperI.Soundness.dec_of_phiPoint`
5. **[core]** a chart point witnesses the paper's own specification — `Q1Paper.PaperI.ComplexSoundness.decComplex_of_phiPoint`
6. **[bridge]** the complex condition compresses, so the two levels can be compared — `Q1Paper.PaperI.ComplexCompression.compressed_of_spectralComplexRaw`
7. **[core]** and conversely the specification yields a chart point (for `omega >= 1`) — `Q1Paper.PaperI.ComplexCompleteness.phiPoint_of_complexDEC`
8. **[bridge]** the chart point built from the two compressed conditions — `Q1Paper.PaperI.ChartComplete.phiPoint_of_conditions`
9. **[bridge]** the complexified kernel basis spans the complex kernel — `Q1Paper.PaperI.KernelLift.range_mulVecLin_eq_ker_map_complex`
10. **[bridge]** row reindexing, which lets the chart speak about `[L0; R]` — `Q1Paper.PaperI.ReindexAlgebraic.rawAlgebraic_submatrix`
11. **[bridge]** the same for the spectral condition — `Q1Paper.PaperI.ReindexSpectral.rawSpectral_submatrix`
12. **[tool]** and `fromRows` commuting with the entrywise map, which makes the reindexing work — `Q1Paper.PaperI.FromRowsMap.fromRows_map`

## What the next section does with it

Nothing: this closes the formalisation.  The cost of acting on the witness is §4.1's subject.
-/

-- Each step below is the machine-checked part of the list above.
#check Q1Paper.PaperI.ChartComplex.complex_spectral_implies_real
#check Q1Paper.PaperI.DecComplex.complexDEC
#check Q1Paper.PaperI.DecComplex.dec_of_complexDEC
#check Q1Paper.PaperI.Soundness.dec_of_phiPoint
#check Q1Paper.PaperI.ComplexSoundness.decComplex_of_phiPoint
#check Q1Paper.PaperI.ComplexCompression.compressed_of_spectralComplexRaw
#check Q1Paper.PaperI.ComplexCompleteness.phiPoint_of_complexDEC
#check Q1Paper.PaperI.ChartComplete.phiPoint_of_conditions
#check Q1Paper.PaperI.KernelLift.range_mulVecLin_eq_ker_map_complex
#check Q1Paper.PaperI.ReindexAlgebraic.rawAlgebraic_submatrix
#check Q1Paper.PaperI.ReindexSpectral.rawSpectral_submatrix
#check Q1Paper.PaperI.FromRowsMap.fromRows_map
