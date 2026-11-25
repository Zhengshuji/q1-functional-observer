import Q1Paper.PaperI.MainTheorems

/-!
# §4.1 Fixed order: rationality, size, and the bound

Paper I, label `sec:fixedq`.  This file contains **no proofs**: it is a reading entry that lists the
section's steps in proof order, each with the declaration that carries it.  Every step is a
`#check`, so if a declaration is renamed this file stops compiling — that is what keeps it honest.

## The problem

Make the certificate rational and bound every coefficient, then feed it to a decision procedure
whose cost is known.

## What it consumes

The certificate from §3.4.

## The result

- `Q1Paper.prop4_r0_iff_spectral`
- `Q1Paper.theorem1_conditional_params_fixedDeg`

Everything else below is scaffolding for those: **tool** = general linear algebra that does not
mention this problem; **bridge** = a translation between two formulations of the same fact;
**core** = mathematical content specific to this paper.

## Steps, in proof order

1. **[bridge]** rational bases with explicit size bounds — `Q1Paper.PaperI.exists_rational_bases_bounded`
2. **[core]** the chart data, including bases of $T$, $S$ and $W_0$ — `Q1Paper.PaperI.Chart14.exists_chart_bases`
3. **[core]** every coefficient of every maximal minor is bounded — `Q1Paper.MinorCoeff.pencilMinor_coeff_bitLen_le`
4. **[core]** the compressed Gram entries are bounded too — `Q1Paper.PaperI.compressedGram_entry_bitLen_le`
5. **[core]** the degenerate $r = 0$ branch reduces to the system (R0) — `Q1Paper.prop4_r0_iff_spectral`
6. **[core]** and the resulting bound is $\mathcal L^{O(q^2)}$ — `Q1Paper.theorem1_conditional_params_fixedDeg`

## What the next section does with it

§4.2 re-does the count with $\ell = \operatorname{rank}(AN)$ as the parameter.
-/

-- Each step below is the machine-checked part of the list above.
#check Q1Paper.PaperI.exists_rational_bases_bounded
#check Q1Paper.PaperI.Chart14.exists_chart_bases
#check Q1Paper.MinorCoeff.pencilMinor_coeff_bitLen_le
#check Q1Paper.PaperI.compressedGram_entry_bitLen_le
#check Q1Paper.prop4_r0_iff_spectral
#check Q1Paper.theorem1_conditional_params_fixedDeg
