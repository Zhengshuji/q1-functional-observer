import Q1Paper.PaperI.S00_Interface.MainTheorems

/-!
# Appendix: explicit size bounds and bit cost

Paper I, label `app:size`.  This file contains **no proofs**: it is a reading entry that lists the
section's steps in proof order, each with the declaration that carries it.  Every step is a
`#check`, so if a declaration is renamed this file stops compiling — that is what keeps it honest.

## The problem

Account for the cost of the exact-arithmetic layer: the Bareiss tableau and its bit-length
behaviour, which is what makes the bounds in §4 concrete rather than asymptotic.

## What it consumes

The size bounds of §4.1.

## The result

- `Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_quadratic`
- `Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_n21_L2`

Everything else below is scaffolding for those: **tool** = general linear algebra that does not
mention this problem; **bridge** = a translation between two formulations of the same fact;
**core** = mathematical content specific to this paper.

## Steps, in proof order

1. **[core]** the $r = 0$ system's quadratic cost, with exact integer division — `Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_quadratic`
2. **[core]** the paper's $O(n^{21} L^2)$ bit-cost bound — `Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_n21_L2`

## What the next section does with it

Nothing; this closes the paper.
-/

-- Each step below is the machine-checked part of the list above.
#check Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_quadratic
#check Q1Paper.PaperI.ComplexityCounts.bareiss_total_bit_cost_le_n21_L2
