import Q1Paper.PaperI.S00_Interface.MainTheorems

/-!
# §4.2 Fixed parameter

Paper I, label `sec:fpt`.  This file contains **no proofs**: it is a reading entry that lists the
section's steps in proof order, each with the declaration that carries it.  Every step is a
`#check`, so if a declaration is renamed this file stops compiling — that is what keeps it honest.

## The problem

Replace the order $q$ by the parameter $\ell$, and obtain a bound that is fixed-parameter
tractable rather than merely polynomial for fixed order.

## What it consumes

The chart enumeration and cost model of §4.1.

## The result

- `Q1Paper.theorem2_fpt_conditional`

Everything else below is scaffolding for those: **tool** = general linear algebra that does not
mention this problem; **bridge** = a translation between two formulations of the same fact;
**core** = mathematical content specific to this paper.

## Steps, in proof order

1. **[core]** the FPT bound, conditional on the declared backend — `Q1Paper.theorem2_fpt_conditional`

## What the next section does with it

§4.3 and §4.4 handle the degenerate branch and the $\exists\mathbb R$ statement.
-/

-- Each step below is the machine-checked part of the list above.
#check Q1Paper.theorem2_fpt_conditional
