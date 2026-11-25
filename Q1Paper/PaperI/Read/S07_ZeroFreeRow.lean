import Q1Paper.PaperI.MainTheorems

/-!
# §4.3 The zero-free-row case

Paper I, label `sec:zero`.  This file contains **no proofs**: it is a reading entry that lists the
section's steps in proof order, each with the declaration that carries it.  Every step is a
`#check`, so if a declaration is renamed this file stops compiling — that is what keeps it honest.

## The problem

The general chart machinery is vacuous when there are no free rows; this branch is handled
separately, and the paper's claim is a chain of equivalences.

## What it consumes

Nothing from §4.1–4.2; this is a separate branch.

## Steps, in proof order

1. the spectral condition, the absence of a common root, and a constant gcd agree — `Q1Paper.claim16_i_iff_iii`
2. a constant gcd yields a rational left inverse of the required degree — `Q1Paper.claim16_iii_implies_iv_of_gcd_isConst`

## What the next section does with it

§4.4 packages the whole decision problem as an $\exists\mathbb R$ statement.
-/

-- Each step below is the machine-checked part of the list above.
#check Q1Paper.claim16_i_iff_iii
#check Q1Paper.claim16_iii_implies_iv_of_gcd_isConst
