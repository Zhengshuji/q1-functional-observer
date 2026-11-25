import Q1Paper.PaperI.MainTheorems

/-!
# §4.4 Membership in the existential theory of the reals

Paper I, label `sec:existsr`.  This file contains **no proofs**: it is a reading entry that lists the
section's steps in proof order, each with the declaration that carries it.  Every step is a
`#check`, so if a declaration is renamed this file stops compiling — that is what keeps it honest.

## The problem

State the decision problem as the existence of an encoding witness, with no abstract hypothesis
left over.

## What it consumes

The certificate of §3.4 and the bounds of §4.1.

## Steps, in proof order

1. the decision problem is equivalent to the existence of an encoding witness — `Q1Paper.Thm5.DECℂ_iff_exists_encodes_auto`

## What the next section does with it

The appendix accounts for the bit cost of the exact-arithmetic layer.
-/

-- Each step below is the machine-checked part of the list above.
#check Q1Paper.Thm5.DECℂ_iff_exists_encodes_auto
