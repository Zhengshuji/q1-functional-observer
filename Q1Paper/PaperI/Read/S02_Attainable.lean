import Q1Paper.PaperI.S00_Interface.MainTheorems

/-!
# §3.2 The space of attainable row pairs

Paper I, label `sec:free`.  This file contains **no proofs**: it is a reading entry that lists the
section's steps in proof order, each with the declaration that carries it.  Every step is a
`#check`, so if a declaration is renamed this file stops compiling — that is what keeps it honest.

## The problem

Describe the set of subspaces $W$ that some free block $R$ can produce, and count the degrees of
freedom.  Without this, a search over subspaces would not be justified.

## What it consumes

The compressed pair from §3.1.

## The result

- `Q1Paper.claim3_attainable`
- `Q1Paper.claim4_sandwich`
- `Q1Paper.claim4_converse`

Everything else below is scaffolding for those: **tool** = general linear algebra that does not
mention this problem; **bridge** = a translation between two formulations of the same fact;
**core** = mathematical content specific to this paper.

## Steps, in proof order

1. **[core]** the attainable pairs have dimension $d_0$, giving $\kappa_{\text{obs}} = r d_0$ — `Q1Paper.claim3_attainable`
2. **[core]** every attainable $W$ sits between $W_0$ and $T$ — `Q1Paper.claim4_sandwich`
3. **[core]** and conversely every such $W$ is attained by some $R$ — `Q1Paper.claim4_converse`

## What the next section does with it

§3.3 may therefore quantify over subspaces $W$ instead of over matrices $R$.
-/

-- Each step below is the machine-checked part of the list above.
#check Q1Paper.claim3_attainable
#check Q1Paper.claim4_sandwich
#check Q1Paper.claim4_converse
