import Q1Paper.PaperI.MainTheorems

/-!
# §3.1 Compression and the pencil criterion

Paper I, label `sec:compression`.  This file contains **no proofs**: it is a reading entry that lists the
section's steps in proof order, each with the declaration that carries it.  Every step is a
`#check`, so if a declaration is renamed this file stops compiling — that is what keeps it honest.

## The problem

Reduce the two conditions on the free block $\mathcal L$ to conditions on the small compressed
pair $(H, H_A) = (\mathcal L N, LA\,N)$, where $N$ is a basis of $\ker[C; CA]$.

## What it consumes

Nothing; this is the entry point.

## Steps, in proof order

1. the rank identity that makes the dimension bookkeeping exact — `Q1Paper.rank_vstack_add_rank_mul`
2. stacking does not change the row space it spans — `Q1Subspace.rowSpace_fromRows`
3. $(5a)$ is a row-space inclusion, not merely a rank test — `Q1Paper.PaperI.rawAlgebraic_iff_rowSpace`
4. so the raw conditions are equivalent to the compressed ones — `Q1Paper.PaperI.DEC_iff_compressed`

## What the next section does with it

§3.2 now asks which pairs $(H, H_A)$ are attainable at all.
-/

-- Each step below is the machine-checked part of the list above.
#check Q1Paper.rank_vstack_add_rank_mul
#check Q1Subspace.rowSpace_fromRows
#check Q1Paper.PaperI.rawAlgebraic_iff_rowSpace
#check Q1Paper.PaperI.DEC_iff_compressed
