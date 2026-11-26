import Q1Paper.PaperI.S00_Interface.MainTheorems

/-!
# §3.4 The finite certificate

Paper I, label `sec:certificate`.  This file contains **no proofs**: it is a reading entry that lists the
section's steps in proof order, each with the declaration that carries it.  Every step is a
`#check`, so if a declaration is renamed this file stops compiling — that is what keeps it honest.

## The problem

Replace `rank $(\lambda H - H_A) = \omega$ for every complex $\lambda$' — a quantifier over
$\lambda$ — by a finite system that a real-algebraic solver can decide.

## What it consumes

The subspace reduction from §3.3.

## The result

- `Q1Paper.PaperI.claim11_iff_gram`
- `Q1Paper.PaperI.claim12_iff_gram`

Everything else below is scaffolding for those: **tool** = general linear algebra that does not
mention this problem; **bridge** = a translation between two formulations of the same fact;
**core** = mathematical content specific to this paper.

## Steps, in proof order

1. **[core]** real Bézout multipliers exist, so the certificate can stay real — `Q1Paper.exists_bezout_family_real`
2. **[bridge]** the window matrix's row space is the window set — `Q1Paper.rowSpace_windowMatrix_eq_windowSet`
3. **[core]** $(5b)$ is equivalent to solvability of the Gram system $Z^{\mathsf T} Z x = e_0$ — `Q1Paper.PaperI.claim11_iff_gram`
4. **[core]** the same for a full-column-rank pencil $\lambda X - G$, the chart coordinates — `Q1Paper.PaperI.claim12_iff_gram`
5. **[bridge]** those two are stated for the injective-indexed minors; every subset pair has $(\omega!)^2$ preimages, so no subset row is missed — `Q1Paper.PaperI.imagePair_surjective`
6. **[bridge]** hence the two window matrices span the same rows, and the certificate transfers to the subset family the paper's Cauchy--Binet argument uses — `Q1Paper.PaperI.rowSpace_windowInj_eq_windowSub`
7. **[core]** which is Claim 11 for the subset-indexed Gram matrix — `Q1Paper.PaperI.claim11_iff_gram_subset`
8. **[core]** and Claim 12 in the same form — `Q1Paper.PaperI.claim12_iff_gram_subset`

## What the next section does with it

§4 needs the certificate to be rational and small; that is §4.1.
-/

-- Each step below is the machine-checked part of the list above.
#check Q1Paper.exists_bezout_family_real
#check Q1Paper.rowSpace_windowMatrix_eq_windowSet
#check Q1Paper.PaperI.claim11_iff_gram
#check Q1Paper.PaperI.claim12_iff_gram
#check Q1Paper.PaperI.imagePair_surjective
#check Q1Paper.PaperI.rowSpace_windowInj_eq_windowSub
#check Q1Paper.PaperI.claim11_iff_gram_subset
#check Q1Paper.PaperI.claim12_iff_gram_subset
