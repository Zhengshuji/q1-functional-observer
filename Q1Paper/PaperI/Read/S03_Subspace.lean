import Q1Paper.PaperI.S00_Interface.MainTheorems

/-!
# §3.3 The subspace reduction

Paper I, label `sec:subspace`.  This file contains **no proofs**: it is a reading entry that lists the
section's steps in proof order, each with the declaration that carries it.  Every step is a
`#check`, so if a declaration is renamed this file stops compiling — that is what keeps it honest.

## The problem

Show that $(5a)$ and $(5b)$ depend only on $W$, so that one test per subspace suffices, and
record the structural constraints on a feasible $W$.

## What it consumes

The subspace picture from §3.2.

## The result

- `Q1Paper.claim5_conditions_depend_on_W`
- `Q1Paper.claim6_struct`
- `Q1Paper.claim7_DEC_succ`
- `Q1Paper.claim8_rank_consistency`

Everything else below is scaffolding for those: **tool** = general linear algebra that does not
mention this problem; **bridge** = a translation between two formulations of the same fact;
**core** = mathematical content specific to this paper.

## Steps, in proof order

1. **[core]** the conditions depend only on $W$, never on which $R$ produced it — `Q1Paper.claim5_conditions_depend_on_W`
2. **[core]** a feasible $W$ satisfies $\omega + 1 \le \dim W \le 2\omega$ — `Q1Paper.claim6_struct`
3. **[core]** the problem is monotone in the order — `Q1Paper.claim7_DEC_succ`
4. **[core]** the rank-consistency criterion, which eliminates the intermediate $B$ — `Q1Paper.claim8_rank_consistency`
5. **[bridge]** its combinatorial form, as a disjunction over the elementary symmetric functions — `Q1Paper.PaperI.Claim8_ElemSymm.claim8_disjunction`

## What the next section does with it

§3.4 turns the spectral condition on a fixed $W$ into a finite algebraic certificate.
-/

-- Each step below is the machine-checked part of the list above.
#check Q1Paper.claim5_conditions_depend_on_W
#check Q1Paper.claim6_struct
#check Q1Paper.claim7_DEC_succ
#check Q1Paper.claim8_rank_consistency
#check Q1Paper.PaperI.Claim8_ElemSymm.claim8_disjunction
