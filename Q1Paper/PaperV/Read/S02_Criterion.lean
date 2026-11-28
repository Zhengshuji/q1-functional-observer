import Q1Paper.PaperV.MainTheorems

/-!
Q1Paper/PaperV/Read/S02_Criterion.lean

§III  The criterion: the specialisation lemma.

This file contains **no proofs**: it is a reading entry that lists the steps in proof
order, each with the declaration that carries it.

## What it sets up

The criterion of Theorem 4 says that a fibre is feasible exactly when the gcd of the
`d'`-minors of the pencil, computed over the fibre's function field, has degree zero.
The only non-trivial step in that equivalence is that a positive-degree common divisor
cannot disappear when the fibre parameters are specialised: its primitive
representative has a constant λ-leading coefficient (a nonzero `d' × d'` minor of `H`),
and Lemma 2 says such a coefficient is never killed by specialisation.

## The result

- `Q1Paper.PaperV.natDegree_map_eval_of_leadingCoeff_const`
- `Q1Paper.PaperV.map_dvd_of_dvd`
- `Q1Paper.PaperV.specialized_common_factor`
-/

#check @Q1Paper.PaperV.natDegree_map_eval_of_leadingCoeff_const
#check @Q1Paper.PaperV.map_dvd_of_dvd
#check @Q1Paper.PaperV.specialized_common_factor
