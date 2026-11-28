import Q1Paper.PaperV.MainTheorems

/-!
Q1Paper/PaperV/Read/S01_Fibre.lean

§II  The fibre.

This file contains **no proofs**: it is a reading entry that lists the steps in proof
order, each with the declaration that carries it.  Every step is a `#check`, so a
rename breaks the build instead of silently rotting the map.

## What it sets up

The paper fixes the compressed row space `U` of an observer and lets the free rows vary.
The admissible values of `H_A` form the *fibre*, and Theorem 2 says it is empty or a
coset of `T ⊓ U`: the per-row fibre `{x ∈ T | x + y ∈ U}` is nonempty exactly when the
translate `y` lies in `U + T`, i.e. exactly when `U Z'' ⊆ U + T` holds row by row.

## The result

- `Q1Paper.PaperV.fibre`, `mem_fibre`
- `Q1Paper.PaperV.fibre_nonempty_iff`
- `Q1Paper.PaperV.fibre_eq_coset`
- `Q1Paper.PaperV.fibre_prod_nonempty_iff`
-/

#check @Q1Paper.PaperV.fibre
#check @Q1Paper.PaperV.mem_fibre
#check @Q1Paper.PaperV.fibre_nonempty_iff
#check @Q1Paper.PaperV.fibre_eq_coset
#check @Q1Paper.PaperV.fibre_prod_nonempty_iff
