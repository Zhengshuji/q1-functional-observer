# Paper V — dependency table (hypotheses and uses)

Purpose: the third review asked for a check that every theorem's hypotheses are established
before it is used, and that every use of a theorem still satisfies its hypotheses. This table
is that check. It is a *meta* document; the paper itself does not contain it.

Read "hypothesis source" as: where the hypothesis is either proved or explicitly assumed.

| Item | Hypotheses | Hypothesis source | Used by |
|---|---|---|---|
| Lemma 1 (pair) | none | — | Thm 2, Thm 4, Def 9 |
| Thm 2 (fibre) | $H$, $Z''$, $T$ given | §II definitions | Thm 4 (parametrisation), Prop 14, Prop 15, Prop 18, Thm 17 |
| Thm 4 (criterion) | $d'\ge1$; $\mathcal F_U\ne\varnothing$ | assumption; compatibility | Thm 17 |
| Lemma 5 (specialisation) | none | — | Cor 10, Thm 11 |
| Thm 6 (intrinsic) | none | — | §III discussion, §VI evidence |
| Thm 7 (witness) | $U$ rational; $\mathcal F_U\ne\varnothing$; $\deg g=0$ | assumption; Thm 4 | Thm 8, Thm 16 |
| Thm 8 (one-sided test) | $\mathcal F_U\ne\varnothing$ | assumption | Thm 16 |
| Def 9 (bad / uniformly bad) | $\mathcal F_U\ne\varnothing$ | definition | Cor 10, Prop 15, Cor 17, Thm 11, Thm 12, Thm 13 |
| Cor 10 | $\deg g\ge1$ | Thm 4 negation | Thm 11 |
| Prop 15 (coefficient test) | $\mathcal F_U\ne\varnothing$ | assumption | Cor 17 |
| Cor 17 (uniformly bad set closed) | none beyond §II | — | Thm 12, Thm 13 |
| Thm 11 (fixed spectral factor) | $\mathcal F_U\ne\varnothing$; $q>d'$; common fibre direction | assumption; Thm 2 (direction) | Thm 12 (identifies $\mathcal B$ with $\mathcal B_{\mathrm{unif}}$), Thm 13 |
| Thm 12 (closed; not thin) | $q>d'$ + common direction (through Thm 11) | Cor 17 + Thm 11 | Thm 13, Thm 16 |
| Thm 13 (infeasibility) | $d'$ fixed; $\mathcal C$ the compatibility stratum | §II | §V discussion |
| Prop 14 (column drop) | column identity on $J$; $J\cap\operatorname{supp}(T)=\varnothing$ | assumption | Remark on mechanisms |
| Prop 18 (column dependence) | subspace $A$, $\dim A>k-d'$, the two identities | assumption | Remark on mechanisms |
| Thm 16 (regime) | $d'+t-k\ge s$; $d'\ge\dim U_0$ | assumption | §V discussion |
| Thm 17 ($t=1$) | $t=1$; $d'\ge1$; $a\ge1$ (hypothesis) | assumption (the rank barrier is not proved here) | §V discussion |

## The chain that the third review asked about

$$\text{Thm 11 (pointwise}\Rightarrow\text{uniform)}\ \Longrightarrow\
\mathcal B=\mathcal B_{\mathrm{unif}}\ \Longrightarrow\
\mathcal C\setminus\mathcal B=\{\text{feasible}\}\ \Longrightarrow\ \text{Thm 12, Thm 13, Thm 16}.$$

Each arrow is now a named step: the first is Theorem 11, the second is the definition of
$\mathcal B_{\mathrm{unif}}$ plus Theorem 11, the third is Theorem 13, and the openness used in
Theorem 16 comes from Theorem 12.

## Residual assumptions that are *not* proved in the paper

1. $a\ge1$ in Theorem 17 (the rank barrier of the companion development; stated as a hypothesis);
2. $U$ rational in Theorem 7 (otherwise only algebraic witnesses are available);
3. the finiteness of the invariant subspaces in Theorem 17 (stated as a hypothesis).

Each is flagged at its point of use, and none is used silently.
