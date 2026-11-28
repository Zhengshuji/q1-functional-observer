# Paper V — dependency table (paper numbering)

Purpose: a check that every theorem's hypotheses are established before it is used, and that
every use of a theorem still satisfies its hypotheses. This is a meta document; the paper does
not contain it.

**Numbering.** All theorem-like environments share one counter, so the actual numbers are:
pair = 1, fibre = 2, criterion = 4, specialisation = 5, intrinsic = 6, witness = 7, one-sided
test = 8, bad/uniformly bad (definition) = 9, cone = 10, coefficient test = 11, uniformly bad
closed = 12, fixed spectral factor = 13, closed; not necessarily thin = 14, infeasibility = 15,
column drop = 16, column dependence = 17, regime = 19, $t=1$ = 22, generic combination (appendix)
= 26.

| Item | Hypotheses | Where they come from | Used by |
|---|---|---|---|
| 1 pair | none | — | 2, 4, 9 |
| 2 fibre | $H$, $Z''$, $T$ | §II | 4, 11, 16, 17, 22 |
| 4 criterion | $d'\ge1$; $\mathcal F_U\ne\varnothing$ | assumption; compatibility | 22 |
| 5 specialisation | none | — | 10, 13 |
| 6 intrinsic form | none | — | §III discussion |
| 7 witness | $U$ rational; $\mathcal F_U\ne\varnothing$; $\deg g=0$ | assumption; 4 | 19 |
| 8 one-sided test | $\mathcal F_U\ne\varnothing$ | assumption | 19 |
| 9 bad / uniformly bad | $\mathcal F_U\ne\varnothing$ | definition | 10, 11, 12, 13, 14, 15 |
| 10 cone | $\deg g\ge1$ | 4 (contrapositive) | used inside 4's converse, not by 13 |
| 11 coefficient test | $\mathcal F_U\ne\varnothing$ | assumption | 12 |
| 12 uniformly bad closed | none beyond §II | stratification by $a$, homogenisation, properness | 14 |
| 13 fixed spectral factor | $\mathcal F_U\ne\varnothing$; $q>d'$; common fibre direction | assumption; 2 (direction automatic) | 14 (identifies $\mathcal B$ with $\mathcal B_{\mathrm{unif}}$) |
| 14 closed; not necessarily thin | $q>d'$ + common direction | 12 + 13 | 19 |
| 15 infeasibility | $d'$ fixed; $\mathcal C$ the compatibility stratum | §II | §V discussion |
| 16 column drop | column identity on $J$; $J\cap\operatorname{supp}(T)=\varnothing$ | assumption | the mechanisms remark |
| 17 column dependence | subspace $A$, $\dim A>k-d'$, two identities | assumption | the mechanisms remark |
| 19 regime | $d'+t-k\ge s$; $d'\ge\dim U_0$; **$q>d'$** (for the density sentence, via 14) | assumption | §V discussion |
| 22 $t=1$ | $t=1$; $d'\ge1$; $a\ge1$ (hypothesis) | assumption (rank barrier not proved here) | §V discussion |
| 26 generic combination | none | appendix | 13, 8 |

## The chain that closes the closure argument

$$\underbrace{\mathcal B_{\mathrm{unif}}\ \text{closed}}_{12}\ +\ \underbrace{\mathcal B=\mathcal B_{\mathrm{unif}}}_{13}
\ \Longrightarrow\ \mathcal B\ \text{closed}\ \Longrightarrow\
\underbrace{\{\text{feasible}\}=\mathcal C\setminus\mathcal B}_{9,\ \text{by definition}}\ \Longrightarrow\ 14,\ 19.$$

The last identification is **definitional**: 9 says a $U\in\mathcal C$ is bad when every point of its
fibre fails, so its negation is exactly the existence of a feasible point. It is *not* a theorem, and
the earlier version of this table wrongly attributed it to 15.

## Residual hypotheses that the paper does not prove

1. $a\ge1$ in item 22 (the rank barrier of the companion development; stated as a hypothesis);
2. $U$ rational in item 7 (otherwise only algebraic witnesses are available);
3. finiteness of the invariant subspaces in item 22 (stated as a hypothesis);
4. $q>d'$ wherever uniformity is used (stated at each use: 13, 14, 19).
