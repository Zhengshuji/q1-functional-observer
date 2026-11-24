# Algorithm 1: implementation review

Scope: `verification/decide.py` against `paper/paper_I_dec.tex` (Algorithm 1, lines 940–969,
and the inner system `eq:phi`).  This file records what has actually been checked **and what
has not**; it is not a certificate that the implementation is correct.

Status: **review in progress**.  No discrepancy found so far, but roughly a third of the code
has been read line by line.

## What was checked

### §1 `eq:phi` (Round 1)

The paper's `eq:phi` has five items; `evaluate_phi` (line 947) evaluates each one, item by item,
and asserts it.

| paper item | implementation | verdict |
|---|---|---|
| (i) `e_ω(XᵀX) > 0` | `assert ai.rank(X) == omega` | equivalent: `X` is `q×ω` so `rank X ≤ ω`, and `e_ω(XᵀX) > 0 ⟺ rank(XᵀX) ≥ ω`; the equivalence is the Lean theorem `elemSymm_pos_iff_rank_ge` (`Q1Paper/PaperI/Claim8Ej.lean`) |
| (ii) `M(X,G)b = c(X,G)` consistent | `chart_linear_system` + `dec0.solve_exact` | exact solve, unknowns are the non-pivot entries of `B` |
| (iii) `X_iB = h0_i`, `G_iB = g0_i` (`i ≤ r0`) | one assert per row | ok |
| (iv) `D[(X_iB)ᵀ;(G_iB)ᵀ] = 0` (`i > r0`) | one assert per row of `ctx.D` | ok |
| (v) `ZᵀZ x = e₀` | `gram_window` / `gram_certificate` | **not read yet** |

`verify_feasible` (line 1094) re-checks the returned witness `L` with the *independent*
`audit_independent.cond_5a_orig` / `cond_5b_orig` and **asserts**, so a `feasible` verdict cannot
be wrong unless that independent checker is.

### §2 The refutations (Round 2)

`chart_obstruction` (line 816) returns an `Obstruction(kind, detail)`; the codes are documented
at lines 127–160.

* `R1` `ω < dim U_pres` (line 819)
* `R2` `ω > ℓ = rank(AN)` (line 822)
* `R4` when `U` is forced: refute at a fixed `λ₀` on the chart's own family, by an **exact
  polynomial identity test** (`_chart_family_obstruction`, line 686) — not by sampling.  The
  docstring's soundness direction is right: the chart is a subset of the family, so refuting the
  family refutes the chart.
* `R2` `ω > ℓ = rank(AN)`: sound, and the argument is worth recording — (5b) **at `λ = 0`**
  gives `rank H_A = ω`, while `H_A = L A N` gives `rank H_A ≤ ℓ`.  The `∀λ` hypothesis is used
  at one specific point.
* `R5` `ω = q`: `X` is `ω×ω` and invertible, so `λX − G = X(λI − GX⁻¹)`, and the square matrix
  `GX⁻¹` has a complex eigenvalue `λ₀` where the rank drops.  Sound.
* `R6` `ω+1 > dim T` or `> dim W₀ + r`: Claim 6 gives `dim W ≥ ω+1`, while `W ⊆ T` and
  `dim(W/W₀) ≤ r` give `dim W ≤ dim T` and `dim W ≤ dim W₀ + r`.  Sound.
* `R3` fixed-`λ₀` refutation on the whole affine family `F`, by an exact polynomial identity test
  (`_MPoly` determinants, not sampling); `F ⊇` chart, so refuting `F` refutes the chart.
* `bounds` (`ω > min(q,k)`): unreachable, the loop stops at `min(q,k)`; defensive only.
* `D1`: **body still not read**.

**Conclusion (Round 4).**  A wrong `feasible` is caught by `verify_feasible`'s independent
asserts, so the silent-risk direction is `infeasible`.  All six refutations were checked to be
**implications**, not reports of a failed search.

Crucially, `unsat` is never produced by "the search found nothing": in `decide` (line 1229) a
failed search yields `ChartOutcome(..., "unknown", certificate="no witness, no refutation")`, and
the top-level verdict is `infeasible` **only when no chart is `unknown`** (line 1239).

### §3 The chart enumeration (Round 3)

`limit = min(q, ctx.k)`, `for omega in range(1, limit + 1)`, and
`for J in itertools.combinations(range(ctx.k), omega)` (lines 1167–1190) — the same enumeration
as Algorithm 1.  The `limit < 1` branch returns `unknown` (line 1169); it is defensive and in
practice unreachable, because `k = 0` makes `h0 = g0 = 0` and step 4 has already returned.

## What was NOT checked

* `eq:phi` item (v) and the Gram window construction (`gram_window`, `gram_certificate`);
* `chart_linear_system` against Claim 8's `Mb = c`;
* the body of `D1`;
* `_search_omega`'s completeness (that it explores enough of the chart to justify "no witness");
* the 1292-line file as a whole.

## Known limitation of the implementation itself

Step 5 decides a chart only when it finds an explicit rational point or when one of `(R1)`–`(R6)`
/ `(D1)` applies; otherwise the chart, and possibly the instance, is `unknown`.  A complete
implementation needs an exact real-feasibility oracle for `Φ_{ω,J}`; it is not present and is not
faked.

Measured coverage (reported by the implementation's author, **not re-verified here**): over 113
swept instances, 42 feasible, 66 infeasible, 5 `unknown`; over the charts, 286 of 299 decided
(95.7 %).

## Why this document exists

The repository ships a decision procedure whose most dangerous failure mode is a *silent*
`infeasible` (a missed chart).  Recording exactly which parts have been read is the only way a
later reader can tell "reviewed" from "shipped".
