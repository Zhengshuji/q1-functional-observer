# Algorithm 1: implementation review

> **Historical record.** This file documents a stage of the work and is kept for provenance.
> Gaps it describes may have been closed since; do not read it as the current status.
> Current status and the reading entry point: [START_HERE.md](START_HERE.md).


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
* `R5` `ω = q`: `X` is `ω×ω` and invertible, so `λX − G = X(λI − X⁻¹G)`, and the square matrix
  `X⁻¹G` has a complex eigenvalue `λ₀` where the rank drops.  Sound.  (An earlier version of
  this note wrote `X(λI − GX⁻¹)`, which is `λX − XGX⁻¹`, not `λX − G`; the conclusion is
  unchanged but the factorization was wrong.  Found by an external review.)
* `R6` `ω+1 > dim T` or `> dim W₀ + r`: Claim 6 gives `dim W ≥ ω+1`, while `W ⊆ T` and
  `dim(W/W₀) ≤ r` give `dim W ≤ dim T` and `dim W ≤ dim W₀ + r`.  Sound.
* `R3` fixed-`λ₀` refutation on the whole affine family `F`, by an exact polynomial identity test
  (`_MPoly` determinants, not sampling); `F ⊇` chart, so refuting `F` refutes the chart.
* `bounds` (`ω > min(q,k)`): unreachable, the loop stops at `min(q,k)`; defensive only.
* `D1` (`_forced_W_analysis`, line 800): applies when `ω + 1 = dim T` and `dim T ≠ 0`.  Claim 6
  gives `dim W ≥ ω+1` and `W ⊆ T` gives `dim W ≤ dim T`, so `W = T` is the **only** candidate; the
  chart is then decided by evaluating (5a)/(5b) on `T`, with no search and no `unknown`.  Sound,
  and complete for that family.  The helper `_rank_deficient_at` tests whether **every** maximal
  minor of `λ₀H − H_A` vanishes **identically**, via `_MPoly` — an exact identity test, not
  sampling; this is what `R3`/`R4` rest on.

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

* `_search_omega`'s completeness (whether it explores enough of the chart to justify "no
  witness").  This does not affect soundness: an incomplete search produces `unknown`, never
  `infeasible`.
* the 1292-line file as a whole, line by line: the review is targeted at the parts that can
  change a verdict (the five items of `eq:phi`, the refutations, the enumeration).

## Round 9: `eq:phi` (v), and the cross-checks

`evaluate_phi` closes with

```
x = gram_certificate(X, G)                        # build Z^T Z x = e0 exactly
assert x is not None                              # (v) solvable
assert cond5b_pencil(X, G, omega)                  # cross-check A: the compressed pencil
assert pencil_constant_rank(H, H_A, omega)         # cross-check B: the actual (H, H_A)
```

so the chart point is checked three ways, and just before it the reconstructed `B` is asserted
to generate `H` for every row (`"(ii) the reconstructed B does not generate H"`).  All of these
are asserts: a wrong construction crashes the run instead of producing a wrong verdict.

`chart_linear_system` was read against `eq:phi` (ii): unknowns are the non-pivot entries of `B`,
the pivots are pinned to `B[t][J[t]] = 1` and `B[t][J[t']] = 0` (the chart normalisation of
`sec:param`), the equations are (iii) for `i ≤ r0` (`2k` per row) and (iv) for `i > r0`
(`2k − d0`).  This matches the paper item by item.

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

## Algorithm 2 (alg:fpt): what is implemented, and an open discrepancy

`verification/fpt.py` builds the objects of Algorithm 2 in exact rational arithmetic and asserts
their invariants: `N = ker[C;CA]`, `M = [N AN]`, `S = row(AN)`, `ell = rank(AN)`, `T = row[N AN]`,
`W0 = row(L0 M)`, `V = T cap (S x S)`, `s0`, `m'`, the Grassmann charts (counted, `2^{m'}`), the
chart matrix `Z_ch = [E0; C_J(Y) E_Q]` and its blocks `H(Y), G(Y)`.  `verification/cb_gram.py`
builds the Cauchy-Binet compression `K(lambda, mu)` and checks it against the direct enumeration
of the maximal minors, and checks that `Z^T Z x = e0` is solvable exactly when the pencil has no
common root.

### The open discrepancy

Take `A` = the shift, `C = e1^T`, `L0 = [-1,-1,-1]`, `q = 2`.  The instance is **feasible**: the
witness `L = [[-1,-1,-1],[0,0,1]]` satisfies the true `(5a)` and `(5b)`, verified independently by
`audit_independent.cond_5a_orig` / `cond_5b_orig`.  For that witness, `N = e3` (`k = 1`) and

    H = L e3 = [-1, 1]^T,     H_A = L A e3 = [-1, 0]^T     (both 2 x 1)

Now compare the two conditions:

| condition | value | holds? |
|---|---|---|
| `row(H_A) <= row(H)`, the compressed form of `(5a)` (here `CAN = 0`) | `k = 1`, so `row(H) = R^1` contains `row(H_A)` | yes |
| `col(H_A) <= col(H)`, which is what Claim 8 gives | `span{(-1,1)}` does not contain `span{(-1,0)}` | no |

The Lean statement of Claim 8 (`Q1Paper/PaperI/Claims38.lean:421`) is the authority for the
reading: `(exists b, M b = c) <-> (M M^T rank = (M M^T + c c^T) rank and (augment M c) rank = M
rank)`, i.e. `c` is a **column** combination of `M`'s columns.  Applying it per row of
`H B = H_A` therefore gives a **column** condition, while the paper's `(5a)` is a **row**
condition.

So Algorithm 2's item (i), as literally read, is **strictly stronger** than `(5a)` and rejects a
feasible instance.  This is not a coding slip in the front end: the front end reproduces the
chart as written.  Three readings remain possible and none is decided here: (a) Algorithm 2 has a
gap; (b) the paper's `H` is meant transposed, which would swap rows and columns; (c) in the
paper's setting `(5a)` is equivalent to the column condition, which needs `H` square or `B`
invertible -- false for the witness, where `H` is `2 x 1`.

**RETRACTED (Round 10).** The discrepancy above was **my own two implementation bugs**, not a gap
in the paper.  Both were found by running the front end against the witness:

1. `[H;G]` is **vertical** stacking -- the paper writes `[P;M]` with a semicolon for that (cf.
   Claim 1).  I had concatenated the rows pairwise, i.e. horizontally, which turns
   `e_{omega+1}([H;G][H;G]^T) = 0` into a statement about the pair-space rank instead of the
   stacked-column rank.
2. `E_0` must be the **actual rows `L0 M`**, not a normalised basis of their span.  A normalised
   basis differs by a scalar, so pinning `L[0..r0] = L0` became inconsistent with `L M = [H G]`
   and `reconstruct_L` returned `None` for every chart point.

After both fixes the front end **reproduces Algorithm 1's witness exactly**:
`L = [[-1,-1,-1],[0,0,1]]` from the chart point `t=1, J=(0,)`, with `(5a)` and `(5b)` re-verified
independently.  So Algorithm 2's item (i) is *not* stronger than `(5a)`, the row/column question
above was a red herring, and the earlier conclusion ("must not be presented as reproducing
Algorithm 1's verdicts") is **withdrawn**.

**Lesson.**  A discrepancy between a paper and an implementation should be attributed to the
implementation until both readings of the paper's own notation have been checked; here the
semicolon in `[H;G]` was decisive and the `E_0` normalisation was a second, independent slip.
## Algorithm 2: current state (Round 12)

`verification/test_fpt.py` compares the Algorithm 2 front end with `decide.py` (Algorithm 1) on
four instances and asserts the **soundness** direction only -- a `Psi` witness exists implies
`decide.py` does not say infeasible -- because the front end searches a finite grid and a miss is a
coverage statement, not a contradiction.  Every `Psi` witness is reconstructed into an `L` and
re-verified against the original `(5a)`/`(5b)` by `audit_independent`.

Result at **Round 16: 10/10 AGREE** (the earlier 4/4 was a smaller sample; the Round-13 range fix
and the Round-14 short-circuit fix then made the comparison honest).

| # | instance | decide.py | Algorithm 2 | agreement |
|---|---|---|---|---|
| 1 | shift, `C = e1`, `L0 = [-1,-1,-1]`, `q = 2` | feasible | chart witness, reconstructed and re-verified | agree |
| 2 | shift, `C = e1`, `L0 = e1`, `q = 2` | feasible | `W0 = 0` shortcut | agree |
| 3 | `A = 0`, `C = e1`, `L0 = e2`, `q = 2` | infeasible | step-6 test | agree |
| 4 | shift, `C = e3`, `L0 = e1`, `q = 2` | infeasible | step-6 test | agree |
| 5 | shift, `C = e1`, `L0 = e2`, `q = 2` | feasible | chart witness, re-verified | agree |
| 6 | `n = 4` shift, `C = e1`, `L0 = e1`, `q = 2` | feasible | `W0 = 0` shortcut | agree |
| 7 | `n = 4` shift, `C = e1`, `L0 = e1`, `q = 3` (`r = 2`) | feasible | `W0 = 0` shortcut | agree |
| 8 | `n = 4` shift, `C = e1`, `L0 = [-1,-1,-1,-1]`, `q = 2` | infeasible | step-6 test | agree |
| 9 | `n = 4` shift, `C = e4`, `L0 = e1`, `q = 2` | infeasible | step-6 test | agree |
| 10 | shift, `C = [e1; e2]`, `L0 = e1`, `q = 2` (`k = 0`) | feasible | `W0 = 0` shortcut | agree |

### Known limitations (not bugs, stated so they are not overclaimed)

1. **Reconstruction can fail on a chart point.**  On the second instance a `Psi` witness exists
   but `reconstruct_L` returns `None`: pinning `L[0..r0] = L0` is not satisfiable at that chart
   point.  Both algorithms say feasible, so this is not a contradiction; the reconstruction needs
   more freedom (or a different representative of the `E0` rows).
2. **The chart search is a grid.**  `Y` runs over `{-1, 0, 1}` only, so "no witness" is never
   turned into "infeasible".  A complete implementation needs an exact real-feasibility oracle for
   `Psi`; that is the same boundary as Algorithm 1's `unknown`.
3. **The chart grid is `{-1, 0, 1}`** and `t` runs to `min(m', r, 2 ell)` as the paper prescribes.
   "No grid witness" is never turned into "infeasible": `decide_fpt` returns `unknown`, which is
   the same boundary as Algorithm 1's `unknown`.

### What "complete" does and does not mean here

`fpt.decide_fpt` implements the paper's control flow -- the `r = 0` delegation, the `W0 <= V`
test, the `W0 = 0` shortcut, and the `(t, J, omega)` loop over `Psi` -- and it agrees with
Algorithm 1 on all ten instances tried.  It is **not** a decision procedure: the chart grid is
finite and there is no real-feasibility oracle, so an instance whose witness is not on the grid is
reported `unknown`.  Closing that requires a real-algebraic feasibility oracle, which is a
research-grade component and is not claimed.

With these caveats the front end is consistent with Algorithm 1 on every instance tried, and it
reproduces Algorithm 1's witness exactly on the first one.