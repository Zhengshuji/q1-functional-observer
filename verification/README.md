# Exact verification scripts

These scripts perform **finite exact checks** (rational arithmetic via `fractions`,
`sympy` where noted) of the identities used in Paper I. They are *not* proofs and do not
replace the paper arguments or the Lean kernel; each one prints the instance it checks and
asserts the basic invariants before drawing a conclusion.

**Naming.** `cNNN_<topic>.py` where `NNN` is the attempt number in the research log.

## Layout

```
ci/       the three scripts run by .github/workflows/build.yml
archive/  the remaining scripts, kept as the exact-arithmetic record
*.py      the two shared helpers (spectral_gcd.py, audit_independent.py)
```

Run a script from this directory: `python ci/cNNN_<topic>.py` (the CI scripts import
`spectral_gcd`, which is found through this directory).

## CI gates

| Script | What it checks |
|---|---|
| `ci/c317_cauchy_binet_random.py` | $K(\lambda,\mu)=\sum_{I,J}f_{IJ}(\lambda)f_{IJ}(\mu)$ and the coefficient identity (Section V) |
| `ci/c318_r0_linear_system.py` | the linear system (R0) $\iff$ the gcd test, with counts and the degree bound (Proposition 1, Appendix A) |
| `ci/c319_encoding_and_rowspace.py` | the coefficient-vector row space, the encoding witness, necessity of the data constraints (Theorem 3, Appendix A) |

## Archive (evidence, not run by CI)

| Script | What it checks |
|---|---|
| `c311_rank_consistency.py` | the rank-consistency elimination identity on random systems (Claim 8) |
| `c312_fixed_q_factor.py` | $H=XB$, $B_{:,J}=I_\omega$, $H_A=FH$ on a feasible instance (Section VI) |
| `c313_gram_indexing.py` | the shifted-index formula and $e_0\in\operatorname{row}Z$ (Claim 10) |
| `c314_G_form.py` | $G=FX$, $H_A=GB$ and the rank identity (Section V) |
| `c315_r0_left_inverse.py` | the rectangular adjugate: $SZ=I_\omega$ and $\deg S\le2\omega-2$ (Appendix A) |
| `c316_gram_certificate_random.py` | the Gram certificate on random polynomial families, with negative controls (Claim 11) |
| `c320_subspace_reduction.py` | the subspace (quotient) reduction of DEC |
| `c321_dimensional_test.py` | whether feasibility is determined by the dimensions alone under the reduction |
| `c322_opt_find.py` | OPT and FIND under the subspace reduction |
| `c323_common_projection_core.py` | the iterated common-projection core $S_*$ of the reduction |
| `c324_boundary_cases.py` | the boundary cases of the reduction |
| `c325_fer26b_example_audit.py` | audit of the illustrative example of the referenced paper |
| `c326_fer26b_order4_observer.py` | the explicit order-4 functional observer for that example |
| `c328_example_direct_dec.py` | the criteria applied directly to that order-4 observer |
| `c329_bounds_comparison.py` | comparison of the spectral lower bound with the quotient-space bound |

## Known limitation

`ci/c319`'s fourth check (a negative control on an external example) needs data that is not
bundled in this repository; it is skipped here and runs in the research repository.

## Entry point: checking a candidate observer

`verify_candidate.py` is the reusable checker for the paper's two conditions.  Given `A`, `C`
and a candidate `L = [L0; R]` it decides, in exact rational arithmetic,

* (5a) `rank[LA; L; CA; C] = rank[L; CA; C]`,
* (5b) the gcd of the `r0`-order minors of `[λL - LA; CA; C]` is a nonzero constant,

prints the shapes and the rank of `[L; CA; C]` first (asserted, so a malformed input trips an
assertion rather than yielding a confident wrong answer), and returns `DEC = (5a) and (5b)`.

```
python verify_candidate.py                  # one feasible and one infeasible example
python verify_candidate.py instance.json    # {"A": .., "C": .., "L0": .., "R": .., "expect": true}
```

It calls `cond_5a_orig` / `cond_5b_orig` from `audit_independent.py` (the independent
implementation with its own Fraction linear algebra and exact polynomial gcd), so the thin CLI
and the research script cannot silently disagree.

**What is *not* here**: a single end-to-end script that runs the whole decision algorithm
(chart enumeration, the per-chart system (R0), and a solver).  The pieces are `c318` (the
`r = 0` system and its gcd test), `c320`-`c324` (the subspace reduction) and `c319` (the
encoding); `audit_independent.py` additionally implements the decision side
(`N = ker[C; CA]`, `A' = (NᵀN)⁻¹NᵀAN`, `R0 = AN - NA'`, the invariant closure `V`, `α0`).

## The r = 0 decision procedure (an algorithm, not a check)

`decide_r0.py` is the one script here that is an **`[algorithm implementation]`** rather than an
`[exact verification]`: it takes an instance, runs the paper's reduction, and returns a verdict.

```
python decide_r0.py --demo          # one feasible and one infeasible instance
python decide_r0.py instance.json   # {"A": .., "C": .., "L0": ..}
```

What it does: N = ker[C; CA], H = L0 N, H_A = L0 A N, omega = rank H, then the two conditions

* `(5a)` `rank[H; H_A] = omega`,
* `(5b)` the pencil `lam X - G` keeps rank omega at every complex lambda,

and it decides `(5b)` through the finite rational system (R0) (unknowns `S_0 .. S_d`,
`d = 2 omega - 2`) rather than through the gcd of minors.

**Certificates in both directions** -- this is the difference from a check script:
* YES returns the actual solution `S_0 .. S_d`, which is substituted back into every equation;
* NO returns a **Farkas certificate** `y` with `y^T M = 0` and `y^T b != 0`, verified directly.
  Absence of a solution is never reported on the strength of the solver not having found one.

**Independent cross-check**: the (R0) verdict is compared against the gcd-of-maximal-minors test,
which is a separate code path (the polynomial arithmetic of `audit_independent.py`).  A
disagreement is an assertion failure, not a warning.

Everything is `fractions.Fraction`; no float takes part in any decision, and `unknown` is never
turned into `False`.

**Boundary (important).** This is the `r = 0` branch only.  The full DEC algorithm also needs the
`r > 0` branch: chart enumeration, the per-chart polynomial system, and a real-algebraic
feasibility oracle.  None of that is implemented here, and the module does not pretend
otherwise.  The witness is in the compressed form the paper itself uses (the `S` family);
reconstructing an actual observer matrix `L` from it is a further step.