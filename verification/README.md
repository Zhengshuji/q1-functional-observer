# Exact verification scripts

These scripts perform **finite exact checks** (rational arithmetic via `fractions`,
`sympy` where noted) of the identities used in Paper I. They are *not* proofs and do not
replace the paper arguments or the Lean kernel; each one prints the instance it checks and
asserts the basic invariants before drawing a conclusion.

**Naming.** `cNNN_<topic>.py` where `NNN` is the attempt number in the research log.

## Layout

```
ci/       the three scripts run by .github/workflows/build.yml
*.py      the shared helpers (spectral_gcd.py, audit_independent.py) and the programs below
```

The research log's numbered experiments (`cNNN_*.py`) are **not published** here; they are kept in the
author's working copy as the exact-arithmetic record.  What is published is the set of programs that
correspond to the paper's algorithms, plus the tests and the two CI scripts.

Run a script from this directory: `python ci/cNNN_<topic>.py` (the CI scripts import
`spectral_gcd`, which is found through this directory).

## CI gates

| Script | What it checks |
|---|---|
| `ci/c317_cauchy_binet_random.py` | $K(\lambda,\mu)=\sum_{I,J}f_{IJ}(\lambda)f_{IJ}(\mu)$ and the coefficient identity (Section V) |
| `ci/c318_r0_linear_system.py` | the linear system (R0) $\iff$ the gcd test, with counts and the degree bound (Proposition 1, Appendix A) |
| `ci/c319_encoding_and_rowspace.py` | the coefficient-vector row space, the encoding witness, necessity of the data constraints (Theorem 3, Appendix A) |

## Known limitation

`ci/c319`'s fourth check (a negative control on an external example) needs data that is not
bundled in this repository; it is skipped here and runs in the research repository.

## Entry point: checking a candidate observer

`verify_candidate.py` is the reusable checker for the paper's two conditions.  Given `A`, `C`
and a candidate `L = [L0; R]` it decides, in exact rational arithmetic,

* (5a) `rank[LA; L; CA; C] = rank[L; CA; C]`,
* (5b) the gcd of the `r0`-order minors of `[位L - LA; CA; C]` is a nonzero constant,

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
(`N = ker[C; CA]`, `A' = (N岬€N)鈦宦筃岬€AN`, `R0 = AN - NA'`, the invariant closure `V`, `伪0`).

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
## Terminology: paper, Python, Lean

The three layers name the same objects differently, and a reader moving between them has to translate
twice.  This table is the translation.  It is the one place where the Python and the Lean are compared
side by side.

| paper | Python | Lean |
|---|---|---|
| $\mathrm{DEC}(q)$, conditions (5a) and (5b) over the reals | `decide(A, C, L0, q)` in decide.py | Q1Paper.PaperI.DEC (S00_Interface/Interface.lean) |
| (5b) over $\mathbb{C}$ -- the paper's own condition | the same decide, since the Python tests the complex pencil | Q1Paper.PaperI.DecComplex.complexDEC |
| the raw algebraic condition, $\operatorname{rank}[LA;L;CA;C]=\operatorname{rank}[L;CA;C]$ | A, C, L used directly | Q1Paper.PaperI.rawAlgebraic |
| a chart system $\Phi_{\omega,J}$ of eq:phi | the per-chart system in decide.py | Q1Paper.PaperI.ChartComplete.PhiPoint |
| the Gram certificate ^{\mathsf T} Z x = e_0$ | cb_gram.py, gram in decide.py | Q1Paper.PaperI.GramSystem.gram_certificate |
| the  = 0$ system (R0) | decide_r0.py | Q1Paper.prop4_r0_iff_spectral (S06_Algorithms/Prop4.lean) |

Two cautions this table makes visible:

* DEC and complexDEC are **not** the same proposition.  The Python decides the complex condition,
  which is the paper's; the Lean DEC quantifies over the reals and is retained only as an auxiliary
  definition (complexDEC → DEC, and the converse fails).  Reading "the Python agrees with DEC" is
  therefore a stronger statement than it looks.
* unknown in the Python is an abstention, never False; there is no Lean counterpart, because the Lean
  formalisation does not include an executable solver.
