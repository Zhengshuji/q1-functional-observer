# Paper V — the free-row fibre: reading guide

Paper V is `paper/paper_V_fibre.tex` (PDF alongside).  This guide says what the paper
proves, which part of it is machine-checked, and where every claim can be verified.

## What the paper is about

Fix the compressed row space `U` of a functional-observer candidate and let the free rows
vary.  The admissible values of `H_A` form the **fibre**, and the paper asks when every
point of the fibre fails the spectral condition `(5b)`.

The paper proves three things about that question:

1. **The fibre is an affine space** (Theorem 1): it is empty or a coset of `T ⊓ U`, of
   dimension `q·a` with `a = dim(U ∩ T)`, and it is nonempty exactly when
   `U Z'' ⊆ U + T`.
2. **On the fibre the spectral condition is a degree condition** (Theorem 4): some point
   of the fibre satisfies `(5b)` exactly when the gcd of the `d'`-minors of
   `λ H - H Z'' - G'`, taken over the fibre's function field, has degree zero.  The only
   non-trivial step is that a positive-degree divisor with constant `λ`-leading
   coefficient survives every specialisation (Lemma 2).
3. **Failure of the whole fibre is a fixed spectral factor** when `q > d'`
   (Theorem 11): the common divisor does not depend on the fibre parameters.  Hence the
   bad set is closed (Theorem 12), the feasible set is relatively open, and infeasibility
   is exactly the containment of the compatibility stratum in the bad set (Theorem 13).

Section V turns this into procedures: a one-sided randomised decision procedure on the
region where compatibility is automatic (Theorem 15), and an enumeration for `t = 1`
(Theorem 16).  Section VI lists what is open — in particular the thin stratum where
compatibility is a genuine constraint.

## What is machine-checked

| Paper item | Lean declaration | File |
|---|---|---|
| Theorem 1 (fibre as a coset; nonemptiness) | `Q1Paper.PaperV.fibre`, `mem_fibre`, `fibre_nonempty_iff`, `fibre_eq_coset`, `fibre_prod_nonempty_iff` | `Q1Paper/PaperV/Fibre.lean` (the assembled `q`-fold product and its dimension `q·a` are paper) |
| Theorem 4's leading-coefficient step | `coeff_det_smul_sub_X`, `coeff_det_smul_sub_X_ne_zero` | `Q1Paper/PaperV/LeadingCoeff.lean` |
| Lemma 2 (specialisation) | `natDegree_map_eval_of_leadingCoeff_const`, `map_dvd_of_dvd` | `Q1Paper/PaperV/Specialize.lean` |
| Corollary 8 (shape) | `specialized_common_factor` | `Q1Paper/PaperV/Specialize.lean` |

The axiom audit is `Q1Paper/PaperV/Audit.lean` (11 declarations, all on
`propext`, `Classical.choice`, `Quot.sound`); `scripts/check.sh` runs it.  The claims
table is `Q1Paper/PaperV/Claims.lean` and its machine check is
`Q1Paper/PaperV/ClaimsCheck.lean` (the same eleven declarations).

## What is *not* machine-checked, and why

* **Theorem 4's gcd criterion** — a statement about gcds of matrix minors over `K(t)[λ]`;
  the formalisation needs multivariate polynomial gcds and matrix minors at once.  The
  paper proof is complete and its only hard step (Lemma 2) *is* checked.
* **Theorem 11 (fixed spectral factor)** — an incidence-variety dimension count.
* **Theorem 12 (closedness of the bad set)** — quantifier elimination over the
  coefficient space of the coefficient test.
* **Theorems 15 and 16** — a probabilistic argument (Schwartz–Zippel) and an enumeration.

`Q1Paper/PaperV/MainTheorems.lean` records this split; `Q1Paper/PaperV/Claims.lean` says it
item by item.  Nothing is silently omitted.

## What is certified exactly

`verification/fibre.py` decides the three examples of §V in exact rational arithmetic:
the feasible fibre (gcd 1), the bad point (gcd `λ + 3`, parameter independent), and the
thin-region instance.  It asserts the ranks and the nonemptiness of the fibre *before*
deciding, so a wrong model fails loudly.  `verification/ci/c773_paperV_fibre.py` runs it in
CI.

## How to read the paper alongside the artifact

1. §II (the fibre) — read with `Fibre.lean` open; every step of Theorem 1 is a named
   declaration.
2. §III (the criterion) — Lemma 2 is `Specialize.lean`; the rest of the criterion is the
   paper's argument.
3. §IV (the bad set) — the paper's Theorem 11 is the structural heart; the coefficient test
   behind Theorem 12 is `verification/fibre.py`'s `inner_deg`.
4. §V (examples) — run `python verification/fibre.py`.
