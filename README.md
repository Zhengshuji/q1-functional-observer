# Functional observer feasibility — artifact

This repository is the artifact for the paper

> **Parameterized algorithms for functional observer feasibility**

It contains the Lean 4 formalization, the exact rational verification scripts, and the
LaTeX sources of the four papers in the series.

The paper studies the decision complexity of minimum-order functional observer design:
given $(A,C,L_0)$ and a prescribed order $q$, decide whether an observer
$L=[L_0;R]$ of order $q$ exists. It proves two parameterized upper bounds (fixed $q$;
fixed effective dimension $\kappa_{\rm obs}=r\,\mathrm{rank}[N\ AN]$), closes the
zero-free-row case with a finite rational linear system, and records membership in
$\exists\mathbb R$.

## Layout

```
paper/          the papers: .tex and .pdf only
                paper_I_dec            decision complexity (Paper I)
                paper_II_minorder      minimum order (Paper II)
                paper_III_hyperplane   the hyperplane layer (Paper III)
                paper_IV_c2            the c2 layer (Paper IV)
docs/           audit trail and handoff documents
                PAPER_I_FORMALIZATION_MAP.md   per-claim formalization status (the map)
                PAPER_I_MASTER_ROADMAP.md      the plan and its progress
                PAPER_I_MATH_AUDIT.md          independent audit, with counterexamples
                PAPER_I_CLAIM19_CRAMER.md      the Cramer re-derivation of Claim 19
                PAPER_I_REUSE_AUDIT.md         theorem-level reuse audit of external Lean code
                LEAN_MAP.md, REPLY_from_paper_agent.md
Q1Paper/        Lean sources
                Q1Paper/            the project layer (row spaces, projections, rank identities)
                Q1Paper/PaperI/     the Paper I modules (40 files), plus Audit.lean
                AGENTS.md           handoff notes (environment, pitfalls, API index)
scripts/        check.sh, check_paperI_axioms.py, promote_paperI.py
verification/   exact rational checks; see verification/README.md for the index
.github/        CI: a Lean job, a paper job, a verification job
```

## Build

Lean (`elan` required; Mathlib is pinned by `lake-manifest.json`):

```text
lake exe cache get
lake build
lake build Q1Paper.PaperI.MainTheorems     # the Paper I entry point
lake env lean PaperI.lean
lake env lean Q1Paper/PaperI/Audit.lean    # per-declaration axiom audit
bash scripts/check.sh
```

Papers (`pdflatex`, two passes, or `latexmk -pdf`):

```text
cd paper && pdflatex paper_I_dec.tex && pdflatex paper_I_dec.tex
```

## What is kernel-checked

`Q1Paper/PaperI/Audit.lean` prints the axioms of 412 declarations; the accepted set is
exactly `propext`, `Classical.choice`, `Quot.sound` (checked by
`scripts/check_paperI_axioms.py`, which fails on anything else, including `sorryAx`).
There is no `sorry`, no `admit` and no custom axiom in the tree.

Covered by kernel-checked theorems: the compression and rank identities (Claims 1-2); the
row-pair, sandwich, W-condition, structural, monotonicity and rank-consistency statements
(Claims 3-8), including the *converse* of the sandwich (`claim4_converse`: every subspace of
the sandwich of dimension at most dim W0 + r is realised by some R); the Bezout/window chain,
the Gram certificate and the full-column-rank pencil (Claims 9-12), including the square
Cauchy-Binet expansion and the bridge between the injective-map and subset-indexed minor
families; rational bases and annihilators with the paper's explicit constant (Claim 13); the
intersection V = T cap (S x S) as the image of the equalizer, the chart bases and E_Q (Claim 14);
a bounded rational Bezout certificate that closes the (i) <=> (ii) <=> (iii) => (iv) chain with
the degree bound (Claim 16); the rank factorization with explicit left and right inverses; the
existential-real encoding of Theorem 5 in both directions with NO abstract hypothesis (the
kernel basis is constructed); and the complexity layer: the Bareiss tableau identity, the exact
integer division cost, the total bit cost O(n^15 L^2) (with the paper's O(n^21 L^2) as a
corollary), the chart count, and a *biting* conditional form of Theorem 1.

**Not formalized, and explicitly marked paper-level in `docs/`:** the algorithmic and
complexity assertions *as unconditional statements* -- that the objects are computed within a
stated number of bit operations (Claims 13-15, Theorems 1-2, Proposition 4, Corollaries 3 and 6).
The Lean statements are the mathematical specifications together with the explicit bit-length
and cost bounds; Theorem 1 is a *conditional* theorem whose only external input is an explicitly
declared real-algebraic backend (`ChartSpecFixedDeg`, whose non-emptiness is proved). The FPT
bound of Theorem 2 has its Renegar-free core (the dimension relations and the Grassmannian chart
count `sum_t C(m',t) = 2^m' <= 4^ell`) formalised; the remaining layers are in progress.
`docs/PAPER_I_FORMALIZATION_MAP.md` is the single source of truth for per-claim status.

## Status labels

`[Lean]` = kernel-checked; `[Lean-conditional]` = kernel-checked under explicitly listed
hypotheses; `[Paper proof]` = a mathematical argument or a complexity claim that is not
formalized.

## Where each paper item is proved

[Q1Paper/PaperI/CLAIMS.md](Q1Paper/PaperI/CLAIMS.md) is the generated index: one row per paper item
(Claims 1-16, Proposition 4, Theorems 1/2/5, the appendix claims), with the Lean declaration
that proves it and its status ([Lean], [Lean-conditional], [Paper]).  It is generated from a
single table by `scripts/generate_paperI_claims.py`, and CI runs
`Q1Paper/PaperI/ClaimsCheck.lean` (one `#check` per item) plus the generator's `--check` mode, so
the index cannot drift from the code.
