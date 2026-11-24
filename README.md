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
paper/          the paper: .tex and .pdf only
                paper_I_dec            decision complexity (Paper I)
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

`Q1Paper/PaperI/Audit.lean` prints the axioms of 439 declarations; the accepted set is
exactly `propext`, `Classical.choice`, `Quot.sound` (checked by
`scripts/check_paperI_axioms.py`, which fails on anything else, including `sorryAx`).
There is no `sorry`, no `admit` and no custom axiom in the tree.

Covered by kernel-checked theorems: the compression and rank identities (Claims 1-2); the
row-pair, sandwich, W-condition, structural, monotonicity and rank-consistency statements
(Claims 3-8), including the *converse* of the sandwich (`claim4_converse`: every subspace of
the sandwich of dimension at most dim W0 + r is realised by some R); the Bezout/window chain,
the Gram certificate and the full-column-rank pencil (Claims 9-12), including the square
Cauchy-Binet expansion, and the *ingredients* of the bridge between the injective-map and the
subset-indexed minor families — the fibre count `card_fibre_imageFin` and the sign relation
`windowRow_inj_eq_sign_mul`; the aggregation step that would identify the two families' Gram
matrices is not a single Lean theorem (the paper's proof carries it, and the paper's evidence
table says the same); rational bases and annihilators with the paper's explicit constant
(Claim 13); the
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

## Scope and limitations

**The specification is the complex-λ one.** Paper I's condition (5b) quantifies over the complex
numbers, and the Lean artifact now states that specification explicitly as
`Q1Paper/PaperI/DecComplex.lean`'s `complexDEC`, with both directions of the chart equivalence proved
against it:

| direction | declaration |
|---|---|
| chart point ⇒ `complexDEC` (soundness) | `ComplexSoundness.decComplex_of_phiPoint` |
| `complexDEC` ⇒ chart point (completeness, `ω ≥ 1`) | `CompletenessB.phiPoint_of_complexDEC` |

The older `DEC` in `Interface.lean` quantifies `(5b)` over the base field, i.e. over the **real**
numbers; it is kept as an **auxiliary** definition only, linked by
`DecComplex.dec_of_complexDEC : complexDEC → DEC` (the only direction that holds — a pencil can keep
full rank at every real λ and drop at a complex one). Read `DEC` in the older module names with that
caveat in mind.

**What the Lean artifact establishes.** It kernel-checks the formalised statements covering
Claims 1–16, Theorem 5, the `r = 0` reduction of Proposition 4, and the bit-complexity results of
Claims 19 and 21. The axiom audit reports **439** checked declarations, all depending only on
`propext`, `Classical.choice` and `Quot.sound`. It also verifies **conditional** complexity bounds
for Theorems 1 and 2, relative to an abstract chart-cost specification whose instances are proved
inhabited and whose exponents are explicit. One detail worth recording: the FPT specification's
degree hypothesis is `deg ≤ 2·vars + 2`, which the paper's chart system satisfies (its degree is
`2ω` and its variable count is `2qω + 2ω ≥ ω`); relaxing it from the earlier `deg ≤ 2` cost a
factor `(ℓ+2)²` in the base and moved the constant from `8k₀+C₀+2` to `10k₀+C₀+2`, still FPT.

**What it does not establish.** It does **not** formalise

1. the equivalence between the `r > 0` chart systems and the original feasibility problem, i.e.
   the correctness of Algorithm 1 / Algorithm 2 (this is proved in the paper, on paper);
2. Renegar's real-algebraic feasibility procedure, which enters the paper as a cited result with
   an explicit cost;
3. an executable rank/feasibility solver (the repository has an interface plus a non-emptiness
   proof, not a computable implementation).

The Python programs under `verification/` implement Algorithm 1, Algorithm 2's control flow and
the `r = 0` branch; they agree with each other on 10 instances and are cross-checked with exact
arithmetic. That is **experimental evidence, not a proof of algorithmic correctness**.

So the honest claim is: *the Lean artifact machine-checks the core mathematical statements of
Paper I and a conditional complexity analysis* — not *all of Paper I's theorems and the full
algorithms*.

## Where each paper item is proved

[Q1Paper/PaperI/CLAIMS.md](Q1Paper/PaperI/CLAIMS.md) is the generated index: one row per paper item
(Claims 1-16, Proposition 4, Theorems 1/2/5, the appendix claims), with the Lean declaration
that proves it and its status ([Lean], [Lean-conditional], [Paper]).  It is generated from a
single table by `scripts/generate_paperI_claims.py`, and CI runs
`Q1Paper/PaperI/ClaimsCheck.lean` (one `#check` per item) plus the generator's `--check` mode, so
the index cannot drift from the code.
