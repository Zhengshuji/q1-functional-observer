# Start here

This repository holds Paper I, Paper II and their Lean 4 formalisations side by side.  It serves two audiences,
and they should not have to learn each other's notation:

* **a reader of the paper** who wants to know which claims are machine-checked, and where;
* **a reader of the Lean** who wants to know which paper item a declaration belongs to.

`docs/PAPER_I_PROOF_MAP.md` is the bridge: one table row per paper item, giving the Lean declaration,
the file and line that define it, and its coverage status.  That table is **generated** from
`Q1Paper/PaperI/S00_Interface/CLAIMS.md` plus the sources, so it cannot drift.

## The paper

`paper/paper_I_dec.tex` (and the compiled `paper/paper_I_dec.pdf`).  The `.tex` is the only source of
truth for the mathematics; there is no parallel Markdown version.

Its structure, which the proof map follows:

| section | subject | paper items |
|---|---|---|
| §2 | preliminaries: the observer conditions (5a)/(5b) | — |
| §3.1 | compression and the pencil criterion | Claims 1, 2 |
| §3.2 | the space of attainable row pairs | Claims 3, 4 |
| §3.3 | the subspace reduction | Claims 5–8 |
| §3.4 | the finite certificate | Claims 9–12 |
| §4.1 | fixed order | Claims 13–15, Proposition 4, Theorem 1 |
| §4.2 | fixed parameter | Theorem 2 |
| §4.3 | the zero-free-row case | Claim 16 |
| §4.4 | membership in the existential theory of the reals | Theorem 5 |
| appendix | explicit size bounds | Claims 19, 21 |

## Paper II

`paper/paper_II_minorder.tex` (minimum order and construction) has its own Lean
tree `Q1Paper/PaperII/` with the same shape as Paper I:

| file | job |
|---|---|
| `MainTheorems.lean` | entry point: what Lean must load |
| `Claims.lean` | the paper's items, in the paper's order (narrative) |
| `ClaimsCheck.lean` | machine-checked index: one `#check` per item |
| `CLAIMS.md` | the same table for readers who do not know Lean (generated) |
| `MODULES.md` | the module index: which file proves what (generated) |
| `Audit.lean` | the axiom footprint of every audited declaration (106) |
| `Read/All.lean` | the reading entry: the paper's order, one `#check` per step |

The section-by-section reading order is `Q1Paper/PaperII/Read/` (`S01_Standing`,
`S02_Sandwich`, `S03_MinOrder`, `S04_LowerBound`, `S05_Tightness`,
`S06_RealDesigns`), mirroring Paper I's `Read/`.  The item map is
`docs/PAPER_II_PROOF_MAP.md`, the module map `docs/PAPER_II_MODULE_MAP.md`.

Paper II reuses Paper I's Claims 4–6 through the column split `Φ`
(`Q1Paper/PaperII/Interface.lean`) between the row(`[N AN]`) encoding and the
pair encoding `row[L N  L A N]`.

## The Lean

Four files have four separate jobs; knowing which is which answers most navigation questions.

| file | job |
|---|---|
| `Q1Paper/PaperI/MainTheorems.lean` | what Lean must **load** — the import entry point |
| `Q1Paper/PaperI/S00_Interface/Claims.lean` | what the paper **claims**, in the paper's order, each with a docstring |
| `Q1Paper/PaperI/S00_Interface/ClaimsCheck.lean` | the same items as `#check`s, machine-checked |
| `Q1Paper/PaperI/Audit.lean` | the **axiom footprint** of all 439 audited declarations |

A declaration's proof lives in whichever module it was developed in — 86 modules under
`Q1Paper/PaperI/`, with historical names
such as `Claim11_MinorsGram.lean` or `GramCompression.lean`.  That is deliberate: this tree does not merge
or rename proof modules, because doing so would touch `Audit.lean`'s fully-qualified names and the
generated indexes, for no mathematical gain.  **Use the proof map to locate a proof; do not expect
the file names to spell out the paper's structure.**

## Checking it yourself

```bash
# 1. the mathematics compiles
cd Q1Paper && lake build Q1Paper.PaperI.MainTheorems

# 2. the claim index matches the sources
python scripts/paper_lean_index.py --check

# 3. every audited declaration uses only the allowed axioms
lake env lean Q1Paper/PaperI/Audit.lean > /tmp/audit.log
python scripts/check_paperI_axioms.py /tmp/audit.log Q1Paper/PaperI/Audit.lean
```

CI runs all of the above plus the LaTeX builds for both papers.

## What is *not* established

The formalisation is not a machine-checked copy of the paper, and the difference matters:

* **Specification.**  Paper I's condition (5b) is complex-λ.  `Q1Paper/PaperI/DecComplex.lean`'s
  `complexDEC` is that specification, and both directions of the chart equivalence are proved against
  it.  The older `DEC` quantifies over the real numbers and is now **auxiliary only**;
  `DecComplex.dec_of_complexDEC : complexDEC → DEC` is the only direction that holds.
* **`ω = 0`.**  The completeness theorem `ComplexCompleteness.phiPoint_of_complexDEC` carries `1 ≤ ω`,
  because the Gram certificate comes from `claim11_iff_gram`, which needs it.  The zero-rank branch is
  a separate case in the paper (Proposition 4 step 2, and `decide_r0` in the Python layer) and is not
  covered by that theorem.
* **The real-algebraic backend.**  `RenegarBackend` is a structure carrying a cost bound; it has no
  correctness field.  Renegar's algorithm is cited, not formalised, so Theorems 1 and 2 are
  **conditional**.  Anything that calls this "verified Algorithm 1" is overstating it.
* **The executable layer.**  `verification/` holds a Python model of the algorithms and a
  differential test on small instances.  That is experimental evidence, not verification, and it is
  labelled as such in `verification/README.md`.
* **Rank-consistency (item (ii) of `eq:phi`).**  Carried by the row inclusion, which
  `claim8_rank_consistency` identifies with the linear system — not stated as a separate structure
  field.  See `docs/ALGORITHM_CORRECTNESS_MAP.md`.

* **Paper II's remaining gaps.** The Paper II tree proves its items for complex free
  blocks and, for the paper's real-design specification `DECℂ`, the forward
  direction, monotonicity, saturation and the minimum-order equivalence (via the
  real-compression lemma `real_compress`).  Prop 3 is proved in both directions.
  What is *not* formalised is listed in `docs/PAPER_II_PROOF_MAP.md` (interface
  counting, OPT/FIND corollaries, the appendix instance).

## Reading order

1. This file.
2. `Q1Paper/PaperI/S00_Interface/Claims.lean` — the paper's items in the paper's order, each with its LaTeX label,
   its status and the name of the declaration that proves it.  It contains no proofs, so it reads as a
   checklist; this is the shortest path from the paper into the Lean.
3. `docs/PAPER_I_PROOF_MAP.md` — the same items with the **module and line** that define each
   declaration, plus the proof routes and the boundaries.
4. `docs/PAPER_I_MODULE_MAP.md` — every Lean module with its declaration count, which paper items it
   hosts, and the module's own stated purpose.  Use it when you have a file name and want to know why
   it exists.
5. `docs/PAPER_I_MATHEMATICAL_GUIDE.md` — the mathematics, for a reader who does not know Lean: what the
   paper proves and why each step needs the next.  It complements the paper rather than restating it.
6. `docs/ALGORITHM_CORRECTNESS_MAP.md` — what is and is not proved *about the algorithms*, as opposed
   to about the mathematics.
7. docs/CONVENTIONS.md — the rules the repository follows: what is published, how the Lean is
   written, how generated artefacts are regenerated, how modules are named and renamed, and how a
   change is verified.
8. The paper itself.
9. `docs/PAPER_II_PROOF_MAP.md` and `docs/PAPER_II_MODULE_MAP.md` — Paper II's item map and module map, in the same layout as the Paper I maps.

Development history, including retracted claims and the reasons, is recorded in the project's
development logs.  Those are **not published** in this repository: they are records, not status
reports, and gaps they describe may have been closed since.
