# Start here

This repository holds Paper I and its Lean 4 formalisation side by side.  It serves two audiences,
and they should not have to learn each other's notation:

* **a reader of the paper** who wants to know which claims are machine-checked, and where;
* **a reader of the Lean** who wants to know which paper item a declaration belongs to.

`docs/PAPER_I_PROOF_MAP.md` is the bridge: one table row per paper item, giving the Lean declaration,
the file and line that define it, and its coverage status.  That table is **generated** from
`Q1Paper/PaperI/CLAIMS.md` plus the sources, so it cannot drift.

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

## The Lean

Four files have four separate jobs; knowing which is which answers most navigation questions.

| file | job |
|---|---|
| `Q1Paper/PaperI/MainTheorems.lean` | what Lean must **load** — the import entry point |
| `Q1Paper/PaperI/Claims.lean` | what the paper **claims**, in the paper's order, each with a docstring |
| `Q1Paper/PaperI/ClaimsCheck.lean` | the same items as `#check`s, machine-checked |
| `Q1Paper/PaperI/Audit.lean` | the **axiom footprint** of all 439 audited declarations |

A declaration's proof lives in whichever module it was developed in — 86 modules under
`Q1Paper/PaperI/`, with historical names
such as `Claim11Final.lean` or `GramCompression.lean`.  That is deliberate: this tree does not merge
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
* **`ω = 0`.**  The completeness theorem `CompletenessB.phiPoint_of_complexDEC` carries `1 ≤ ω`,
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

## Reading order

1. This file.
2. `docs/PAPER_I_PROOF_MAP.md` — the paper item ↔ declaration ↔ file table, and the boundaries.
3. `docs/PAPER_I_MODULE_MAP.md` — every Lean module with its declaration count, which paper items it
   hosts, and the module's own stated purpose.  Use it when you have a file name and want to know why
   it exists; use the proof map when you have a paper item and want the declaration.
4. `docs/ALGORITHM_CORRECTNESS_MAP.md` — what is and is not proved *about the algorithms*, as opposed
   to about the mathematics.
5. `Q1Paper/PaperI/CLAIMS.md` — the machine-maintained claim list (both maps are built from it).
6. The paper itself.

Development history, including retracted claims and the reasons, is recorded in the project's
development logs.  Those are **not published** in this repository: they are records, not status
reports, and gaps they describe may have been closed since.
