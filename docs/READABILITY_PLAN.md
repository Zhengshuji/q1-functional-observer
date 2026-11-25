# Readability plan (working document)

The goal is that a reader who knows the mathematics can get from a paper claim to the Lean that proves
it, and can tell which declarations are the results and which are scaffolding.  The documents in
`docs/` solve "where is it"; they cannot solve "what am I looking at".  This plan changes the Lean
itself.

This file is a working note and should be deleted when the work is done.

## Phases

| phase | work | risk | status |
|---|---|---|---|
| **P0** | give the 15 `Scratch*` namespaces semantic names | medium — changes fully-qualified names, so `open` sites and `Audit.lean` move with them | done |
| **P1** | 8 per-section reading entries: `/-!` narrative in proof order + one `#check` per step, generated and CI-checked | low — additive only | done |
| **P1.5** | a hierarchy per claim: base tool / bridge / core lemma / the official proof | low — metadata, no code | done |
| **P2** | rename 16 claim-hosting modules in 5 groups | medium — module names change, so imports and the generators follow; the audit does not, because declaration names are namespace-qualified | done |
| **P3** | move modules into per-section directories | high — 221 import lines | done — 86 modules in 9 sections |

## P3: executed, and how the classification was made

The phase is done.  Its prerequisite was a classification pass, and that is what happened: all 86
modules under `Q1Paper/PaperI/` were assigned from **their own stated purpose**, read one at a time.

A keyword classifier was tried first and rejected: run over the module table it put 39 of the 86 into a
single bucket, because declaration names contain words like `gram` and `minor`.  That is the misfiling
failure this plan warned about, caught before any file was moved.

    S00_Interface 5   S01_Compression 2   S02_Subspace 10   S03_Certificate 22
    S04_Rationality 13   S05_Complexity 10   S06_Algorithms 9   S07_ExistsReal 4
    S08_ChartEquivalence 12

`S08_ChartEquivalence` is not a section of the paper: it holds the chart / Phi / DEC development that
connects the certificate to the algorithm.  It exists because `S03_Certificate` had grown to 39 members,
and that overflow was the signal that two topics were being mixed.

Three things had to change with the move, each found by building rather than by reasoning:

* the directories are `S00_…` rather than `00_…`: a Lean module name may not start with a digit, so
  `lake build Q1Paper.PaperI.00_Interface.MainTheorems` fails with `unknown target`;
* 72 module docstrings open with their own path, which had to be rewritten;
* the audit path in CI and `check.sh` moved to `S00_Interface/Audit.lean`.

What did **not** change: any declaration name, and therefore `Audit.lean`'s 439 entries.  Module paths
and namespace qualification are independent — the property that also made P0 and P2 safe.

`Q1Paper/*.lean` (the 31-module project layer) stays flat on purpose: it is not the paper's
formalisation.

## P0: semantic namespaces, not filename mirrors

15 modules under `Q1Paper/PaperI/` carry a namespace that begins `Q1Paper.Scratch…` — an artefact of
how they were promoted from scratch files.  Their *file* names are already semantic
(`Soundness.lean`, `DecComplex.lean`, `ChartComplete.lean`, …), so the namespace should carry the same
name, not merely lose the `Scratch` prefix:

    Q1Paper.ScratchSoundness  ->  Q1Paper.PaperI.Soundness

Namespace and module path then agree for these files, which is also what most of the older modules do
in spirit (`Q1Paper.PaperI.claim11_iff_gram` lives in a module of the same tree).  The alternative —
flattening everything into `Q1Paper.PaperI` — was rejected: it risks collisions with existing names for
no gain in structure.

Blast radius, measured before starting: 15 module headers, 23 files that `open` or reference one of the
namespaces, 38 lines in `Audit.lean`.  All are textual and all are caught by the build and the audit.

## P1: what the reading entries must not be

`Claims.lean`, `ClaimsCheck.lean`, `PAPER_I_PROOF_MAP.md` and `PAPER_I_MODULE_MAP.md` already index the
paper's items.  A new set of files that repeats those indexes would be noise.  Each reading entry must
add what none of them has:

1. the mathematical problem that section solves;
2. the objects and prior results it consumes;
3. the key steps **in proof order**;
4. for each step, the declaration and its `#check`;
5. what the next section does with this one's result.

The `#check` lines are what keep it honest: rename a declaration and the entry stops compiling.

## P1.5: the hierarchy that answers "what am I looking at"

For each claim, record which declarations are:

* a **base tool** (general linear algebra, not about this problem);
* a **bridge** (translates one formulation into another);
* a **core lemma** (mathematical content specific to this claim);
* the **official proof** of the paper's statement.

This is metadata, so it costs no code, and it is the part a reader benefits from most.

## Acceptance

* every claim in the paper can be reached from a per-section entry, in proof order;
* for each claim it is visible which declaration is the result and which are scaffolding;
* no phase may be declared done without a full build, the axiom audit, and the three generated-index
  checks passing.
