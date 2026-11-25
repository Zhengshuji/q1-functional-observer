# Readability plan (working document)

The goal is that a reader who knows the mathematics can get from a paper claim to the Lean that proves
it, and can tell which declarations are the results and which are scaffolding.  The documents in
`docs/` solve "where is it"; they cannot solve "what am I looking at".  This plan changes the Lean
itself.

This file is a working note and should be deleted when the work is done.

## Phases

| phase | work | risk | status |
|---|---|---|---|
| **P0** | give the 15 `Scratch*` namespaces semantic names | medium — changes fully-qualified names, so `open` sites and `Audit.lean` move with them | in progress |
| **P1** | 8 per-section reading entries: `/-!` narrative in proof order + one `#check` per step, generated and CI-checked | low — additive only | not started |
| **P1.5** | a hierarchy per claim: base tool / bridge / core lemma / the official proof | low — metadata, no code | not started |
| **P2** | rename the ~20 claim-hosting modules (`Claim11Final.lean` → `Claim11_gram_certificate.lean`) | medium — module names change, so imports, `Audit.lean` and three generators follow | not started |
| **P3** | move modules into per-section directories | high — every module path changes | deliberately last, and **not** an acceptance criterion |

## Why P3 is not the target

Reorganising 86 flat files into seven directories does not answer the reader's actual question, which
is *why* `Claim11Final` depends on `GramCompression`.  If P0 + P1 + P1.5 make the proof route and the
statement/lemma hierarchy visible, the flat file list is a cosmetic remainder.  Conversely, a tidy
directory tree with no hierarchy inside each claim would leave the reader exactly where they started.

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
