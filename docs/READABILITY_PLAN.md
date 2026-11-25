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
| **P2** | rename 16 claim-hosting modules in 5 groups (`Claim11Final.lean` → `Claim11_MinorsGram.lean`, …) | medium — module names change, so imports and the generators follow; the audit does not, because declaration names are namespace-qualified | done |
| **P3** | move modules into per-section directories | high — 221 import lines | **not executed**; see the section below |

## P3: measured, and deliberately not executed

The original objective named P0 through P3, so this records why P3 stops here rather than leaving it
silently undone.

**Cost, measured.**  Moving the 86 modules of `Q1Paper/PaperI/` into per-section directories rewrites
**221 `import` lines across 87 files**, plus the directory list in `generate_paperI_modules.py`.  The
axiom audit is *not* affected — declaration names are qualified by namespace, not by module path, which
is the same property that made P2's renames safe.  The mechanical cost is real but containable.

**The blocking problem is classification, not cost.**  A section assignment has to be defensible for all
86 modules.  Only 20 host a paper item, and those are the easy ones; the other 66 are supporting modules
whose home is a judgement call — `Hadamard.lean`, `DesnanotJacobi.lean`, `FibreCard.lean`,
`DenOne.lean`.  Assigning them by filename prefix would misfile some, and a mis-filed module is worse
than a flat one: it tells the reader something false about why the module exists.

**What would make P3 worth doing.**  A per-module reading pass deciding each of the 66 by what it
actually proves, not by its name — several rounds with a real misfiling risk, in exchange for a
directory tree.  Against that: after P0-P2 the file names are already semantic, and P1/P1.5 give the
proof order and the statement hierarchy, which is the part that was actually missing.

**Decision.**  P3 is not executed.  The `Read/` entries remain the answer to "where do I start", and
`PAPER_I_MODULE_MAP.md` remains the answer to "why does this file exist".  If P3 is ever wanted, its
prerequisite is the classification pass above, not a script.

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
