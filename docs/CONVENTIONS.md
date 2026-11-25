# Conventions

The rules this repository follows, written down so they do not have to be re-derived from commit
messages.  They are grouped by when they matter: what gets published, how the Lean is written, how the
generated artefacts are treated, how modules are named and renamed, how a change is verified, and how
the work is done.

## 1. What this repository publishes

This is the public artefact: the papers, the Lean formalisation, the verification programs, CI, and the
documents that help a reader.  Things that exist only to run the author's own workflow are **not
published**; they stay in the working copy and are listed in `.gitignore`:

* maintainer tooling with machine-specific paths;
* agent handoff notes;
* correspondence with reviewers or other agents;
* one-off migration scripts (after they have been run);
* development logs that record how the work was done rather than what it establishes.

`paper/` holds `.tex` and `.pdf` only.  The `.tex` is the single source of truth for the paper.

## 2. How the Lean is written

* **No `sorry`, ever.**  A statement that is not proved is not committed, and a half-finished file is
  deleted rather than left in the tree.
* **No new axioms.**  Every audited declaration must depend only on `propext`, `Classical.choice` and
  `Quot.sound`.  `scripts/check_paperI_axioms.py` enforces this against `Audit.lean`, and fails if the
  audit file and the Lean output disagree by even one declaration.
* **Every module opens with a `/-!` docstring** stating what it proves, and its first path-like line is
  the module's own path.  `scripts/check_consistency.py` verifies both.
* **A `#check` per claim.**  `Read/` entries and `ClaimsCheck.lean` name declarations by `#check`, so a
  rename breaks the build instead of silently invalidating a document.

## 3. Generated artefacts

Generated, never hand-edited: `CLAIMS.md`, `Claims.lean`, `ClaimsCheck.lean`, `MODULES.md`,
`docs/PAPER_I_PROOF_MAP.md`, `docs/PAPER_I_MODULE_MAP.md`, `Q1Paper/PaperI/Read/*`.

Each generator has a `--check` mode wired into CI, so a stale artefact fails the build rather than
misleading a reader.  Regenerate **in this order**, because later artefacts read earlier ones:

1. module docstrings (in the sources);
2. `generate_paperI_claims.py`;
3. `generate_paperI_modules.py`;
4. `paper_lean_index.py`;
5. `generate_reading_entries.py`.

## 4. Naming

* **The namespace carries the API name; the module path is independent.**  This is why renaming or
  moving a module never changes a declaration's fully-qualified name, and why `Audit.lean` never has to
  move.  It has held through every restructuring so far.
* **A directory name becomes a module name**, so it must be a valid Lean identifier: `S00_Interface`
  and not `00_Interface`, because Lean module names may not start with a digit.
* **`PaperI/` is organised by the paper's sections.**  A module's section is decided by *what it proves*,
  not by its name or a keyword match.
* **`Q1Paper/` root is the reusable project layer** and is deliberately flat: it is not a chapter of the
  paper, and 30 files do not need directories.  Its modules are still named for what they prove.

## 5. Renaming and moving

* **Measure the blast radius first.**  `scripts/rename_module.py --dry-run` reports how many files and
  references would change; a first attempt at one rename reported 125 files where the true number was 6,
  because its substitution rewrote every `import` line.
* **One group at a time, verified after each.**  A group that fails is reverted with
  `git checkout -- Q1Paper` before the next is attempted.
* **Scripts fix imports and namespaces only.**  Prose in docstrings and documents still names the old
  module, so grep the tracked tree afterwards; this has caught stale references every time.
* **Directory and module renames do not touch `Audit.lean`**; namespace renames do, and so do the claims
  table and `ClaimsCheck.lean`.

## 6. Verifying a change

Local, in this order:

```bash
lake build Q1Paper                                        # or the specific entry point
lake env lean Q1Paper/PaperI/S00_Interface/Audit.lean      # then check_paperI_axioms.py on the output
lake build Q1Paper.PaperI.Read.All
python scripts/generate_paperI_claims.py --check
python scripts/generate_paperI_modules.py --check
python scripts/paper_lean_index.py --check
python scripts/generate_reading_entries.py --check
python scripts/check_consistency.py
```

`scripts/check.sh` runs the same set.

**CI is the authority, not the local tree.**  A local pass can succeed against a stale `.olean` for a
module path that no longer exists in the sources; that has happened once, and CI was right.  After a
move or a rename, clear `Q1Paper/`'s stale build products before trusting a local result.

## 7. How the documents are organised

Each document has one job and says so where it is listed:

| document | job |
|---|---|
| `docs/START_HERE.md` | the reading entry point, and what is *not* established |
| `docs/PAPER_I_MATHEMATICAL_GUIDE.md` | the mathematics, for a reader who does not know Lean |
| `docs/PAPER_I_PROOF_MAP.md` | paper item → declaration → file:line (generated) |
| `docs/PAPER_I_MODULE_MAP.md` | module → purpose, size, paper items (generated) |
| `docs/ALGORITHM_CORRECTNESS_MAP.md` | what is and is not proved *about the algorithms* |
| `docs/READABILITY_PLAN.md` | the plan and the decisions behind the current structure |
| `Q1Paper/PaperI/Read/` | how to read each section's proof, in order |

Development logs kept locally are **not** published; if one is ever added back it must carry a
`Historical record` banner at the top, because a log that describes closed gaps reads as open ones.

## 8. How the work is done

* **Complex changes start with a plan**, and the plan is offered to a second reader (ChatGPT, which can
  read this repository) before any file moves.  Short prompts, stating the task and the constraint
  rather than the intended answer.
* **Take the reviewer's disagreement seriously.**  In this work the review twice overturned a planned
  order — it argued against making a directory tree the goal, and against facades that would put the
  reading structure and the real dependencies in different places.
* **Report failures, not just outcomes.**  Every commit here that fixed something says what was wrong,
  including the author's own mistakes, because that is what makes the next person's diagnosis shorter.
