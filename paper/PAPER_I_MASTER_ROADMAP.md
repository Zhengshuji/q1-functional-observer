# Paper I Master Roadmap

> 只管理任务与状态，不重复数学证明。逐项对照见 `PAPER_I_FORMALIZATION_MAP.md`。

## 1. Scope and deliverables

Four independent quality lines (none replaces another):

- **A. Mathematical completeness** — every main claim has a proof whose hypotheses are used and whose edge cases are checked.
- **B. Lean formalization completeness** — the selected scope is formalized with no `sorry`/`admit`/custom axioms, and paper objects are bridged to Lean objects.
- **C. Algorithm and complexity completeness** — arithmetic vs bit complexity separated; denominator clearing, determinant bounds, Bareiss intermediates, and the final bit bound proved.
- **D. Paper and engineering completeness** — every claim traceable to a proof; paper ↔ Lean two-way index; CI + axiom audit + reproducible build.

States are kept separate: `Mathematisch proved` (M) and `Lean formalized` (F); never merged into a single "complete".

## 2. Completed work (as of commit 367ad9d)

- Claims 1, 2, 9, 10, 11, 12 formalized in Lean (Claim 11 via `claim11_iff_gram`, Claim 12 via `claim12_iff_gram`).
- Section III-D algebraic chain: square Cauchy–Binet (ported, Apache-2.0) → `gramKernelEval` double expansion → coefficient identity → window Gram entry identity → `windowGram_eq_compressed`.
- Axiom audit: 110 declarations, only `propext`, `Classical.choice`, `Quot.sound`.

## 3. Open mathematical proofs

- Claim 13 (rational bases / bit lengths), Claim 14 (chart data), Claim 15 (coefficient bit lengths), Claim 16 (five conditions), Proposition 4 (`r = 0` algorithm), Theorems 1–2 complexity, Theorem 5 (∃ℝ encoding).

## 4. Open Lean formalizations

- **D1 bridge**: subset-indexed vs injective-map-indexed minor families (sign relation, row-space equality, Gram scaling `(ω!)²`, certificate equivalence).
- §III-D end-to-end assembly at the pencil.
- Everything in §3.

## 5. Complexity and bit-length

- `bitLen` foundation (in progress, subagent).
- Denominator clearing via `Matrix.num`/`Matrix.den`.
- Determinant bound: `Matrix.det_le` (Leibniz, `n!` factor) first; Hadamard only if needed.
- Bareiss: meta-level only in Mathlib; intermediate/ minor relation is new mathematics.

## 6. Paper-to-Lean correspondence

- Maintained in `PAPER_I_FORMALIZATION_MAP.md` (§4 per-claim, §7 audit findings).
- Known deviation: D1 (bridge missing) — tracked as the top Lean obligation.

## 7. Parallel workstreams

| Stream | Owner | Status |
|---|---|---|
| A. D1 bridge + §III-D assembly | main line | in progress |
| B. Claim 13 bit-length base | subagent `bitlen-base` | in progress |
| C. Paper I mathematical audit | subagent `math-audit` | in progress |
| D. Lean coverage audit | pending | not started |
| E. Algorithm/complexity audit (`r=0`, ∃ℝ) | pending | not started |
| F. Paper/engineering integration | main line | continuous |

## 8. Dependencies and integration gates

- Gate 1: D1 bridge complete before §III-D is declared integrated.
- Gate 2: Claim 13 scalar bit-length base compiles before the determinant bound.
- Gate 3: mathematical audit findings triaged before any "complete" label is applied to Claims 13–16.

## 9. Known risks and counterexamples

- D1: the Lean certificate matrix is `(ω!)²` times the paper's `Z_Q`; the equivalences survive but the literal object differs until the bridge is proved.
- Paper §III-D: `rem:algo` says `J ⊆ [k]` while the definition uses `J ⊆ [ℓ]` (mathematically equivalent because complement columns give zero determinants; wording to fix).
- Hadamard inequality absent from Mathlib; Bareiss only a tactic.

## 10. Final acceptance criteria

- No `sorry`/`admit`/custom axioms in the Paper I closure.
- `lake build Q1Paper`, `lake env lean PaperI.lean`, both audits, and CI green.
- Each paper claim carries an explicit status in the map, with any deviation from the Lean objects described.
- Bit-complexity claims backed by explicit lemmas, not by the paper's prose.
