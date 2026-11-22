# Paper I Master Roadmap

> 只管理任务与状态，不重复数学证明。逐项对照见 `PAPER_I_FORMALIZATION_MAP.md`；数学审计见 `PAPER_I_MATH_AUDIT.md`。
> 最后同步：commit `80eac0a`（BitLen 进主线）。

## 1. Scope and deliverables

Four independent quality lines (none replaces another):

- **A. Mathematical completeness** — every main claim has a proof whose hypotheses are used and whose edge cases are checked.
- **B. Lean formalization completeness** — the selected scope is formalized with no `sorry`/`admit`/custom axioms, and paper objects are bridged to Lean objects.
- **C. Algorithm and complexity completeness** — arithmetic vs bit complexity separated; denominator clearing, determinant bounds, Bareiss intermediates, and the final bit bound proved.
- **D. Paper and engineering completeness** — every claim traceable to a proof; paper ↔ Lean two-way index; CI + axiom audit + reproducible build.

States are kept separate: `Mathematically proved` (M) and `Lean formalized` (F); never merged.

## 2. Completed work

- Claims 1, 2, 9, 10, 11, 12 formalized in Lean (Claim 11 via `claim11_iff_gram`, Claim 12 via `claim12_iff_gram`).
- Section III-D algebraic chain: square Cauchy–Binet (ported, Apache-2.0) → `gramKernelEval` double expansion → coefficient identity → window Gram entry identity → `windowGram_eq_compressed` (commits `1bf3167`, `9577ed3`, `4c9811f`, `8106a64`).
- D1 first identity: `det_submatrix_perm` (commit `d24b8ac`).
- Independent mathematical audit of Paper I, five primary findings (commit `5963a27`);
  see `PAPER_I_MATH_AUDIT.md`.
- Claim 13 bit-length base, 43 declarations (commit `80eac0a`): `bitLenInt`,
  `bitLenRat`, `bitLenMat`, cleared-entry identity `|A.num i j| = A.den * |A i j|`.
- Axiom audit: 121 declarations, only `propext`, `Classical.choice`, `Quot.sound`.

## 3. Open mathematical proofs

- **P0 (paper correctness):** Eq. (1) universal bound is false — keep only `q_min ≤ n₀−p`;
  Algorithm 1 needs the `q < r₀` guard; Theorem 1 must be restricted to `r₀ ≤ q ≤ n` and
  stated as `DEC_q ∈ P` (XP in q).
- **P0 (Claim 19):** re-derive the constant chain with `F H = H_A` and Cramer
  (the current proof uses `(HᵀH)⁻¹`, which requires `ω = k`).
- Claim 14, 15, 16, Proposition 4, Theorems 1–2 complexity, Theorem 5 (∃ℝ encoding).

## 4. Open Lean formalizations

- **D1 bridge** (in order): `rowEmb_permOfInjective` → `maximalMinor_injective_eq_signed_subset`
  → `minorCoeff_injective_eq_signed_subset` → `windowRow_injective_eq_signed_subset`
  → `windowSet_minorFamily_eq` → `rowSpace_windowMatrix_eq`
  → `windowGram_injective_eq_factorial_smul` → `exists_gram_certificate_iff`.
- §III-D end-to-end assembly at the pencil.
- Claim 13: `bitLenRat_add`, Leibniz determinant bound, Bareiss intermediate/subminor relation,
  total bit complexity.

## 5. Complexity and bit-length

- `bitLen` foundation: **done** (commit `80eac0a`).
- Denominator clearing: `Matrix.num`/`Matrix.den`, exact identity; **done**.
- Determinant bound: `Matrix.det_le` (Leibniz, `n!` factor) first; Hadamard only if needed.
- Bareiss: meta-level only in Mathlib; intermediate/subminor relation is new mathematics.
- Input-length convention: `bitLenMat A ≤ L_input` needs an explicit input-encoding definition
  (open; must include numerators, denominators and dimensions).

## 6. Paper-to-Lean correspondence

- Maintained in `PAPER_I_FORMALIZATION_MAP.md` (§4 per-claim, §7 audit findings).
- Known deviation: D1 (bridge missing) — top Lean obligation.

## 7. Parallel workstreams

| Stream | Owner | Status |
|---|---|---|
| A. D1 bridge + §III-D assembly | main line | in progress (`det_submatrix_perm` done) |
| B. Paper corrections (Eq. (1), Algorithm 1, Theorem 1/2, §III-D [ℓ]) | paper agent / main line | in progress |
| C. Claim 19 Cramer re-derivation | math agent | to launch |
| D. Claim 13 bit length (`bitLenRat_add`, Leibniz) | Lean agent | to launch |
| E. Bareiss intermediates | algorithm agent | to launch |
| F. Roadmap / map / audit consistency | main line | continuous |

## 8. Dependencies and integration gates

- Gate 1: D1 bridge complete before §III-D is declared integrated.
- Gate 2: `bitLenRat_add` and the Leibniz bound compile before any bit-complexity claim.
- Gate 3: Claim 19 re-derivation reviewed before Prop 4's constants are quoted.
- Gate 4: the five paper corrections merged before the next external report.

## 9. Known risks and counterexamples

Full report: `PAPER_I_MATH_AUDIT.md`. Top items:

1. **Eq. (1) is literally false**; true form `q_min ≤ n₀−p` (verified counterexample, n = 2, k = 0).
2. **Claim 19** `(HᵀH)⁻¹` requires `ω = k` (counterexample `ω = 1 < k = 2`); re-derive via Cramer.
3. **§III-D index set**: `[ℓ]` vs `[k]` in `rem:algo`; cost claim depends on `[ℓ]`.
4. **Theorem 2 step (v)** should also cite Claim 9, Claim 11 and §III-D(ii).
5. **Algorithm 1** lacks the `q < r₀` guard (counterexample `r₀ = 2, q = 1`).

Lean-side: Hadamard absent (use `Matrix.det_le`); Bareiss is tactic-only.

## 10. Final acceptance criteria

- No `sorry`/`admit`/custom axioms in the Paper I closure.
- `lake build Q1Paper`, `lake env lean PaperI.lean`, both audits, and CI green.
- Each paper claim carries an explicit status in the map, with any deviation described.
- Bit-complexity claims backed by explicit lemmas.
- Roadmap, map and audit agree on the same commit.
