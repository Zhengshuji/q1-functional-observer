# Paper I Master Roadmap

> 只管理任务与状态，不重复数学证明。逐项对照见 `PAPER_I_FORMALIZATION_MAP.md`；数学审计见 `PAPER_I_MATH_AUDIT.md`；Claim 19 重推见 `PAPER_I_CLAIM19_CRAMER.md`。
> 最后同步：commit `86a7f09`（D1 单子式符号关系），审计 140 条声明。

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
- Independent mathematical audit of Paper I, five primary findings (commit `5963a27`), see `PAPER_I_MATH_AUDIT.md`.
- **Paper corrections of the five primary findings** (commit `f6be7a4`): Eq. (1) restricted to the minimal order,
  Algorithm 1 `q < r₀ → INFEASIBLE` guard, Theorem 1 restricted to `r₀ ≤ q ≤ n` and stated as `DEC_q ∈ P`,
  §III-D column sets `J ⊆ [ℓ]`, Theorem 2 step (v) full citation chain, Table 5 regenerated.
- **Claim 19 Cramer re-derivation** (report `PAPER_I_CLAIM19_CRAMER.md`, commit `5181bef`): replaces `(HᵀH)⁻¹`
  by Cramer on an invertible `ω × ω` minor (row replacement); corrected constants
  `h(F) ≤ 41n⁴L`, `h(G) ≤ 20n²L`, `τ₀ ≤ 20n²L`, `M ≤ 2n³`, total `1.41×10⁴n¹⁹L²` (paper accounting) /
  `1.21×10⁵n²¹L²` (strict clearing); the `r = 0` polynomial-time claim survives.
- Claim 13 bit-length base, 43 declarations (commit `80eac0a`): `bitLenInt`, `bitLenRat`, `bitLenMat`,
  cleared-entry identity `|A.num i j| = A.den * |A i j|`.
- **`bitLenRat_add` and the Leibniz determinant bound** (commit `2756ead`, `BitLenAdd.lean`):
  `bitLenRat (q₁+q₂) ≤ 1 + bitLenRat q₁ + bitLenRat q₂`;
  `|M.det| ≤ ω!·B^ω` for `|M i j| ≤ B`; `bitLenInt M.det ≤ ω·b + bitLenInt ω!`;
  and the rational-matrix corollary `bitLenInt A.num.det ≤ ω·bitLenMat A + bitLenInt ω!`.
- **D1 single-minor sign relation** (commit `86a7f09`): `det_submatrix_perm` generalised to
  `[CommRing R]` (the field-only version made the elaborator search for `Field K[X]` and diverge);
  plain-`Finset` layer `embOfFinset`, `imageFinset`, `imageFinset_card`, `imageEquivFinset`,
  `permOfImage`, `embOfFinset_permOfImage`; `det_submatrix_comp`; and
  `maximalMinor_injective_eq_signed_image`.
- Axiom audit: **161 declarations**, only `propext`, `Classical.choice`, `Quot.sound`.

## 3. Open mathematical proofs

- **P0 (paper appendix):** rewrite Claim 19 / Claim 21 / Proposition 4 with the Cramer construction and the
  corrected constants; keep the strict-clearing and paper-accounting complexities as separate statements
  (main theorem: strict; remark: paper accounting).
- Claim 14, 15, 16, Theorem 5 (∃ℝ encoding).
- **P2 (secondary audit items):** Claim 15(i) prescribed-factorization restriction, Claim 22 rows/columns swap,
  Claim 16 unconditional citation.

## 4. Open Lean formalizations

- **D1 bridge**. Structure revised after an external review (web ChatGPT, whose reading of the repo was
  confirmed): prove the coefficient relation first, then a *generic fibre-sum lemma*, then the Gram
  scaling, then the certificate equivalence; row-space equality is a separate structural result and is
  **not** needed for the certificate equivalence.
  1. ~~single-minor sign relation~~ (`maximalMinor_injective_eq_signed_image`, done);
  2. coefficient relation: each coefficient of `f_{ρ,κ}` is the sign times the coefficient of `f_{I,J}`;
  3. generic fibre lemma: for finite `R, S`, a surjection `Φ : R → S` with every fibre of cardinality `m`,
     a sign `ε : R → K` with `ε r ^ 2 = 1`, and `v : S → Fin n → K`, one has
     `∑ r, (ε r • v (Φ r))ᵀ (ε r • v (Φ r)) = m • ∑ s, v sᵀ v s`
     (sum by index with multiplicity, never by distinct vector values);
  4. instantiate: `R` = injective pairs, `S` = subset pairs, `Φ` = images, `m = (ω!)²`,
     `ε = sign σ · sign τ`, giving `Z_injᵀZ_inj = (ω!)² • Z_subᵀZ_sub`;
  5. certificate equivalence: `G₁ = m • G₂`, `m ≠ 0` (characteristic 0: true over ℚ/ℝ/ℂ; in
     characteristic `p ≤ ω` the factorial vanishes, so the hypothesis must be explicit);
  6. row-space equality (`rowSpace Z_inj = rowSpace Z_sub`): needs both inclusions; forward from the
     sign relation, backward from surjectivity of the image map. Zero rows, repeated rows and signs are
     harmless.
- §III-D end-to-end assembly at the pencil.
- Claim 13: Bareiss intermediate/subminor relation (pivoting, zero pivots, rank deficiency), total bit complexity,
  and the input-length interface `bitLenMat A ≤ L_input`.

## 5. Complexity and bit-length

- `bitLen` foundation, `bitLenRat_add`, Leibniz determinant bound: **done**.
- Denominator clearing: `Matrix.num`/`Matrix.den`, exact identity: **done**.
- Bareiss: meta-level only in Mathlib; intermediate/subminor relation is new mathematics.
- Input-length convention: `bitLenMat A ≤ L_input` needs an explicit input-encoding definition (open).

## 6. Paper-to-Lean correspondence

- Maintained in `PAPER_I_FORMALIZATION_MAP.md` (§4 per-claim, §7 audit findings).
- Known deviation: D1 steps 2–6 (bridge incomplete); §III-D compression is proved for the subset family only.

## 7. Parallel workstreams

| Stream | Owner | Status |
|---|---|---|
| A. D1 bridge + §III-D assembly | main line | in progress (step 1 of 6 done) |
| B. Paper corrections | paper agent / main line | **done** (commit `f6be7a4`) |
| C. Claim 19: math re-derivation | math agent | **done** (report) |
| C'. Claim 19: paper appendix rewrite | paper agent | **done** (commit `ca0305b`) |
| D. Claim 13 bit length (`bitLenRat_add`, Leibniz) | Lean agent | **done** |
| E. Bareiss intermediates | algorithm agent | to launch |
| F. Roadmap / map / audit consistency | main line | continuous |

## 8. Dependencies and integration gates

- Gate 1: D1 steps 2–6 complete before §III-D is declared integrated.
- Gate 2: input-length interface before any `L`-complexity claim.
- Gate 3: Claim 19 appendix rewrite reviewed before Prop 4's constants are quoted.
- Gate 4: Bareiss intermediate relation before the final bit-complexity theorem.

## 9. Known risks and counterexamples

Full report: `PAPER_I_MATH_AUDIT.md`. Top items:

1. **Eq. (1)** was literally false; now fixed to `q_min ≤ n₀−p`.
2. **Claim 19** `(HᵀH)⁻¹` required `ω = k`; re-derived via Cramer (report), appendix pending.
3. **§III-D index set** `[ℓ]` vs `[k]`; fixed in the remark.
4. **Theorem 2 step (v)** citation chain; fixed.
5. **Algorithm 1** `q < r₀` guard; fixed.

Lean-side: Hadamard absent (use `Matrix.det_le`); Bareiss is tactic-only; `det_submatrix_perm` must stay
`[CommRing R]` (a field-only version diverges on `K[X]`).

## 10. Final acceptance criteria

- No `sorry`/`admit`/custom axioms in the Paper I closure.
- `lake build Q1Paper`, `lake env lean PaperI.lean`, both audits, and CI green, with the run link recorded.
- Each paper claim carries an explicit status in the map, with any deviation described.
- Bit-complexity claims backed by explicit lemmas.
- Roadmap, map and audit agree on the same commit.
