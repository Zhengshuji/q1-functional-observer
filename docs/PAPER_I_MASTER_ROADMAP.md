# Paper I master roadmap

> **Historical record.** This file documents a stage of the work and is kept for provenance.
> Gaps it describes may have been closed since; do not read it as the current status.
> Current status and the reading entry point: [START_HERE.md](START_HERE.md).


> **STATUS DISCLAIMER (2026-11-23).** This file is the *plan and its history*; it is not kept in
> lockstep with the code.  The **single source of truth for per-claim status is
> `docs/PAPER_I_FORMALIZATION_MAP.md`** (currently 352 audited declarations, CI green).
> Sections below that still say "D1 pending", quote 140/167 declarations, or describe Claims
> 13-16 as paper-only are historical records of earlier rounds, not the current state.

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
- **D1 bridge complete** (commits `86a7f09` … `2d29702`): six steps, from the
  single-minor sign relation through the coefficient relation, the window row,
  the Gram scaling `(ω!)²`, the certificate equivalence, to the row-space
  equality; map entry D1 closed.
- **Claim 13 layer** (commits `2756ead`, `842ed52`, `9afc183`, `7f0f5f1`,
  `b5c6d14`, `82e1c38`): `bitLenRat_add`, the Leibniz determinant bound, the
  input-length interface `bitLenMat A ≤ inputLen A`, the bordered
  Desnanot–Jacobi identity (block / tuple / prefix forms), the Bareiss tableau
  defined by recursion with `tab_eq_bord`, `tab_pivot`, `tab_last`, and the
  bit-length corollaries `tab_entry_num_bitLen`,
  `tab_entry_bitLen_inputLen`.  The appendix constant of Claim 21 was corrected
  from `M tau + (M/2) log2 M` to `M tau + bitLen(M!)` (audit D10).
- Axiom audit: **191 declarations**, only `propext`, `Classical.choice`, `Quot.sound`.

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
- ~~D1 bridge incomplete~~ (closed, commit `2d29702`): the injective-map-indexed and subset-indexed window matrices are now connected by five equivalence theorems (sign, coefficient, window row, Gram scaling, certificate) and the row-space equality.

## 7. Parallel workstreams

| Stream | Owner | Status |
|---|---|---|
| A. D1 bridge + §III-D assembly | main line | **D1 complete** (all 6 steps) |
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

## 11. Claims 13–15: formalization route (decided 2026-11-23, after external review)

The paper's Claims 13 (`lem:rationalbasis`), 14 (`clm:chartdata`) and 15 (`lem:coeff`) are stated as
"computed in poly(bit) operations, with entries of bit length <= ...".  Mathlib has no complexity theory,
and a cost model would be a project of its own.  Decision (route A, recommended by the external review):

- Formalize the **mathematical specification**: existence of the objects plus the **explicit bit-length
  bound** (each entry a ratio of minors of the cleared matrix, bounded by Leibniz).
- Leave the **"poly bit operations"** clause as a paper-level statement, labelled explicitly.
- Three-state labelling to be used from now on:
  `[Lean]` = statement and bound kernel-checked; `[Lean-conditional]` = formalized under explicit
  hypotheses; `[Paper proof]` = complexity/algorithmic claim, not formalized.
- Never derive "X is computable in poly bit operations" from "there exists X with bitLen X <= B".

Ordering (by value/cost, then by strategic value):

1. Claim 15(iv) `beta <= 240 q n^5 L`: pure `Nat` counting, layered inequality chain
   (first the intermediate bounds, then `omega`/`nlinarith`) — cheapest self-contained result.
2. Claim 14 `clm:chartdata`: `Submodule.map` for `V = T cap (S x S)` via the kernel of
   `[A_T^T; -A_V^T]`; the image of a kernel basis is only a **generating set**, so a linear-dependence
   removal step is required before calling it a basis.
3. Claim 13 `lem:rationalbasis`: kernel basis, row-space basis, annihilator with the explicit
   `tau_M` bound — most work, most reusable.

Warnings to keep in mind: (a) row-space equality and the Gram identity are independent results, neither
may be used as a premise for the other (already respected: `RowSpanBridge` and `GramInj` are separate);
(b) the image of a basis under a linear map spanning the target space is not automatically a basis;
(c) `[Paper proof]` must never be silently upgraded to `[Lean]`.

## 12. Status after the four closing items (2026-11-23)

Integrated (all kernel-checked, no `sorry`, audit 233 declarations, CI green):

- `PaperI/RationalBasis.lean` — **Claim 13** (`lem:rationalbasis`) with the paper's exact constant
  `tauM`; kernel basis, row-space basis and annihilator, all entries bounded (commit `7c27898`).
- `PaperI/Claim14.lean` — **Claim 14** core: the intersection `V = T cap (S x S)` as the image of the
  equalizer `(u,v) |-> psi u - phi v`, plus the "generating set vs basis" criterion and the dependency
  removal via the first isomorphism theorem (commit `f0a28ff`).
- `PaperI/Claim15iv.lean` — **Claim 15(iv)** arithmetic skeleton: the chain
  `X -> Z -> S -> beta` with the constants 22/47/240 pinned hypothesis-free (commit `26231ea`).
- `PaperI/RankFactorization.lean` — rank factorization with explicit left/right inverses (commit `baaa7f4`).
- `PaperI/T5Complete.lean` — **Theorem 5** completeness and the two directions combined; stated with
  the paper's complex-lambda (5b), with the real-lambda counterexample recorded (commit `bd96554`).

Acceptance table (from the external review):

| item | status |
|---|---|
| Claims 1/2/9/10/11/12 | done |
| §III-D compression + D1 bridge | done |
| Claim 13 Bareiss / bit length / rank factorization | done |
| Claim 13 rational basis existence + explicit bound | **done** |
| Theorem 5 completeness | **done** (complex-lambda form) |
| Claim 14 intersection (kernel-image + basis interface) | **done** |
| Claim 15(iv) intermediate bounds => beta | **done** (skeleton) |
| Three-state labelling | done (map + this roadmap) |

Still paper-level by decision (route A): the "computed in polynomially many bit operations" clause of
Claims 13/14/15, the `D`-form of (B2), the `omega = 0` branch of the encoding, and the literal gcd
formulation of Claim 16(iii).  The paper's Claim 19 appendix still awaits independent review.

## 13. Full-coverage goal (2026-11-23): three rounds

Objective upgraded from route A ("math spec + bit bounds") to covering the whole paper: mathematical
correctness, executable algorithms, and complexity bounds with explicitly declared external assumptions.

### Round 1 -- math coverage closure (`PaperIComplete.lean`)

- Claims 3-8 bridged from the abstract-core project lemmas (`Q1Subspace`, `Q1Projection`, `BoundLower`,
  `Monotone`, `G5GramRank`) to the paper's statements and into the Paper I audit.
- Theorem 5 restated with `DECℂ` (not the real `DEC`), the D-form of (B2), and the `omega = 0` branch.
- Claim 16 literal gcd form over `Q[lambda]` and its link to the no-common-root condition.
- Claim 19/21 constant chains as independent arithmetic specs.
- Acceptance: every body claim/theorem has a Lean statement (or an explicit conditional interface),
  no real-DEC posing as complex-DEC, CI green, audit list updated.

### Round 2 -- cost model and Theorem 1 (`Q1Complexity/Core.lean` + `Theorem1.lean`)

- `Cost`, `Q1Prog`, sequential/branch/loop cost semantics, bit costs of the rational primitives.
- One real algorithm executed through the semantics; domain-operation count derived from the semantics;
  bit cost derived from the integer primitives.
- Proposition 4 (r = 0) and Theorem 1's `L^{O(q^2)}` statement; Theorem 1 must not depend on unproved
  cost fields.

### Round 3 -- Theorem 2 and FPT (`Theorem2FPT.lean`)

- Chart enumeration and its count, semialgebraic instance-size bounds, `RenegarBoundSpec` as an explicit
  structure, the conditional FPT theorem, Corollary 6, and the correspondence of Corollary 3 with
  Theorem 1.
- The Renegar dependency is passed explicitly and recorded; no external complexity bound is labelled
  unconditional `[Lean]`.

### Design decisions

1. One DSL is not required for every algorithm: keep algorithm-specific implementations and route them
   through a uniform cost interface (`CostedResult`) to the complexity theorems.
2. External assumptions are registered in a structure (e.g. `ExternalComplexityAssumptions`) so the
   dependency of the final theorem is visible and auditable.
3. Every algorithm has three separate interfaces: `algorithm`, `algorithm_correct`, `algorithm_cost`
   (the last may be conditional); the three are audited separately.