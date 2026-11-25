# Algorithm correctness: what is proved, what is missing

This document maps an external review's six propositions (A–F) for algorithm correctness onto the
Lean development, and states exactly which single theorem is missing.  It is the answer to the
question "are Algorithms 1 and 2 verified?" — no, but the gap is narrower than it looks.

Last updated: 2026-11-24, after the axiom audit reached 418 declarations.

## The six propositions

| id | proposition | status | evidence / gap |
|---|---|---|---|
| **A** | *Parameterization completeness*: every feasible free block is covered by the enumeration over `t` | **proved at the level of `W`** | `Claim4Converse.claim4_converse`: for every `W` with `row(L₀M) ≤ W ≤ row M` and `dim(W/W₀) ≤ r` there is an `R` with exactly `r` rows and `row([L₀;R] M) = W`. The converse of `claim4_sandwich`. |
| **B** | *Chart coverage*: every relevant subspace lies in some Grassmann chart | **proved** | `Chart14.exists_chart_bases` (the `E₀`, `E_Q` data) and `exists_chart_completion` (every `t`-dimensional subspace of `V/W₀` has a chart), with the chart count in `FptCore.fpt_chart_count_le`. |
| **C** | *Certificate correctness*: the algebraic constraints are equivalent to the original conditions | **proved in both directions** | `ChartComplete.PhiPoint` packages the five items of `eq:phi`; `phiPoint_of_conditions` produces one from the two row-space conditions (forward), and `feasible_of_phiPoint` gives the paper's `(5a)` and `(5b)` back from one (backward). Supporting: `row_LA_mul_le_row_L_mul`, `exists_chart_factorization`, `exists_L_pinned`, `raw_of_compressed`, `factor_of_phiPoint`. Item (ii) is carried by the row inclusion, which `claim8_rank_consistency` identifies with the rank-consistency system. |

**Soundness at the level of `DEC` is now a theorem**: `PaperI/Soundness.lean`'s `dec_of_phiPoint`
takes a chart point for the compressed data of `[L₀; R]` and concludes `DEC C A L0 r`.  The bridge is
`rawAlgebraic_submatrix` / `rawSpectral_submatrix` (a row bijection preserves both raw conditions)
plus `submatrix_mul_right`.  Completeness remains out of reach for this `DEC`, for the reason in the
next section — not for want of a lemma.
| **D** | *Backend correctness*: the real-algebraic decision procedure is correct | **not proved, and not attempted** | `RenegarBackend` is a structure carrying a cost bound; it has no correctness field. This is the honest boundary: Renegar's algorithm is cited, not formalised. |
| **E** | *Edge cases*: `q < r₀`, `ω = 0`, `r = 0` | **proved** | `q < r₀` is a one-line bound; `ω = 0` is Proposition 4 step 2 (and `decide_r0` decides it by the original conditions); `r = 0` is `prop4_r0_iff_spectral`. |
| **F** | *Complexity* | **partly proved** | Claim 19/21 bit-cost chain (`ExactDiv`, `ComplexityCounts`) is kernel-checked; Theorems 1 and 2 are *conditional* on `ChartSpecFixedDeg` / `FptChartSpec` (inhabited, exponents explicit). |

## The one missing theorem

Everything except **C** is either proved or explicitly out of scope.  C is missing the *assembly*:

```lean
theorem feasible_iff_exists_chart_point :
    (∃ L : Matrix (Fin q) (Fin n) ℝ, Feasible L) ↔
      ∃ (ω : ℕ) (J : Finset (Fin k)) (X B G x), PhiHolds ω J X B G x
```

where `Feasible L` is the paper's `(5a) ∧ (5b)` for `L` with `L`'s first `r₀` rows equal to `L₀`,
and `PhiHolds` is the five items of `eq:phi`.

### Proof plan, forward direction (`Feasible L → Φ-point`)

Given a feasible `L`, with `N` a basis of `ker[C; CA]`, `H = L N`, `H_A = L A N`, `ω = rank H`:

1. **`row(H_A) ≤ row(H)`.** ✅ **proved**: `ChartComplete.row_LA_mul_le_row_L_mul`.  `(5a)` says
   `row(LA) ≤ row[L;CA;C]`; right-multiplying by `N` gives `row(H_A) ≤ row(H) + row(CAN) + row(CN)`,
   and `CN = CAN = 0` because `N` spans `ker[C;CA]`.
2. **Rank factorization.** ✅ available: `RankFactorization.exists_rank_factorization_of_rank`
   gives `X` (`q×ω`, `rank X = ω`) and `B` (`ω×k`) with `X B = H` and a left inverse of `X`.
3. **`G`.** ✅ **proved**: `ChartComplete.exists_chart_factorization` combines steps 1–2 —
   `row(H_A) ≤ row(H)` gives `H_A = F H = F (X B) = (F X) B`, so one `B` serves both
   factorizations.  This is Φ's items (iii)/(iv) after the pivot normalization.
4. **`x`.** `(5b)` plus `claim11_iff_gram` give `x` with `ZᵀZ x = e₀` (Φ item (v)).  *Not yet
   assembled.*
5. Φ item (i) is `rank X = ω` (step 2), and item (ii) is the rank-consistency system, discharged
   by `claim8_rank_consistency` applied to the rows of `H_A`.  *Not yet assembled.*

### Proof plan, backward direction (`Φ-point → Feasible L`)

Given `(ω, J, X, B, G, x)`: **`claim8_rank_consistency`** supplies a `B` with `B[:,J] = I`, hence
`L` with the prescribed rows and `H = X B`, `H_A = G B`; `(5a)` follows from `H_A = (G X_L) X B`
using a left inverse `X_L` of `X` (`exists_left_inverse_of_rank_eq`), and `(5b)` from
`ZᵀZ x = e₀` via `claim11_iff_gram`.

## What this means for the review's acceptance criterion

The review asks for four theorems per algorithm: soundness, completeness, termination, complexity.
The current state gives:

| | Algorithm 1 | Algorithm 2 |
|---|---|---|
| soundness | components proved, assembly missing (C) | same, plus the `W₀ ⊆ V` test and the `W₀ = 0` shortcut, both proved as *statements* but not assembled |
| completeness | same gap | same gap |
| termination | the enumeration is finite and explicit (`min(q,k)` charts), so termination is immediate **once the assembly exists** | likewise (`min(r,2ℓ)` × `2^{m'}`) |
| complexity | conditional (F) | conditional (F) |

So the honest statement is: **the algorithms are not yet verified, and the single missing theorem
is the equivalence in C.**  Everything else the review lists is already in the development or is
explicitly declared out of scope.

## The two obstacles to the `DEC`-level theorem (found while attempting it)

Prop C is now proved **at the level of the compressed pair** (`PhiPoint`, both directions).  Lifting
it to `DEC C A L0 r` runs into two concrete obstacles, and they are of different kinds.

### (1) A reindexing obligation (technical)

`DEC C A L0 r` is `∃ R, let L := fromRows L0 R, rawAlgebraic … ∧ rawSpectral …`, and Mathlib's
`fromRows` gives `L` the row type `Fin r0 ⊕ Fin r`.  `PhiPoint`, however, is indexed by `Fin q`,
because its `gram` field uses `minorFamily`, which needs `Fin` indices for the window matrix.

So the lift needs a transfer lemma: for a bijection `e : Fin q' ≃ Fin q`,

    rawAlgebraic C CA (L.submatrix e.symm id) (LA.submatrix e.symm id) ↔ rawAlgebraic C CA L LA

and the same for `rawSpectral`, applied with `e := finSumFinEquiv`.  Rank is invariant under
reindexing, so this is plumbing rather than mathematics — but it is not free, because `rawAlgebraic`
is a rank of a *four-block* stack, so the bijection has to be assembled blockwise.

### (2) A real-vs-complex mismatch (substantive)

This one is not plumbing.  In `Interface.lean`,

    rawSpectral C CA L LA := ∀ lam : K, rank [lam • L - LA; CA; C] = rank [L; CA; C]

quantifies over the **base field**, while `claim11_iff_gram` states (5b) over **ℂ** (the paper's
convention, cf. the complex-λ remark in `paper_I_dec.tex`).  The implication that holds is

    complex everywhere  ⟹  real everywhere

and that is exactly what `feasible_of_phiPoint` uses (specialise `z = ↑λ`, then `rank_map_ofReal`).
The converse is **false** — a pencil can keep full rank at every real λ and drop at a complex one —
so for the **real-λ** `DEC` there is no completeness direction at all.

Consequence for the review's acceptance table: the paper's Theorem 1 is about the *complex* `DEC`,
while the Lean definition called `DEC` is the *real* one.  They are different propositions.  The
honest options are

* state completeness for a complex-λ `DEC` (a new definition, e.g. `DECℂ`, whose spectral condition
  quantifies over `ℂ` after complexification), and keep the real `DEC` only for soundness; or
* leave the real `DEC` as a weaker variant and say so.

Neither is done yet, and the choice is the reviewer's to make because it changes what "Algorithm 1
is verified" means.

### What the complex-λ DEC would look like, and the one lemma it needs


awSpectral is polymorphic in the base field: 
awSpectral {p q n} (C CA : Matrix p n K)
(L LA : Matrix q n K) := forall lam : K, rank [lam L - LA; CA; C] = rank [L; CA; C].  So the
complex condition for real data is simply 
awSpectral at K = ℂ applied to the complexified
matrices, and

    DECℂ C A L0 r := exists R, let L := fromRows L0 R,
                       rawAlgebraic C (C*A) L (L*A) and rawSpectralℂ C (C*A) L (L*A)

with 
awSpectralℂ C CA L LA := rawSpectral (C.map f) (CA.map f) (L.map f) (LA.map f),  the
algebra map to ℂ.

Two of the three lemmas needed for DECℂ => DEC are routine:

* the scalar commutation (lam • L - LA).map f = (f lam) • L.map f - LA.map f (one ext/simp);
* 
ank ((M : Matrix _ _ R).map f) = M.rank (
ank_map_ofReal, already in the tree).

The third is the one that blocked the attempt: **(fromRows A B).map f = fromRows (A.map f)
(B.map f)** for romRows into a Fin m1 ⊕ Fin m2 row type.  It is a case split on the Sum
index, and my first two attempts (Fin.addCases, then a nested 
cases) did not line up with the
type.  It is a small lemma, but it is the gate for everything at the DECℂ level, so it is the
first thing to do next.

## Update: the complex-lambda specification now exists (PaperI/DecComplex.lean)

    complexDEC C A L0 r := exists R, let L := fromRows L0 R,
                             rawAlgebraic C (C*A) L (L*A) and spectralComplexRaw C (C*A) L (L*A)

with spectralComplexRaw the generic 
awSpectral on complexified matrices, indexed by **types**.
Proved alongside it: 
ank_map_ofReal_any (complexification preserves rank for any finite index
types) and dec_of_complexDEC : complexDEC -> DEC — the only direction that holds.

The five failed attempts at this definition had one root cause, worth recording because the error
message pointed elsewhere: it flagged L * A inside the **second** conjunct, and the cause was that

awSpectral_C had been declared with {p q n : Nat}, i.e. Fin q indices.  DEC's free block has
row type Fin r0 (+) Fin r, which is not Fin q for any q; 
awAlgebraic is polymorphic in its
index **types**, so the first conjunct accepted the term and the second could not.

## What remains: PhiPoint -> complexDEC

dec_of_phiPoint gives the real-lambda soundness.  The complex one needs the lift of the *compressed*
complex condition to the raw stack over C, i.e. 
awSpectral_iff_compressed at K = C.  Its
hypothesis is that the complexified kernel basis spans the complex kernel:

    (N.map f).mulVecLin.range = ker (fromRows ((C*A).map f) (C.map f))

Discharging that from N.mulVecLin.range = ker (fromRows (C*A) C) is dimension theory over C — an
inclusion plus a inrank equality via 
ank_map_ofReal_any and the kernel rank formula.  It is the
next discrete task.  An attempted file for it was **deleted, not committed**, because it contained a
sorry; the tree has none.
## Specification decision (settled)

The specification is the **complex-λ** one, `PaperI/DecComplex.lean`'s `complexDEC`, and the two
directions of the chart equivalence are both kernel-checked against it:

    ComplexSoundness.decComplex_of_phiPoint : chart point  ->  complexDEC      (soundness)
    ComplexCompleteness.phiPoint_of_complexDEC    : complexDEC (omega >= 1) -> chart point (completeness)

The older real-λ `DEC` is an auxiliary definition, linked only by
`DecComplex.dec_of_complexDEC : complexDEC -> DEC`.  That direction is the one that holds; the
converse is false (a pencil can keep full rank at every real lambda and drop at a complex one), which
is why completeness is stated against `complexDEC` and not against `DEC`.

Boundary still open: `omega = 0`.  `PhiPoint`'s Gram certificate comes from `claim11_iff_gram`, which
requires `omega >= 1`, so the completeness theorem carries `1 <= omega` as a hypothesis.  The
zero-rank branch is a separate case in the paper (Proposition 4 step 2 / `decide_r0`) and is not
covered by that theorem.
