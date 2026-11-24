# Algorithm correctness: what is proved, what is missing

This document maps an external review's six propositions (A–F) for algorithm correctness onto the
Lean development, and states exactly which single theorem is missing.  It is the answer to the
question "are Algorithms 1 and 2 verified?" — no, but the gap is narrower than it looks.

Last updated: 2026-11-24, after the axiom audit reached 418 declarations.

## The six propositions

| id | proposition | status | evidence / gap |
|---|---|---|---|
| **A** | *Parameterization completeness*: every feasible free block is covered by the enumeration over `t` | **proved at the level of `W`** | `Claim4Converse.claim4_converse`: for every `W` with `row(L₀M) ≤ W ≤ row M` and `dim(W/W₀) ≤ r` there is an `R` with exactly `r` rows and `row([L₀;R] M) = W`. The converse of `claim4_sandwich`. |
| **B** | *Chart coverage*: every relevant subspace lies in some Grassmann chart | **proved** | `Claim14Basis.exists_chart_bases` (the `E₀`, `E_Q` data) and `exists_chart_completion` (every `t`-dimensional subspace of `V/W₀` has a chart), with the chart count in `FptCore.fpt_chart_count_le`. |
| **C** | *Certificate correctness*: the algebraic constraints are equivalent to the original conditions | **components proved, assembly missing** | components: `claim5_conditions_depend_on_W` ((5a)/(5b) depend only on `W`), `claim8_rank_consistency` (the `M b = c` system), `claim11_iff_gram` (`ZᵀZ x = e₀` ⟺ (5b)), `prop4_r0_iff_spectral` (the `r = 0` case). **Missing: the single statement `(∃ L, feasible L) ⟺ ∃ (ω, J, Φ-point)`.** |
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
