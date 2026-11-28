import Mathlib

open Finset

/-!
Q1Paper/PaperV/Probability.lean

§V, the probabilistic counting core behind Theorem 8 (`thm:rp`, the one-sided test) and Theorem 19
(`thm:regime`).

**Paper usage.**  In the one-sided test of Theorem 8 two finite grids are sampled *independently*:
the coefficient vector `c` is drawn from a grid `S_c` and the fibre point `t` from a grid `S`, and the
test accepts when the resultant `D_c(t)` is nonzero.  Failure needs one of two things:

* the sampled `c` lies in the bad set, where `D_c ≡ 0` — a proportion of at most `d'/|S_c|`;
* the sampled `c` is good, so `D_c` is a nonzero polynomial in `t`, but the sampled `t` is one of its
  roots — a proportion of at most `deg_t D_c/|S| ≤ 2d'²/|S|`.

Counting over the product of the two grids turns this into the paper's acceptance bound
`1 - 2d'²/|S| - d'/|S_c|`.  That product count is the content of item 2 below, and the same
acceptance estimate is what Theorem 19 reuses inside the generic stratum.

**What this file covers.**

1. `schwartz_zippel_zero_count` — Mathlib's Schwartz–Zippel
   (`MvPolynomial.schwartz_zippel_totalDegree`, file
   `Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean`) restated in the form §V uses for `ℂ`-valued
   polynomials: for a nonzero `p` in `n` variables and a finite `S ⊆ ℂ`, the proportion of the grid
   `Sⁿ` on which `p` vanishes is at most `p.totalDegree / |S|`.  Mathlib's lemma already has exactly
   this content, so the declaration is only a named wrapper: the proof is Mathlib's, not ours.

2. `two_grid_bad_bound` (with the finite-type form `two_grid_bad_bound_univ`) — the pure counting
   union bound: if at most a proportion `a` of the first grid is bad, and inside every *good* first
   coordinate at most a proportion `b` of the second grid is bad, then at most a proportion `a + b` of
   the paired grid is bad.  `two_grid_good_bound` is the equivalent statement that at least
   `1 - a - b` of the pairs are good.  Only `Finset.card`, unions and complements are used: no
   probability measure appears.

3. `two_grid_failure_bound_of_schwartz_zippel` — the composition: a polynomial whose zero proportion
   on `Sⁿ` is at most `deg/|S|` (item 1) together with a per-row bad proportion `b` (item 2) gives
   joint failure proportion at most `deg/|S| + b`.  This is the shape of the paper's estimate; it is a
   special case of item 2 and it does not instantiate the resultant.

**Scope.**  This is *not* a formalisation of Theorem 8 or of Theorem 19.  Not formalised here: the
construction of `g_c` and of the resultant `D_c = Res_λ(f, g_c)`, its bidegree bounds `deg_c D_c ≤ d'`
and `deg_t D_c ≤ 2d'²`, a height bound on `D`, the one-sidedness step (a bad fibre forces `D_c ≡ 0`),
and the assembly of the two-grid inequality into the algorithmic statement.

No `sorry`, no axioms beyond Lean's three standard ones; the declarations are audited in
`Audit.lean` (and machine-checked by `ClaimsCheck.lean`).
-/

namespace Q1Paper.PaperV

/-! ## 1. Schwartz–Zippel, restated in the form used in §V -/

/-- **Schwartz–Zippel (Mathlib), paper form.**  For a nonzero polynomial `p` in `n` variables over
`ℂ` and a finite grid `S ⊆ ℂ`, the proportion of the grid `Sⁿ` on which `p` vanishes is at most
`p.totalDegree / |S|`, i.e. `#zeros / |S|^n ≤ p.totalDegree / |S|` in `ℚ≥0`.

Source: `MvPolynomial.schwartz_zippel_totalDegree` (Mathlib, `MvPolynomial.schwartz_zippel_totalDegree`
in `Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean`), specialised to `R = ℂ`; the grid is the
constant family `fun _ : Fin n => S`.  The proof below is Mathlib's — this is a named wrapper, not a
new proof. -/
theorem schwartz_zippel_zero_count {n : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p ≠ 0)
    (S : Finset ℂ) :
    #{f ∈ Fintype.piFinset fun _ : Fin n => S | MvPolynomial.eval f p = 0} / (#S ^ n : ℚ≥0)
      ≤ (p.totalDegree : ℚ≥0) / #S :=
  MvPolynomial.schwartz_zippel_totalDegree hp S

/-! ## 2. The two-grid counting core

We count pairs `(c, t)` in the product of the two grids `Cdom × Tdom`.  A pair is **bad** when either
its first coordinate lies in `badC`, or its first coordinate is good and its second lies in the
corresponding `badT c`; it is **good** when neither happens.  Nothing probabilistic is used: the two
statements below are statements about natural-number cardinalities, transported to `ℚ≥0` at the very
end only to divide by the grid size. -/

section Counting

variable {C T : Type*} [DecidableEq C] [DecidableEq T]

/-- The bad pairs of the two-grid test: the first coordinate is bad, or it is good and the second
coordinate is bad in its row. -/
def badPairs (Cdom : Finset C) (badC : Finset C) (Tdom : Finset T) (badT : C → Finset T) :
    Finset (C × T) :=
  (Cdom ×ˢ Tdom).filter fun p => p.1 ∈ badC ∨ p.2 ∈ badT p.1

/-- The good pairs of the two-grid test: both coordinates are good. -/
def goodPairs (Cdom : Finset C) (badC : Finset C) (Tdom : Finset T) (badT : C → Finset T) :
    Finset (C × T) :=
  (Cdom ×ˢ Tdom).filter fun p => p.1 ∉ badC ∧ p.2 ∉ badT p.1

/-- **Counting the bad pairs.**  The bad pairs are covered by the rows whose first coordinate is bad
(all of `Tdom` in such a row) together with the `badT c` fibres of the good first coordinates, so
their number is at most `#badC * #Tdom + ∑_{c ∈ Cdom, c ∉ badC} #(badT c)`.

Pure `Finset.card` bookkeeping: a union bound for `card`, `card_product` for a full row, and
`card_biUnion` for the (pairwise disjoint) bad fibres of distinct rows. -/
theorem card_badPairs_le (Cdom : Finset C) (badC : Finset C) (Tdom : Finset T)
    (badT : C → Finset T) :
    (badPairs Cdom badC Tdom badT).card ≤
      badC.card * Tdom.card + ∑ c ∈ Cdom.filter (fun c => c ∉ badC), (badT c).card := by
  classical
  have hsub : badPairs Cdom badC Tdom badT ⊆
      badC ×ˢ Tdom ∪ (Cdom.filter fun c => c ∉ badC).biUnion fun c => {c} ×ˢ badT c := by
    intro p hp
    simp only [badPairs, mem_filter, mem_product] at hp
    obtain ⟨⟨hpC, hpT⟩, hpbad⟩ := hp
    rcases em (p.1 ∈ badC) with h | h
    · exact mem_union_left _ (mem_product.mpr ⟨h, hpT⟩)
    · rcases hpbad with hbad | hbad
      · exact absurd hbad h
      · exact mem_union_right _
          (mem_biUnion.mpr ⟨p.1, mem_filter.mpr ⟨hpC, h⟩,
            mem_product.mpr ⟨mem_singleton.mpr rfl, hbad⟩⟩)
  have hdisj : (↑(Cdom.filter fun c => c ∉ badC) : Set C).PairwiseDisjoint
      fun c => {c} ×ˢ badT c := by
    intro a _ b _ hab
    refine Finset.disjoint_left.mpr ?_
    intro p hp hq
    simp only [mem_product, mem_singleton] at hp hq
    exact hab (hp.1.symm.trans hq.1)
  calc (badPairs Cdom badC Tdom badT).card
      ≤ (badC ×ˢ Tdom ∪ (Cdom.filter fun c => c ∉ badC).biUnion
          fun c => {c} ×ˢ badT c).card := card_le_card hsub
    _ ≤ (badC ×ˢ Tdom).card +
          ((Cdom.filter fun c => c ∉ badC).biUnion fun c => {c} ×ˢ badT c).card :=
        card_union_le _ _
    _ = badC.card * Tdom.card +
          ∑ c ∈ Cdom.filter (fun c => c ∉ badC), (badT c).card := by
        rw [card_product, card_biUnion hdisj]
        congr 1
        refine sum_congr rfl ?_
        intro c _
        rw [card_product, card_singleton, one_mul]

/-- **Theorem 19's counting core: the bad proportion is at most `a + b`.**  Let `a` bound the
proportion of bad first coordinates and let `b` bound the proportion of bad second coordinates inside
every good row.  Then at most a proportion `a + b` of the paired grid is bad.

Note that no hypothesis `badC ⊆ Cdom` is needed: rows of `badC` outside `Cdom` only make the estimate
`#badC ≤ a * #Cdom` larger, and `badC ⊆ Cdom` holds in the applications. -/
theorem two_grid_bad_bound (Cdom : Finset C) (badC : Finset C) (Tdom : Finset T)
    (badT : C → Finset T) (a b : ℚ≥0) (hCne : Cdom.Nonempty) (hTne : Tdom.Nonempty)
    (hC : (badC.card : ℚ≥0) / Cdom.card ≤ a)
    (hT : ∀ c ∈ Cdom, c ∉ badC → ((badT c).card : ℚ≥0) / Tdom.card ≤ b) :
    ((badPairs Cdom badC Tdom badT).card : ℚ≥0) /
      ((Cdom.card : ℚ≥0) * Tdom.card) ≤ a + b := by
  classical
  have hCpos : (0 : ℚ≥0) < (Cdom.card : ℚ≥0) := by
    have h : 0 < Cdom.card := card_pos.mpr hCne
    exact_mod_cast h
  have hTpos : (0 : ℚ≥0) < (Tdom.card : ℚ≥0) := by
    have h : 0 < Tdom.card := card_pos.mpr hTne
    exact_mod_cast h
  have hden : (0 : ℚ≥0) < (Cdom.card : ℚ≥0) * Tdom.card := mul_pos hCpos hTpos
  rw [div_le_iff₀ hden]
  have hcardQ : ((badPairs Cdom badC Tdom badT).card : ℚ≥0) ≤
      (badC.card : ℚ≥0) * Tdom.card +
        ∑ c ∈ Cdom.filter (fun c => c ∉ badC), ((badT c).card : ℚ≥0) := by
    exact_mod_cast card_badPairs_le Cdom badC Tdom badT
  have h1 : (badC.card : ℚ≥0) * Tdom.card ≤ a * ((Cdom.card : ℚ≥0) * Tdom.card) := by
    have hbad : (badC.card : ℚ≥0) ≤ a * Cdom.card := (div_le_iff₀ hCpos).mp hC
    calc (badC.card : ℚ≥0) * Tdom.card ≤ (a * Cdom.card) * Tdom.card := by gcongr
      _ = a * ((Cdom.card : ℚ≥0) * Tdom.card) := by ring
  have h2 : (∑ c ∈ Cdom.filter (fun c => c ∉ badC), ((badT c).card : ℚ≥0)) ≤
      b * ((Cdom.card : ℚ≥0) * Tdom.card) := by
    have hrow : ∀ c ∈ Cdom.filter (fun c => c ∉ badC),
        ((badT c).card : ℚ≥0) ≤ b * Tdom.card := by
      intro c hc
      exact (div_le_iff₀ hTpos).mp (hT c (mem_filter.mp hc).1 (mem_filter.mp hc).2)
    calc (∑ c ∈ Cdom.filter (fun c => c ∉ badC), ((badT c).card : ℚ≥0))
        ≤ ∑ c ∈ Cdom.filter (fun c => c ∉ badC), b * Tdom.card := sum_le_sum hrow
      _ = ((Cdom.filter (fun c => c ∉ badC)).card : ℚ≥0) * (b * Tdom.card) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (Cdom.card : ℚ≥0) * (b * Tdom.card) := by
          gcongr
          exact filter_subset _ _
      _ = b * ((Cdom.card : ℚ≥0) * Tdom.card) := by ring
  calc ((badPairs Cdom badC Tdom badT).card : ℚ≥0)
      ≤ (badC.card : ℚ≥0) * Tdom.card +
          ∑ c ∈ Cdom.filter (fun c => c ∉ badC), ((badT c).card : ℚ≥0) := hcardQ
    _ ≤ a * ((Cdom.card : ℚ≥0) * Tdom.card) + b * ((Cdom.card : ℚ≥0) * Tdom.card) :=
        add_le_add h1 h2
    _ = (a + b) * ((Cdom.card : ℚ≥0) * Tdom.card) := by ring

/-- **Theorem 19's counting core, finite-type form.**  With the grids taken to be the whole of two
finite types, the statement reads `#badC / #C ≤ a` and `#(badT c) / #T ≤ b`, hence the bad proportion
of `C × T` is at most `a + b`.  This is the literal form of the paper's counting step. -/
theorem two_grid_bad_bound_univ {C T : Type*} [Fintype C] [Fintype T] [DecidableEq C]
    [DecidableEq T] [Nonempty C] [Nonempty T] (badC : Finset C) (badT : C → Finset T) (a b : ℚ≥0)
    (hC : (badC.card : ℚ≥0) / Fintype.card C ≤ a)
    (hT : ∀ c, c ∉ badC → ((badT c).card : ℚ≥0) / Fintype.card T ≤ b) :
    ((badPairs (univ : Finset C) badC (univ : Finset T) badT).card : ℚ≥0) /
      ((Fintype.card C : ℚ≥0) * Fintype.card T) ≤ a + b := by
  have h := two_grid_bad_bound (univ : Finset C) badC (univ : Finset T) badT a b
    (univ_nonempty) (univ_nonempty) (by simpa using hC) (fun c _ hc => by simpa using hT c hc)
  simpa using h

/-- **Counting complement.**  If the good and bad parts of a grid of size `D` add up to `D` and the
bad proportion is at most `a + b`, then the good proportion is at least `1 - a - b`.  This is the
elementary `ℚ≥0` step relating the two halves of the counting core, stated with the sizes as separate
variables so that it can be used without unfolding either grid. -/
theorem one_sub_le_div_of_add_eq {G B : ℕ} {D a b : ℚ≥0} (hD : 0 < D)
    (hsum : (G : ℚ≥0) + (B : ℚ≥0) = D) (hB : (B : ℚ≥0) / D ≤ a + b) :
    1 - a - b ≤ (G : ℚ≥0) / D := by
  rw [tsub_tsub, tsub_le_iff_right]
  have hkey : (G : ℚ≥0) / D + (B : ℚ≥0) / D = 1 := by
    rw [← add_div, hsum, div_self (ne_of_gt hD)]
  calc (1 : ℚ≥0) = (G : ℚ≥0) / D + (B : ℚ≥0) / D := hkey.symm
    _ ≤ (G : ℚ≥0) / D + (a + b) := by gcongr

/-- **The good proportion is at least `1 - a - b`.**  The complement of `two_grid_bad_bound`: the good
pairs are the bad-free pairs, so their number is the size of the product minus the number of bad pairs,
and `one_sub_le_div_of_add_eq` converts the bad bound into the good one.  As everywhere in `ℚ≥0`,
`1 - a - b` is truncated subtraction, so the inequality is trivially true when `a + b ≥ 1`. -/
theorem two_grid_good_bound (Cdom : Finset C) (badC : Finset C) (Tdom : Finset T)
    (badT : C → Finset T) (a b : ℚ≥0) (hCne : Cdom.Nonempty) (hTne : Tdom.Nonempty)
    (hC : (badC.card : ℚ≥0) / Cdom.card ≤ a)
    (hT : ∀ c ∈ Cdom, c ∉ badC → ((badT c).card : ℚ≥0) / Tdom.card ≤ b) :
    1 - a - b ≤ ((goodPairs Cdom badC Tdom badT).card : ℚ≥0) /
      ((Cdom.card : ℚ≥0) * Tdom.card) := by
  classical
  have hCpos : (0 : ℚ≥0) < (Cdom.card : ℚ≥0) := by
    have h : 0 < Cdom.card := card_pos.mpr hCne
    exact_mod_cast h
  have hTpos : (0 : ℚ≥0) < (Tdom.card : ℚ≥0) := by
    have h : 0 < Tdom.card := card_pos.mpr hTne
    exact_mod_cast h
  have hden : (0 : ℚ≥0) < (Cdom.card : ℚ≥0) * Tdom.card := mul_pos hCpos hTpos
  have hbad := two_grid_bad_bound Cdom badC Tdom badT a b hCne hTne hC hT
  -- the two kinds of pair partition the product
  have hprod : ((goodPairs Cdom badC Tdom badT).card : ℚ≥0) +
      ((badPairs Cdom badC Tdom badT).card : ℚ≥0) =
      (Cdom.card : ℚ≥0) * Tdom.card := by
    have hpart := card_filter_add_card_filter_not (s := Cdom ×ˢ Tdom)
      (p := fun p : C × T => p.1 ∈ badC ∨ p.2 ∈ badT p.1)
    have hgood : (Cdom ×ˢ Tdom).filter
        (fun p : C × T => ¬ (p.1 ∈ badC ∨ p.2 ∈ badT p.1)) = goodPairs Cdom badC Tdom badT := by
      ext p
      simp only [goodPairs, mem_filter, not_or]
    rw [← hgood, ← Nat.cast_add, add_comm]
    simp only [badPairs]
    rw [hpart, card_product, Nat.cast_mul]
  exact one_sub_le_div_of_add_eq hden hprod hbad

end Counting

/-! ## 3. Composing the two: the shape of the paper's estimate

The resultant `D_c` is *not* constructed here.  What the composition needs from it is only that its
zero set on the coefficient grid has proportion at most `deg/|S|` — which is exactly what
Schwartz–Zippel supplies — and that on every good coefficient the bad `t` form at most a proportion
`b` of the fibre grid.  The statement below records that composition. -/

section Compose

/-- **Theorem 19's failure bound, in the form used in §V.**  If the zero set of `p` on the grid `Sⁿ`
occupies at most a proportion `p.totalDegree / |S|` of it (Schwartz–Zippel, item 1) and if, for every
grid point at which `p` does not vanish, the bad set `badT x` occupies at most a proportion `b` of the
second grid `T`, then at most a proportion `p.totalDegree / |S| + b` of the paired grid `Sⁿ × T` is
bad.  This is `two_grid_bad_bound` with `a = p.totalDegree / |S|` and the first grid's bad set read off
from `p`; no resultant is instantiated. -/
theorem two_grid_failure_bound_of_schwartz_zippel {n : ℕ} {p : MvPolynomial (Fin n) ℂ}
    (hp : p ≠ 0) (S T : Finset ℂ) (hS : S.Nonempty) (hT : T.Nonempty)
    (badT : (Fin n → ℂ) → Finset ℂ) (b : ℚ≥0)
    (hbadT : ∀ x ∈ Fintype.piFinset (fun _ : Fin n => S), MvPolynomial.eval x p ≠ 0 →
      ((badT x).card : ℚ≥0) / T.card ≤ b) :
    ((badPairs (Fintype.piFinset fun _ : Fin n => S)
        ((Fintype.piFinset fun _ : Fin n => S).filter (fun x => MvPolynomial.eval x p = 0))
        T badT).card : ℚ≥0) /
      (((Fintype.piFinset fun _ : Fin n => S).card : ℚ≥0) * T.card) ≤
      (p.totalDegree : ℚ≥0) / S.card + b := by
  classical
  -- the zero proportion on the grid, from Schwartz–Zippel
  have hC : (((Fintype.piFinset fun _ : Fin n => S).filter
        (fun x => MvPolynomial.eval x p = 0)).card : ℚ≥0) /
        ((Fintype.piFinset fun _ : Fin n => S).card : ℚ≥0) ≤
        (p.totalDegree : ℚ≥0) / S.card := by
    have hsz := schwartz_zippel_zero_count hp S
    have hcard : ((Fintype.piFinset fun _ : Fin n => S).card : ℚ≥0) = (#S : ℚ≥0) ^ n := by
      rw [Fintype.card_piFinset, prod_const, card_univ, Nat.cast_pow]
      simp
    rwa [hcard]
  have hT' : ∀ c ∈ Fintype.piFinset fun _ : Fin n => S,
      c ∉ (Fintype.piFinset fun _ : Fin n => S).filter
        (fun x => MvPolynomial.eval x p = 0) → ((badT c).card : ℚ≥0) / T.card ≤ b := by
    intro c hc hcnot
    refine hbadT c hc ?_
    intro hzero
    exact hcnot (mem_filter.mpr ⟨hc, hzero⟩)
  exact two_grid_bad_bound (Fintype.piFinset fun _ : Fin n => S)
    ((Fintype.piFinset fun _ : Fin n => S).filter (fun x => MvPolynomial.eval x p = 0))
    T badT ((p.totalDegree : ℚ≥0) / S.card) b
    (Fintype.piFinset_nonempty.mpr (fun _ => hS)) hT hC hT'

end Compose

end Q1Paper.PaperV
