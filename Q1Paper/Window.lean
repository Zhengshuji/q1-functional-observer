
import Mathlib
import Q1Paper.RowSpaceAlgebraic
import Q1Paper.SubspaceQuotient
/-!
Q1Paper/Window.lean

Paper I, Claim 10 (`lem:window`, "degree-windowed relations").

The paper fixes `f₁, …, f_s ∈ K[λ]` of degree at most `ω`, writes `c_{i,a}` for the
coefficient of `λ^a` (zero outside `0 ≤ a ≤ ω`), and forms the window matrix `Z` with rows
`(i, j)`, `0 ≤ j < ω`, columns `t = 0, …, 2ω − 1`, and entries `Z_{(i,j),t} = c_{i, t−j}`.
For a polynomial `p` let `coef p` be its coefficient vector in `1, λ, …, λ^{2ω−1}`.  Claim 10
states

  `row Z = { coef (∑ i, g i * f i) : deg (g i) < ω }`.

The coefficient window is Mathlib's `Polynomial.toFn N`, the linear map sending a polynomial
to the vector of its first `N` coefficients; `toFn_apply` records that this is exactly the
paper's `coef`.  The entry `c_{i, t−j}` with the convention `c_{i,a} = 0` for `a < 0` is the
`ℕ`-truncated form `if j ≤ t then coeff (f i) (t - j) else 0`; under the paper's hypothesis
`deg (f i) ≤ ω` the coefficients with `a > ω` also vanish, so this is the paper's matrix.

Contents:

* `windowMatrix_apply`, `windowMatrix_row` : row `(i, j)` is `coef (λ^j * f i)`;
* `rowSpace_windowMatrix_eq_span_shift` : item 3, the row space of `Z` is the span of the
  coefficient windows of the shifts `λ^j * f i`;
* `toFn_sum_mem_rowSpace`, `exists_vecMul_windowMatrix` : item 4 (forward), the window of
  `∑ i, g i * f i` with `deg (g i) < ω` is a linear combination of the rows of `Z`;
* `row_mem_windowSet` : item 4 (backward), every row of `Z` is such a window;
* `rowSpace_windowMatrix_eq_windowSet`, `mem_rowSpace_iff_exists_window` : the paper's
  equality `row Z = { coef (∑ i, g i * f i) : deg (g i) < ω }` for `ω ≥ 1`;
* `toFn_injective_of_natDegree_lt`, `toFn_injOn_degree_lt_two_mul` : item 5, injectivity of
  the window map on polynomials of degree `< 2ω`;
* `natDegree_X_pow_mul_le` : the paper's degree bookkeeping, `deg (λ^j * f i) ≤ 2ω − 1`.

Only coefficient algebra is used, so the field is arbitrary; `K = ℝ` (the paper's case) is
covered.  The main results do not need the degree hypothesis `deg (f i) ≤ ω`: the identity
`coef (λ^j * p) = (coef p) shifted by j` holds for every polynomial.
-/


open Polynomial Matrix
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace Q1Paper

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-! ### The coefficient window and the window matrix -/

/-- Mathlib's coefficient window: the `i`-th entry of `Polynomial.toFn N p` is the
coefficient of `λ^i` in `p`.  This is the paper's `coef` (for `N = 2ω`). -/
@[simp] theorem toFn_apply (N : ℕ) (p : K[X]) (i : Fin N) :
    Polynomial.toFn N p i = p.coeff (i : ℕ) := rfl

/-- The degree-window matrix `Z` of Claim 10: rows are indexed by `(i, j)` with
`j : Fin ω`, columns by `t : Fin (2 * ω)`, and `Z p t = c_{i, t - j}`, where `c_{i,a} = 0`
for `a < 0` (the `if`).  For `deg (f i) ≤ ω` the coefficients with `a > ω` vanish as well,
so this is the paper's matrix. -/
noncomputable def windowMatrix (f : ι → K[X]) (ω : ℕ) :
    Matrix (ι × Fin ω) (Fin (2 * ω)) K :=
  fun p t => if (p.2 : ℕ) ≤ (t : ℕ) then (f p.1).coeff ((t : ℕ) - (p.2 : ℕ)) else 0

omit [Fintype ι] in
/-- Row `(i, j)` of the window matrix is the coefficient window of `λ^j * f i`. -/
theorem windowMatrix_apply (f : ι → K[X]) (ω : ℕ) (p : ι × Fin ω) (t : Fin (2 * ω)) :
    windowMatrix f ω p t
      = Polynomial.toFn (2 * ω) ((X : K[X]) ^ (p.2 : ℕ) * f p.1) t := by
  rw [windowMatrix]
  have h : Polynomial.toFn (2 * ω) ((X : K[X]) ^ (p.2 : ℕ) * f p.1) t
      = ((X : K[X]) ^ (p.2 : ℕ) * f p.1).coeff (t : ℕ) := rfl
  rw [h, Polynomial.coeff_X_pow_mul']

omit [Fintype ι] in
/-- Row `(i, j)` of the window matrix, as a vector. -/
theorem windowMatrix_row (f : ι → K[X]) (ω : ℕ) (p : ι × Fin ω) :
    windowMatrix f ω p
      = Polynomial.toFn (2 * ω) ((X : K[X]) ^ (p.2 : ℕ) * f p.1) :=
  funext (windowMatrix_apply f ω p)

omit [Fintype ι] in
/-- The paper's degree bookkeeping: if `deg p ≤ ω`, `ω ≥ 1` and `j < ω`, then
`deg (λ^j * p) ≤ 2ω − 1`, so the window of length `2ω` loses no coefficient. -/
theorem natDegree_X_pow_mul_le {ω : ℕ} (hω : 1 ≤ ω) {p : K[X]} (hp : p.natDegree ≤ ω)
    (j : Fin ω) :
    ((X : K[X]) ^ (j : ℕ) * p).natDegree ≤ 2 * ω - 1 := by
  calc ((X : K[X]) ^ (j : ℕ) * p).natDegree
      ≤ ((X : K[X]) ^ (j : ℕ)).natDegree + p.natDegree := Polynomial.natDegree_mul_le
    _ = (j : ℕ) + p.natDegree := by rw [Polynomial.natDegree_X_pow]
    _ ≤ (ω - 1) + ω := by
        have hj : (j : ℕ) ≤ ω - 1 := by omega
        omega
    _ = 2 * ω - 1 := by omega

/-! ### The row space of the window matrix (item 3) -/

/-- **Claim 10, item 3.**  The row space of `Z` is the span of the coefficient windows of
the shifts `λ^j * f i`, `0 ≤ j < ω`. -/
theorem rowSpace_windowMatrix_eq_span_shift (f : ι → K[X]) (ω : ℕ) :
    Q1Subspace.rowSpace (windowMatrix f ω)
      = Submodule.span K (Set.range (fun p : ι × Fin ω =>
          Polynomial.toFn (2 * ω) ((X : K[X]) ^ (p.2 : ℕ) * f p.1))) := by
  rw [Q1Subspace.rowSpace]
  have h : (fun p : ι × Fin ω => windowMatrix f ω p)
      = fun p : ι × Fin ω =>
          Polynomial.toFn (2 * ω) ((X : K[X]) ^ (p.2 : ℕ) * f p.1) :=
    funext (windowMatrix_row f ω)
  rw [h]

/-! ### The attainable windows (item 4) -/

/-- The paper's set of attainable coefficient windows: windows of the sums
`∑ i, g i * f i` with `deg (g i) < ω`. -/
noncomputable def windowSet (f : ι → K[X]) (ω : ℕ) : Set (Fin (2 * ω) → K) :=
  {v | ∃ g : ι → K[X], (∀ i, (g i).natDegree < ω) ∧
        v = Polynomial.toFn (2 * ω) (∑ i, g i * f i)}

/-- For `ω ≥ 1` the attainable windows form a `K`-submodule: the degree bound is preserved
by sums and scalar multiples.  This is the set on the right of Claim 10. -/
noncomputable def windowSubmodule (f : ι → K[X]) (hω : 1 ≤ ω) :
    Submodule K (Fin (2 * ω) → K) where
  carrier := windowSet f ω
  zero_mem' := by
    rw [windowSet]
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i
      simp only [Polynomial.natDegree_zero]
      exact lt_of_lt_of_le Nat.zero_lt_one hω
    · simp
  add_mem' := by
    rw [windowSet]
    rintro v w ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
    refine ⟨g + h, ?_, ?_⟩
    · intro i
      exact lt_of_le_of_lt (Polynomial.natDegree_add_le (g i) (h i)) (max_lt (hg i) (hh i))
    · rw [← map_add]
      congr 1
      simp [add_mul, Finset.sum_add_distrib]
  smul_mem' := by
    rw [windowSet]
    rintro c v ⟨g, hg, rfl⟩
    refine ⟨c • g, ?_, ?_⟩
    · intro i
      exact lt_of_le_of_lt (Polynomial.natDegree_smul_le c (g i)) (hg i)
    · rw [← map_smul]
      congr 1
      simp only [Finset.smul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp [smul_eq_C_mul, mul_assoc]

/-- **Claim 10, item 4 (forward).**  The coefficient window of `∑ i, g i * f i` with
`deg (g i) < ω` is a `K`-linear combination of the rows of `Z`. -/
theorem toFn_sum_mem_rowSpace (f : ι → K[X]) {g : ι → K[X]}
    (hg : ∀ i, (g i).natDegree < ω) :
    Polynomial.toFn (2 * ω) (∑ i, g i * f i)
      ∈ Q1Subspace.rowSpace (windowMatrix f ω) := by
  classical
  have hg_exp : ∀ i, g i = ∑ j : Fin ω,
      Polynomial.C ((g i).coeff (j : ℕ)) * (X : K[X]) ^ (j : ℕ) := by
    intro i
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ => Polynomial.C ((g i).coeff j) * (X : K[X]) ^ j) ω]
    exact Polynomial.as_sum_range_C_mul_X_pow' (g i) (hg i)
  have hmul : ∀ i, Polynomial.toFn (2 * ω) (g i * f i)
      = ∑ j : Fin ω, (g i).coeff (j : ℕ) •
          Polynomial.toFn (2 * ω) ((X : K[X]) ^ (j : ℕ) * f i) := by
    intro i
    conv_lhs => rw [hg_exp i]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [mul_assoc, ← smul_eq_C_mul, map_smul]
  have hmain : Polynomial.toFn (2 * ω) (∑ i, g i * f i)
      = ∑ p : ι × Fin ω, (g p.1).coeff (p.2 : ℕ) • windowMatrix f ω p := by
    calc Polynomial.toFn (2 * ω) (∑ i, g i * f i)
        = ∑ i, Polynomial.toFn (2 * ω) (g i * f i) := by rw [map_sum]
      _ = ∑ i, ∑ j : Fin ω, (g i).coeff (j : ℕ) •
            Polynomial.toFn (2 * ω) ((X : K[X]) ^ (j : ℕ) * f i) :=
          Finset.sum_congr rfl fun i _ => hmul i
      _ = ∑ p : ι × Fin ω, (g p.1).coeff (p.2 : ℕ) • windowMatrix f ω p := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
          exact Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by rw [windowMatrix_row]
  rw [hmain]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self p))

/-- **Claim 10, item 4 (forward), matrix form.**  The window of `∑ i, g i * f i` with
`deg (g i) < ω` is `y ᵥ* Z` for a coefficient vector `y` indexed by the rows of `Z`. -/
theorem exists_vecMul_windowMatrix (f : ι → K[X]) {g : ι → K[X]}
    (hg : ∀ i, (g i).natDegree < ω) :
    ∃ y : ι × Fin ω → K,
      y ᵥ* windowMatrix f ω = Polynomial.toFn (2 * ω) (∑ i, g i * f i) := by
  classical
  rw [← Q1Subspace.mem_rowSpan_iff_exists_vecMul]
  exact toFn_sum_mem_rowSpace f hg

/-- **Claim 10, item 4 (backward).**  Every row of `Z` is the window of a sum
`∑ i, g i * f i` with `deg (g i) < ω`: row `(i, j)` is the window of `λ^j * f i`. -/
theorem row_mem_windowSet (f : ι → K[X]) (ω : ℕ) (p : ι × Fin ω) :
    windowMatrix f ω p ∈ windowSet f ω := by
  classical
  have hω : 0 < ω := lt_of_le_of_lt (Nat.zero_le _) p.2.isLt
  rw [windowSet]
  refine ⟨fun i => if i = p.1 then (X : K[X]) ^ (p.2 : ℕ) else 0, ?_, ?_⟩
  · intro i
    by_cases h : i = p.1
    · subst h
      simp
    · simp [h, hω]
  · have hsum : (∑ i, (if i = p.1 then (X : K[X]) ^ (p.2 : ℕ) else 0) * f i)
        = (X : K[X]) ^ (p.2 : ℕ) * f p.1 := by
      rw [Finset.sum_eq_single p.1]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hmem
        exact absurd (Finset.mem_univ p.1) hmem
    rw [hsum, windowMatrix_row]

/-- **Claim 10** (`lem:window`), set form.  For `ω ≥ 1`, the row space of the window matrix
is exactly the set of coefficient windows of the sums `∑ i, g i * f i` with `deg (g i) < ω`. -/
theorem rowSpace_windowMatrix_eq_windowSet (f : ι → K[X]) (hω : 1 ≤ ω) :
    (Q1Subspace.rowSpace (windowMatrix f ω) : Set (Fin (2 * ω) → K)) = windowSet f ω := by
  apply Set.Subset.antisymm
  · intro v hv
    have hspan : Submodule.span K (Set.range (windowMatrix f ω)) ≤ windowSubmodule f hω :=
      Submodule.span_le.mpr (by
        rintro _ ⟨p, rfl⟩
        exact row_mem_windowSet f ω p)
    exact hspan hv
  · rintro v ⟨g, hg, rfl⟩
    exact toFn_sum_mem_rowSpace f hg

/-- **Claim 10** (`lem:window`), membership form: a coefficient vector lies in the row space
of `Z` exactly when it is the window of some `∑ i, g i * f i` with `deg (g i) < ω`. -/
theorem mem_rowSpace_iff_exists_window (f : ι → K[X]) (hω : 1 ≤ ω)
    (v : Fin (2 * ω) → K) :
    v ∈ Q1Subspace.rowSpace (windowMatrix f ω) ↔
      ∃ g : ι → K[X], (∀ i, (g i).natDegree < ω) ∧
        v = Polynomial.toFn (2 * ω) (∑ i, g i * f i) := by
  constructor
  · intro hv
    have hv' : v ∈ windowSet f ω := by
      rw [← rowSpace_windowMatrix_eq_windowSet f hω]
      exact hv
    exact hv'
  · rintro ⟨g, hg, rfl⟩
    exact toFn_sum_mem_rowSpace f hg

/-! ### Injectivity of the window map (item 5) -/

/-- Windows of length `N` distinguish polynomials of degree `< N`. -/
theorem toFn_injective_of_natDegree_lt {N : ℕ} {p q : K[X]}
    (hp : p.natDegree < N) (hq : q.natDegree < N)
    (h : Polynomial.toFn N p = Polynomial.toFn N q) : p = q := by
  classical
  rw [← Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hp,
    ← Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hq, h]

/-- **Claim 10, item 5.**  On polynomials of degree `< 2ω` the coefficient window is
injective. -/
theorem toFn_injOn_degree_lt_two_mul (ω : ℕ) :
    Set.InjOn (Polynomial.toFn (R := K) (2 * ω)) {p : K[X] | p.natDegree < 2 * ω} := by
  intro p hp q hq h
  exact toFn_injective_of_natDegree_lt hp hq h

end Q1Paper
