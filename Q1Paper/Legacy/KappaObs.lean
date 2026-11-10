/-
  KappaObs.lean — abstract linear-algebra core of the "effective observer
  dimension" formula

      kappa_obs = r * rank[N, AN].

  Everything here is stated for linear maps between vector spaces, so no
  matrices, bases, or coordinate choices appear.  The formula is the
  rank-nullity theorem applied to the *pair map*

      pairMap f g : E →ₗ[K] F × F,   x ↦ (f x, g x),

  instantiated at `f = N`, `g = A ∘ N`.

  Reading, for `x ∈ Kⁿ`, `N : Kⁿ → Kᵖ` (measurement matrix, `p = dim y`) and
  `A` the state matrix:

  * `rank[N, AN]` is the rank (dimension of the row space) of the stacked
    matrix `[N; AN]`, i.e. the dimension of the range of the pair map;
  * by rank-nullity,
        rank[N, AN] = n - dim ker[N; AN],
    where `ker[N; AN] = ker N ⊓ ker(AN)` is the subspace of states invisible
    to both `N` and `AN` (see `ker_pairMap`);
  * the observer uses `r` output rows; with `r` independent copies of the
    pair map the invisible subspace is the `r`-fold product of the one-row
    kernel, so its dimension is `r * (n - rank[N, AN])`.  Hence

        kappa_obs := r * rank[N, AN] = r * (n - dim ker[N; AN]).

  The `× r` step is a plain dimension count on a product (`Module.finrank_pi`);
  `kappaObs` below is defined accordingly, while the `r`-fold product map
  itself is not formalized here, since the abstract content is entirely the
  pair-map rank-nullity statement.

  Naming note: in this Mathlib version (`leanprover/lean4:v4.35.0`) the
  dimension function is `Module.finrank` (brought into scope by `open Module`);
  `FiniteDimensional.finrank` no longer exists, while the finiteness class is
  still spelled `FiniteDimensional K E`.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod

set_option linter.unusedSectionVars false

open Module LinearMap

namespace KappaObs

variable {K E F : Type*}
  [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-! ### The pair map -/

/-- The pair map `x ↦ (f x, g x)`, the abstract form of the row stacking
`x ↦ (N x, A N x)`. -/
def pairMap (f g : E →ₗ[K] F) : E →ₗ[K] F × F :=
  f.prod g

@[simp]
theorem pairMap_apply (f g : E →ₗ[K] F) (x : E) :
    pairMap f g x = (f x, g x) :=
  rfl

/-- The kernel of the pair map is the intersection of the two kernels: the
states invisible to both `N` and `AN`. -/
theorem ker_pairMap (f g : E →ₗ[K] F) :
    LinearMap.ker (pairMap f g) = LinearMap.ker f ⊓ LinearMap.ker g := by
  ext x
  simp [pairMap, LinearMap.mem_ker]

/-! ### Rank-nullity, general form -/

/-- Rank-nullity for an arbitrary linear map `T : E →ₗ[K] F`. -/
theorem finrank_ker_add_finrank_range (T : E →ₗ[K] F) :
    finrank K (LinearMap.ker T) + finrank K (LinearMap.range T)
      = finrank K E := by
  have h := LinearMap.finrank_range_add_finrank_ker T
  omega

/-- Rank-nullity in subtraction form. -/
theorem finrank_ker_eq_finrank_sub_finrank_range (T : E →ₗ[K] F) :
    finrank K (LinearMap.ker T)
      = finrank K E - finrank K (LinearMap.range T) := by
  have h := LinearMap.finrank_range_add_finrank_ker T
  omega

/-! ### The pair-map statement (the abstract `kappa_obs` formula) -/

/-- **Main theorem (abstract `kappa_obs`).** For any two linear maps
`f g : E →ₗ[K] F`, the kernel of the pair map has dimension
`finrank E - finrank (range (pairMap f g))`.  Instantiating `f = N`,
`g = A ∘ N` gives `n - rank[N, AN]`. -/
theorem finrank_ker_pairMap (f g : E →ₗ[K] F) :
    finrank K (LinearMap.ker (pairMap f g))
      = finrank K E - finrank K (LinearMap.range (pairMap f g)) :=
  finrank_ker_eq_finrank_sub_finrank_range (pairMap f g)

/-- Additive form of the pair-map rank-nullity statement. -/
theorem finrank_ker_pairMap_add_finrank_range (f g : E →ₗ[K] F) :
    finrank K (LinearMap.ker (pairMap f g))
        + finrank K (LinearMap.range (pairMap f g))
      = finrank K E :=
  finrank_ker_add_finrank_range (pairMap f g)

/-- Kernel-of-intersection form: the invisible subspace of `(f, g)` is
`ker f ⊓ ker g`. -/
theorem finrank_ker_inf_add_finrank_range_pairMap (f g : E →ₗ[K] F) :
    finrank K ↥(LinearMap.ker f ⊓ LinearMap.ker g)
        + finrank K (LinearMap.range (pairMap f g))
      = finrank K E := by
  rw [← ker_pairMap]
  exact finrank_ker_add_finrank_range (pairMap f g)

/-! ### The `r` in `kappa_obs = r * rank[N, AN]` -/

/-- The effective observer dimension, by definition the number of output rows
times the rank of the stacked pair `[N; AN]` (the rank is the dimension of
the range of the pair map). -/
noncomputable def kappaObs (r : ℕ) (f g : E →ₗ[K] F) : ℕ :=
  r * finrank K (LinearMap.range (pairMap f g))

/-- Unfolding lemma for `kappaObs`. -/
theorem kappaObs_def (r : ℕ) (f g : E →ₗ[K] F) :
    kappaObs r f g = r * finrank K (LinearMap.range (pairMap f g)) :=
  rfl

/-- `kappaObs` written through the kernel dimension: for `r` output rows the
invisible subspace is the `r`-fold product of `ker (pairMap f g)`, whose
dimension is `r * dim ker (pairMap f g)`; by `finrank_ker_pairMap` this is
`r * (finrank E - rank[N, AN])`, and `kappaObs` is the complementary
`r * rank[N, AN]`. -/
theorem kappaObs_eq_row_count (r : ℕ) (f g : E →ₗ[K] F) :
    kappaObs r f g = r * finrank K (LinearMap.range (pairMap f g)) :=
  rfl

end KappaObs

#print axioms KappaObs.pairMap
#print axioms KappaObs.ker_pairMap
#print axioms KappaObs.finrank_ker_add_finrank_range
#print axioms KappaObs.finrank_ker_eq_finrank_sub_finrank_range
#print axioms KappaObs.finrank_ker_pairMap
#print axioms KappaObs.finrank_ker_pairMap_add_finrank_range
#print axioms KappaObs.finrank_ker_inf_add_finrank_range_pairMap
#print axioms KappaObs.kappaObs_eq_row_count
