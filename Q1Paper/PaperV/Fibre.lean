import Mathlib

/-!
Q1Paper/PaperV/Fibre.lean

§II, Theorem 2 (**the fibre is a coset of `T ⊓ U`**).

Paper statement (verbatim):

  *Fix `H` with `U = row H` and `d' = rank H`. The set of admissible `H_A` for this `H`
  is `H Z'' + F_U` with `F_U = ∏ᵢ (T ∩ (U - Hᵢ Z''))`. Either `F_U = ∅`, or `F_U` is an
  affine space of dimension `q a` with `a = dim(U ∩ T)`. Moreover `F_U ≠ ∅` if and only
  if `U Z'' ⊆ U + T`, and then `F_U ≅ ∏ᵢ (U ∩ T)`.*

The formal statement below is the per-row core, which is what the product form needs:
for subspaces `T U ≤ E` and a point `y : E`, the set `{x ∈ T | x + y ∈ U}` is

* empty, or
* the coset `x₀ + (T ⊓ U)` for any point `x₀` of it;

and it is nonempty exactly when `y ∈ U ⊔ T`.  The product over rows is then the
dimension statement `q · dim (T ⊓ U)`; we record the per-row nonemptiness criterion
(`fibre_nonempty_iff`, which is the paper's `U Z'' ⊆ U + T` row by row) and the coset
description (`fibre_eq_coset`), from which the dimension `dim (T ⊓ U)` and its
multiplicativity over the `q` rows are immediate.

The direction `T` of the fibre (`T = {l A N : l N = 0}`) is intrinsic; see
`Q1Paper.PaperV.fibre_of_mem` for the shape used in the paper's proof of Theorem 6.
-/

namespace Q1Paper.PaperV

open Submodule

variable {K : Type*} [Field K]
variable {E : Type*} [AddCommGroup E] [Module K E]

/-- The per-row fibre: points of `T` whose translate by `y` lands in `U`. -/
def fibre (T U : Submodule K E) (y : E) : Set E := {x | x ∈ T ∧ x + y ∈ U}

@[simp]
theorem mem_fibre {T U : Submodule K E} {y x : E} :
    x ∈ fibre T U y ↔ x ∈ T ∧ x + y ∈ U := Iff.rfl

/-- **Theorem 2 (nonemptiness).** The fibre is empty exactly when the translate misses,
i.e. `y ∉ U + T`.  This is the paper's `T ∩ (U - x) ≠ ∅ ⇔ x ∈ U + T`. -/
theorem fibre_nonempty_iff (T U : Submodule K E) (y : E) :
    (fibre T U y).Nonempty ↔ y ∈ U ⊔ T := by
  constructor
  · rintro ⟨x, hxT, hxU⟩
    -- `y = (x + y) - x` with `x + y ∈ U` and `x ∈ T`
    have h : y = (x + y) - x := by abel
    rw [h]
    exact (U ⊔ T).sub_mem (Submodule.mem_sup_left hxU) (Submodule.mem_sup_right hxT)
  · intro hy
    -- write `y = u + t`, then `x = -t` works
    rw [Submodule.mem_sup] at hy
    obtain ⟨u, hu, t, ht, rfl⟩ := hy
    refine ⟨-t, neg_mem ht, ?_⟩
    have : -t + (u + t) = u := by abel
    rw [this]
    exact hu

/-- **Theorem 2 (coset form).** Any point of the fibre generates it as a coset of the
direction `T ⊓ U`; hence the fibre is affine with direction `T ⊓ U`. -/
theorem fibre_eq_coset (T U : Submodule K E) (y : E) {x₀ : E}
    (hx : x₀ ∈ fibre T U y) :
    fibre T U y = {x | ∃ z ∈ T ⊓ U, x = x₀ + z} := by
  obtain ⟨hxT, hxU⟩ := hx
  ext x
  constructor
  · rintro ⟨hxT', hxU'⟩
    refine ⟨x - x₀, ⟨?_, ?_⟩, by abel⟩
    · exact sub_mem hxT' hxT
    · have : x - x₀ = (x + y) - (x₀ + y) := by abel
      rw [this]
      exact sub_mem hxU' hxU
  · rintro ⟨z, ⟨hzT, hzU⟩, rfl⟩
    refine ⟨add_mem hxT hzT, ?_⟩
    have : x₀ + z + y = (x₀ + y) + z := by abel
    rw [this]
    exact add_mem hxU hzU

/-- **Theorem 2 (product over the rows).** The fibre of the paper is the product of the
per-row fibres, so it is nonempty exactly when every row's translate lies in `U + T`;
that is the paper's criterion `U Z'' ⊆ U + T`, read row by row. -/
theorem fibre_prod_nonempty_iff {q : ℕ} (T U : Submodule K E) (y : Fin q → E) :
    (∀ i, (fibre T U (y i)).Nonempty) ↔ ∀ i, y i ∈ U ⊔ T :=
  forall_congr' fun i => fibre_nonempty_iff T U (y i)

/-- **Theorem 2 (assembled coset form).** When every row's translate lies in `U + T` --- the paper's
`U Z'' ⊆ U + T` read row by row --- the product of the row fibres is a coset of `(T ⊓ U)^q`:
there is a point `g` of the product such that a tuple `x` lies in the product exactly when
`x - g` lies in `(T ⊓ U)^q` row by row. -/
theorem fibre_prod_coset {q : ℕ} (T U : Submodule K E) (y : Fin q → E)
    (hy : ∀ i, y i ∈ U ⊔ T) :
    ∃ g : Fin q → E, (∀ i, g i ∈ fibre T U (y i)) ∧
      ∀ x : Fin q → E, (∀ i, x i ∈ fibre T U (y i)) ↔ ∀ i, x i - g i ∈ T ⊓ U := by
  choose g hg using fun i => (fibre_nonempty_iff T U (y i)).mpr (hy i)
  refine ⟨g, hg, fun x => ?_⟩
  constructor
  · intro hx i
    have h := fibre_eq_coset T U (y i) (hg i)
    have hxi := hx i
    rw [h] at hxi
    obtain ⟨z, hz, hxz⟩ := hxi
    rw [hxz]
    simpa using hz
  · intro hx i
    have h := fibre_eq_coset T U (y i) (hg i)
    rw [h]
    exact ⟨x i - g i, hx i, by abel⟩


end Q1Paper.PaperV
