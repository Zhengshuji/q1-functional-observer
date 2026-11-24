
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Q1Paper/RankIdentity.lean

The compression identity of the paper, abstract form:

  finrank (range (f.prod g)) = finrank (range f) + finrank (map g (ker f)),

for `f.prod g : E →ₗ[K] F × G`, `x ↦ (f x, g x)`.  This is the linear-map
counterpart of

  rank [J; M] = rank J + rank (M N_J),   N_J a basis of ker J,

the identity through which every compression step of the paper passes.
-/


open Module LinearMap

namespace Q1Paper

variable {K E F G : Type*}
  [Field K]
  [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
  [AddCommGroup G] [Module K G]

/-- The restriction of `g` to `ker f`. -/
def restrictToKer (f : E →ₗ[K] F) (g : E →ₗ[K] G) : (LinearMap.ker f) →ₗ[K] G :=
  g.comp (LinearMap.ker f).subtype

/-- Its range is the image of `ker f` under `g`. -/
theorem range_restrictToKer (f : E →ₗ[K] F) (g : E →ₗ[K] G) :
    LinearMap.range (restrictToKer f g) = Submodule.map g (LinearMap.ker f) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : E), x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The kernel of the restriction is the intersection of the two kernels. -/
def kerRestrictEquiv (f : E →ₗ[K] F) (g : E →ₗ[K] G) :
    ↥(LinearMap.ker (restrictToKer f g)) ≃ₗ[K]
      ↥(LinearMap.ker f ⊓ LinearMap.ker g) where
  toFun x :=
    ⟨(x : E),
      ⟨(x : ↥(LinearMap.ker f)).2, by
        have hx : restrictToKer f g x = 0 := x.2
        simpa [restrictToKer] using hx⟩⟩
  invFun y :=
    ⟨⟨(y : E), y.2.1⟩, by
      have hy : g (y : E) = 0 := y.2.2
      simpa [restrictToKer] using hy⟩
  map_add' a b := by ext; rfl
  map_smul' c a := by ext; rfl
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl

/-- The compression identity, abstract form. -/
theorem finrank_range_prod [FiniteDimensional K E]
    (f : E →ₗ[K] F) (g : E →ₗ[K] G) :
    finrank K ↥(LinearMap.range (f.prod g)) =
      finrank K ↥(LinearMap.range f) +
        finrank K ↥(Submodule.map g (LinearMap.ker f)) := by
  have hker : LinearMap.ker (f.prod g) = LinearMap.ker f ⊓ LinearMap.ker g := by
    ext x
    simp [LinearMap.mem_ker, LinearMap.prod_apply, Submodule.mem_inf]
  have h1 : finrank K E =
      finrank K ↥(LinearMap.range (f.prod g)) +
        finrank K ↥(LinearMap.ker f ⊓ LinearMap.ker g) := by
    rw [← hker]
    exact (LinearMap.finrank_range_add_finrank_ker (f := f.prod g)).symm
  have h2 : finrank K E =
      finrank K ↥(LinearMap.range f) + finrank K ↥(LinearMap.ker f) :=
    (LinearMap.finrank_range_add_finrank_ker (f := f)).symm
  have h3 : finrank K ↥(LinearMap.ker f) =
      finrank K ↥(Submodule.map g (LinearMap.ker f)) +
        finrank K ↥(LinearMap.ker f ⊓ LinearMap.ker g) := by
    rw [← range_restrictToKer f g, ← (kerRestrictEquiv f g).finrank_eq]
    exact (LinearMap.finrank_range_add_finrank_ker (f := restrictToKer f g)).symm
  omega

end Q1Paper
