/-
Q1Paper/Compression.lean

Lemma A, algebraic core: the compressed pair (H, H_A) and the
kernel-inclusion criterion on the invisible subspace K0.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Module LinearMap

namespace Q1Paper

variable {K E F : Type*}
  [Field K]
  [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- The inclusion of the invisible subspace `K0` into the state space. -/
def incl (K0 : Submodule K E) : K0 →ₗ[K] E :=
  K0.subtype

/-- The compressed observer matrix `H = L N`. -/
def compressedH (L : E →ₗ[K] F) (K0 : Submodule K E) : K0 →ₗ[K] F :=
  L.comp (incl K0)

/-- The compressed pencil constant term `H_A = L A N`. -/
def compressedHA (L : E →ₗ[K] F) (A : E →ₗ[K] E)
    (K0 : Submodule K E) : K0 →ₗ[K] F :=
  L.comp (A.comp (incl K0))

/-- Lemma A(i), abstract form: on the invisible subspace `K0`, the kernel
inclusion for the compressed pair is exactly the kernel inclusion for
`L` and `L A` intersected with `K0`. -/
theorem ker_compressed_iff (L : E →ₗ[K] F) (A : E →ₗ[K] E)
    (K0 : Submodule K E) :
    LinearMap.ker (compressedH L K0) ≤ LinearMap.ker (compressedHA L A K0) ↔
      (LinearMap.ker L ⊓ K0) ≤ (LinearMap.ker (L.comp A) ⊓ K0) := by
  constructor
  · intro h x hx
    rcases hx with ⟨hLx, hxK0⟩
    have hxH : (⟨x, hxK0⟩ : K0) ∈ LinearMap.ker (compressedH L K0) := by
      simpa [compressedH, incl, LinearMap.mem_ker] using hLx
    have hxHA : (⟨x, hxK0⟩ : K0) ∈ LinearMap.ker (compressedHA L A K0) := h hxH
    have hLAx : (L.comp A) x = 0 := by
      simpa [compressedHA, incl, LinearMap.mem_ker] using hxHA
    exact ⟨hLAx, hxK0⟩
  · intro h k hk
    have hkL : L (k : E) = 0 := by
      simpa [compressedH, incl, LinearMap.mem_ker] using hk
    have hkK0 : (k : E) ∈ K0 := k.property
    have hk' : (k : E) ∈ (LinearMap.ker L ⊓ K0) := ⟨hkL, hkK0⟩
    have hk'' : (k : E) ∈ (LinearMap.ker (L.comp A) ⊓ K0) := h hk'
    have hLAk : (L.comp A) (k : E) = 0 := hk''.1
    simpa [compressedHA, incl, LinearMap.mem_ker] using hLAk

end Q1Paper
