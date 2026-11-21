/-
Q1Paper/HyperplaneC2.lean

The `c = 2` layer, `K`-split part: the two elementary facts behind the corrected fibre
(`workspace/augmentation_family/attempts/393_c2_fibre_and_base.md`, Proposition 2).

With `D ≤ K` (the kernel direction `D = ker H = K ⊓ Vᗮ`) and the ansatz `V = (K ⊓ Dᗮ) ⊔ W`
where `W ≤ Kᗮ` (the `K`-split design `V = D^{⊥_K} ⊕ W`), one has

    V ⊓ K = K ⊓ Dᗮ                              (`sup_inf_eq_left_of_le_orthogonal`)
    finrank V = finrank (K ⊓ Dᗮ) + finrank W     (`finrank_sup_of_disjoint_of_le_orthogonal`)

The second is the bookkeeping `q = (k - c) + t` of the layer, with `c = dim D` and `t = dim W`.
-/

import Q1Paper.HyperplaneFibre
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Module

namespace Q1Paper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The `K`-part of the `K`-split design.**  If `D ≤ K`, `W ≤ Kᗮ` and `V = (K ⊓ Dᗮ) ⊔ W`, then
`V ⊓ K = K ⊓ Dᗮ`: the `W` summand is orthogonal to `K`, the other summand lives in `K`, so nothing
outside `K ⊓ Dᗮ` survives the intersection. -/
theorem sup_inf_eq_left_of_le_orthogonal {K D W : Submodule ℝ E}
    (hDK : D ≤ K) (hW : W ≤ Kᗮ) :
    ((K ⊓ Dᗮ) ⊔ W) ⊓ K = K ⊓ Dᗮ := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxsup, hxK⟩ := hx
    rw [Submodule.mem_sup] at hxsup
    obtain ⟨a, ha, w, hw, haw⟩ := hxsup
    have haK : a ∈ K := (Submodule.mem_inf.mp ha).1
    have haD : a ∈ Dᗮ := (Submodule.mem_inf.mp ha).2
    have hwK : w ∈ K := by
      have hwx : w = x - a := by rw [← haw]; abel
      rw [hwx]
      exact K.sub_mem hxK haK
    have hwKperp : w ∈ Kᗮ := hW hw
    have hw0 : w = 0 := by
      have h0 : inner ℝ w w = 0 := Submodule.inner_right_of_mem_orthogonal hwK hwKperp
      exact inner_self_eq_zero.mp h0
    have hxeq : x = a := by rw [← haw, hw0, add_zero]
    rw [Submodule.mem_inf]
    exact ⟨by rw [hxeq]; exact haK, by rw [hxeq]; exact haD⟩
  · intro x hx
    rw [Submodule.mem_inf]
    exact ⟨Submodule.mem_sup_left hx, (Submodule.mem_inf.mp hx).1⟩

/-- **`W` is disjoint from `K ⊓ Dᗮ`** when `W ≤ Kᗮ`: the intersection lies in `K ⊓ Kᗮ`, and
`inner ℝ x x = 0` forces `x = 0`. -/
theorem disjoint_of_le_orthogonal (K D W : Submodule ℝ E) (hW : W ≤ Kᗮ) :
    Disjoint (K ⊓ Dᗮ) W := by
  rw [disjoint_iff_inf_le]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxKD, hxW⟩ := hx
  have hxK : x ∈ K := (Submodule.mem_inf.mp hxKD).1
  have h0 : inner ℝ x x = 0 :=
    Submodule.inner_right_of_mem_orthogonal hxK (hW hxW)
  have hx0 : x = 0 := inner_self_eq_zero.mp h0
  rw [hx0]
  exact Submodule.zero_mem _

/-- **The dimension bookkeeping.**  With `W ≤ Kᗮ` the summands are disjoint, so the rank of the
sum is the sum of the ranks: `finrank V = finrank (K ⊓ Dᗮ) + finrank W`, i.e. `q = (k - c) + t`. -/
theorem finrank_sup_of_disjoint_of_le_orthogonal (K D W : Submodule ℝ E) (hW : W ≤ Kᗮ) :
    finrank ℝ ↥((K ⊓ Dᗮ) ⊔ W) = finrank ℝ ↥(K ⊓ Dᗮ) + finrank ℝ ↥W := by
  have hdisj : Disjoint (K ⊓ Dᗮ) W := disjoint_of_le_orthogonal K D W hW
  have h := Submodule.finrank_sup_add_finrank_inf_eq (K ⊓ Dᗮ) W
  have hinf : (K ⊓ Dᗮ) ⊓ W = ⊥ := by
    rw [← le_bot_iff]
    exact disjoint_iff_inf_le.mp hdisj
  rw [hinf] at h
  rw [finrank_bot] at h
  omega

end Q1Paper
