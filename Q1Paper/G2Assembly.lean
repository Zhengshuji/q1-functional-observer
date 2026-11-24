
import Q1Paper.BezoutDeg
import Q1Paper.HyperplaneAvoid

/-!
Q1Paper/G2Assembly.lean

The degree-bounded Bezout lemma for a family of polynomials (Lemma 4 of the paper),
assembled from the pieces:

* `exists_ne_zero_linearCombination`, `exists_ne_zero_with_finite_roots` (BezoutDeg);
* the hyperplane-avoidance lemma (HyperplaneAvoid);
* `isCoprime_of_no_common_root` and `exists_bezout_deg_lt` (BezoutDeg).

Over an algebraically closed field, a finite family with no common root and degrees at
most `ω ≥ 1` has a Bezout relation with all multipliers of `natDegree < ω`.
-/


open Polynomial

namespace Q1Paper

variable {K ι : Type*} [Field K] [Fintype ι]

/-- Evaluation of the linear combination `Σ bᵢ fᵢ` at `α`, as a linear functional in
the coefficients `b`. -/
def evalComb (f : ι → K[X]) (α : K) : (ι → K) →ₗ[K] K where
  toFun b := ∑ i, b i * (f i).eval α
  map_add' x y := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- The functional of a point where some member of the family does not vanish is
nonzero. -/
theorem evalComb_ne_zero (f : ι → K[X]) (α : K) (h : ∃ i, (f i).eval α ≠ 0) :
    evalComb f α ≠ 0 := by
  classical
  intro hzero
  obtain ⟨i, hi⟩ := h
  have happ : evalComb f α (Pi.single i 1) = (f i).eval α := by
    simp only [evalComb, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  have hz : evalComb f α (Pi.single i 1) = 0 := by
    rw [hzero]
    rfl
  rw [happ] at hz
  exact hi hz

/-- Degree of a linear combination, bounded by the largest degree of the family. -/
theorem natDegree_sum_C_mul_le (f : ι → K[X]) (b : ι → K) (ω : ℕ)
    (h : ∀ i, (f i).natDegree ≤ ω) :
    (∑ i, C (b i) * f i).natDegree ≤ ω := by
  classical
  by_cases hne : (∑ i, C (b i) * f i) = 0
  · rw [hne]
    simp
  · calc (∑ i, C (b i) * f i).natDegree
        ≤ (Finset.univ.sup (fun i => (C (b i) * f i).natDegree)) := by
          exact Polynomial.natDegree_sum_le _ _
      _ ≤ ω := by
          apply Finset.sup_le
          intro i _
          calc (C (b i) * f i).natDegree
              ≤ (C (b i)).natDegree + (f i).natDegree := Polynomial.natDegree_mul_le
            _ ≤ 0 + ω := by
                have := h i
                have hC : (C (b i) : K[X]).natDegree = 0 := Polynomial.natDegree_C _
                omega
            _ = ω := by omega


variable [IsAlgClosed K]

/-- The degree-bounded Bezout lemma for a family (Lemma 4 of the paper). -/
theorem exists_bezout_family {f : ι → K[X]} {ω : ℕ}
    (hω : 1 ≤ ω) (hdeg : ∀ i, (f i).natDegree ≤ ω)
    (hroot : ∀ x : K, ∃ i, (f i).eval x ≠ 0) :
    ∃ g : ι → K[X], (∑ i, g i * f i) = 1 ∧ ∀ i, (g i).natDegree < ω := by
  classical
  obtain ⟨a, ha⟩ := exists_ne_zero_linearCombination f hroot
  set F : K[X] := ∑ i, C (a i) * f i with hF
  have hFdeg : F.natDegree ≤ ω := natDegree_sum_C_mul_le f a ω hdeg
  have hfin : Set.Finite {x : K | IsRoot F x} := finite_setOfPred_isRoot ha
  set s : Finset K := hfin.toFinset with hs
  obtain ⟨b, hb⟩ : ∃ b : ι → K, ∀ α ∈ s, evalComb f α b ≠ 0 := by
    rcases Finset.eq_empty_or_nonempty s with hem | hne
    · refine ⟨fun _ => 0, ?_⟩
      intro α hα
      rw [hem] at hα
      exact absurd hα (by simp)
    · exact exists_forall_apply_ne_zero s (fun α => evalComb f α)
        (fun α _ => evalComb_ne_zero f α (hroot α))
  set G : K[X] := ∑ i, C (b i) * f i with hG
  have hGdeg : G.natDegree ≤ ω := natDegree_sum_C_mul_le f b ω hdeg
  have hGeval : ∀ α : K, eval α G = evalComb f α b := by
    intro α
    simp only [hG, evalComb, LinearMap.coe_mk, AddHom.coe_mk]
    rw [eval_finsetSum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [eval_mul, eval_C]
  have hno : ∀ x : K, ¬ (F.IsRoot x ∧ G.IsRoot x) := by
    intro x hx
    have hmem : x ∈ s := by
      rw [hs, Set.Finite.mem_toFinset]
      exact hx.1
    have h1 : evalComb f x b ≠ 0 := hb x hmem
    have h2 : eval x G = 0 := hx.2
    exact h1 (by rw [← hGeval x, h2])
  have hcop : IsCoprime F G := isCoprime_of_no_common_root ha hno
  by_cases hG0 : G = 0
  · obtain ⟨u, v, huv⟩ := hcop
    have hF1 : u * F = 1 := by
      rw [hG0, mul_zero, add_zero] at huv
      exact huv
    have hu0 : u ≠ 0 := by
      intro h
      rw [h] at hF1
      simp at hF1
    have huF : (u * F).natDegree = 0 := by rw [hF1]; simp
    have hmul : (u * F).natDegree = u.natDegree + F.natDegree :=
      Polynomial.natDegree_mul hu0 ha
    have hudeg : u.natDegree < ω := by omega
    refine ⟨fun i => C (a i) * u, ?_, ?_⟩
    · have hsum : (∑ i, (C (a i) * u) * f i) = u * F := by
        rw [hF]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [hsum, hF1]
    · intro i
      calc (C (a i) * u).natDegree
          ≤ (C (a i) : K[X]).natDegree + u.natDegree := Polynomial.natDegree_mul_le
        _ ≤ 0 + u.natDegree := by rw [Polynomial.natDegree_C]
        _ < ω := by omega
  · obtain ⟨U, V, hUV, hUdeg, hVdeg⟩ :=
      exists_bezout_deg_lt ha hG0 hω hFdeg hGdeg hcop
    refine ⟨fun i => C (a i) * U + C (b i) * V, ?_, ?_⟩
    · have hsum : (∑ i, (C (a i) * U + C (b i) * V) * f i) = U * F + V * G := by
        rw [hF, hG, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [hsum, hUV]
    · intro i
      calc (C (a i) * U + C (b i) * V).natDegree
          ≤ max (C (a i) * U).natDegree (C (b i) * V).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ < ω := by
            apply max_lt
            · calc (C (a i) * U).natDegree
                  ≤ (C (a i) : K[X]).natDegree + U.natDegree := Polynomial.natDegree_mul_le
                _ ≤ 0 + U.natDegree := by rw [Polynomial.natDegree_C]
                _ < ω := by omega
            · calc (C (b i) * V).natDegree
                  ≤ (C (b i) : K[X]).natDegree + V.natDegree := Polynomial.natDegree_mul_le
                _ ≤ 0 + V.natDegree := by rw [Polynomial.natDegree_C]
                _ < ω := by omega

end Q1Paper
