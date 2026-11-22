import Q1Paper.PaperI.MinorFamilyBridge

open Matrix Polynomial

namespace Q1Paper.PaperI

variable {K : Type*} [Field K]

/-- **Fibre grouping for a surjection with constant fibre cardinality.** -/
theorem sum_comp_eq_card_smul_sum {R S : Type*} [Fintype R] [Fintype S] [DecidableEq S]
    (Φ : R → S) (m : ℕ)
    (hm : ∀ s : S, Fintype.card {r : R // Φ r = s} = m)
    (h : S → K) :
    ∑ r : R, h (Φ r) = m • ∑ s : S, h s := by
  classical
  have hcard : ∀ s : S, (Finset.univ.filter (fun r : R => Φ r = s)).card = m := by
    intro s
    rw [← Fintype.card_subtype]
    exact hm s
  have hfib :
      (∑ s : S, (Finset.univ.filter (fun r : R => Φ r = s)).sum (fun r => h (Φ r)))
        = ∑ r : R, h (Φ r) :=
    Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := Φ) (f := fun r => h (Φ r)) (fun r _ => Finset.mem_univ _)
  rw [← hfib]
  calc (∑ s : S, (Finset.univ.filter (fun r : R => Φ r = s)).sum (fun r => h (Φ r)))
      = ∑ s : S, (Finset.univ.filter (fun r : R => Φ r = s)).sum (fun _ => h s) := by
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r hr => ?_
        rw [(Finset.mem_filter.mp hr).2]
    _ = ∑ s : S, m • h s := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_const, hcard s]
    _ = m • ∑ s : S, h s := by
        rw [Finset.smul_sum]

/-- **Signed fibre grouping**: a sign with square one does not change the sum. -/
theorem sum_sign_mul_sq_eq_card_smul_sum {R S : Type*} [Fintype R] [Fintype S] [DecidableEq S]
    (Φ : R → S) (m : ℕ)
    (hm : ∀ s : S, Fintype.card {r : R // Φ r = s} = m)
    (ε : R → K) (hε : ∀ r, ε r ^ 2 = 1) (v : S → K) :
    ∑ r : R, (ε r * v (Φ r)) * (ε r * v (Φ r)) = m • ∑ s : S, v s * v s := by
  have hfun : ∀ r : R, (ε r * v (Φ r)) * (ε r * v (Φ r)) = v (Φ r) * v (Φ r) := by
    intro r
    calc (ε r * v (Φ r)) * (ε r * v (Φ r))
        = (ε r * ε r) * (v (Φ r) * v (Φ r)) := by ring
      _ = v (Φ r) * v (Φ r) := by rw [← pow_two, hε r, one_mul]
  simp only [hfun]
  exact sum_comp_eq_card_smul_sum Φ m hm (fun s => v s * v s)

end Q1Paper.PaperI
