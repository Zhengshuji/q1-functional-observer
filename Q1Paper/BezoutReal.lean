
import Q1Paper.G2Assembly
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Q1Paper/BezoutReal.lean

The real-coefficient Bézout lemma of Paper I (Claim 9, labels `lem:bezout`, `sec:bezout`).

Paper I needs multipliers `g_i` that are *real* polynomials, because the identity
`∑ g_i f_i = 1` is substituted into a real system of polynomial equations.  The
declarations in `Q1Paper/BezoutDeg.lean` and `Q1Paper/G2Assembly.lean` are stated over an
arbitrary algebraically closed field and therefore do not give this.

Main results:

* `complexify` : complexification `p ↦ p.map (algebraMap ℝ ℂ)` of a real polynomial;
* `exists_complex_root_of_natDegree_pos` : the fundamental-theorem-of-algebra step (a real
  polynomial of positive degree has a complex root);
* `isCoprime_of_no_common_complex_root` : two real polynomials without a common complex
  root are coprime in `ℝ[X]` (steps 1–2 of the paper's proof);
* `exists_bezout_family_real` : Claim 9 — for a finite family `f_i ∈ ℝ[λ]` of degree at most
  `ω ≥ 1` without a common complex root there are real `g_i` with `∑ g_i f_i = 1` and
  `natDegree g_i < ω` (step 3).

The proof follows the paper.  One first chooses a combination `F = ∑ aᵢ fᵢ ≠ 0`, then a
second combination `G = ∑ bᵢ fᵢ` that avoids the finitely many complex roots of `F`
(hyperplane avoidance over `ℝ`, with the complex value split into real and imaginary
parts); then `F` and `G` are coprime over `ℝ[X]` by the fundamental theorem of algebra,
and the two-polynomial degree-bounded Bézout identity `exists_bezout_deg_lt` gives the
multipliers.
-/


open Polynomial

namespace Q1Paper

noncomputable section

/-- Complexification of a real polynomial. -/
abbrev complexify (p : ℝ[X]) : ℂ[X] := p.map (algebraMap ℝ ℂ)

lemma complexify_injective : Function.Injective complexify :=
  Polynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective

lemma complexify_ne_zero {p : ℝ[X]} : complexify p ≠ 0 ↔ p ≠ 0 :=
  Polynomial.map_ne_zero_iff Complex.ofReal_injective

/-- Evaluation of a complexified real polynomial at a real point. -/
lemma eval_complexify_ofReal (p : ℝ[X]) (x : ℝ) :
    (complexify p).eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  have h : (x : ℂ) = algebraMap ℝ ℂ x := rfl
  rw [h, Polynomial.eval₂_at_apply]
  rfl

/-- Fundamental theorem of algebra, in the form needed below: a real polynomial of
positive degree has a complex root. -/
lemma exists_complex_root_of_natDegree_pos {p : ℝ[X]} (hp : p ≠ 0) (hdeg : 0 < p.natDegree) :
    ∃ z : ℂ, (complexify p).IsRoot z := by
  have hmap0 : complexify p ≠ 0 := complexify_ne_zero.mpr hp
  have hnd : (complexify p).natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective p
  have hdeg' : 0 < (complexify p).degree := by
    rw [Polynomial.degree_eq_natDegree hmap0, hnd]
    exact_mod_cast hdeg
  exact Complex.exists_root hdeg'

/-- Two real polynomials without a common complex root are coprime in `ℝ[X]`.

This is steps 1–2 of the proof of the paper's Bézout claim: a common divisor of positive
degree would have a complex root, which would then be a common complex root. -/
theorem isCoprime_of_no_common_complex_root {F G : ℝ[X]} (hF : F ≠ 0)
    (h : ∀ z : ℂ, ¬ ((complexify F).IsRoot z ∧ (complexify G).IsRoot z)) :
    IsCoprime F G := by
  classical
  set d := EuclideanDomain.gcd F G with hd
  have hdvdF : d ∣ F := EuclideanDomain.gcd_dvd_left F G
  have hdvdG : d ∣ G := EuclideanDomain.gcd_dvd_right F G
  have hd0 : d ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := hdvdF
    rw [h0] at hq
    exact hF (by rw [hq]; simp)
  have hnat : d.natDegree = 0 := by
    by_contra hne
    have hpos : 0 < d.natDegree := Nat.pos_of_ne_zero hne
    obtain ⟨z, hz⟩ := exists_complex_root_of_natDegree_pos hd0 hpos
    have hz' : (complexify d).eval z = 0 := hz
    have hmul : ∀ q : ℝ[X], complexify (d * q) = complexify d * complexify q := by
      intro q
      simp [Polynomial.map_mul]
    have hzF : (complexify F).IsRoot z := by
      obtain ⟨q, hq⟩ := hdvdF
      rw [hq, hmul q]
      show ((complexify d) * (complexify q)).eval z = 0
      rw [Polynomial.eval_mul, hz', zero_mul]
    have hzG : (complexify G).IsRoot z := by
      obtain ⟨q, hq⟩ := hdvdG
      rw [hq, hmul q]
      show ((complexify d) * (complexify q)).eval z = 0
      rw [Polynomial.eval_mul, hz', zero_mul]
    exact h z ⟨hzF, hzG⟩
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hnat
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0] at hc
    exact hd0 (by simpa using hc.symm)
  have hgcd : d = F * EuclideanDomain.gcdA F G + G * EuclideanDomain.gcdB F G := by
    rw [hd]
    exact EuclideanDomain.gcd_eq_gcd_ab F G
  refine ⟨C c⁻¹ * EuclideanDomain.gcdA F G, C c⁻¹ * EuclideanDomain.gcdB F G, ?_⟩
  have hone : C c⁻¹ * d = 1 := by
    rw [← hc, ← C_mul, inv_mul_cancel₀ hc0, C_1]
  calc C c⁻¹ * EuclideanDomain.gcdA F G * F
        + C c⁻¹ * EuclideanDomain.gcdB F G * G
      = C c⁻¹ * (F * EuclideanDomain.gcdA F G + G * EuclideanDomain.gcdB F G) := by
        ring
    _ = C c⁻¹ * d := by rw [hgcd]
    _ = 1 := hone

/-- Bézout identity for two real polynomials without a common complex root. -/
theorem exists_bezout_of_no_common_complex_root {F G : ℝ[X]} (hF : F ≠ 0)
    (h : ∀ z : ℂ, ¬ ((complexify F).IsRoot z ∧ (complexify G).IsRoot z)) :
    ∃ u v : ℝ[X], u * F + v * G = 1 :=
  isCoprime_of_no_common_complex_root hF h

section family

variable {ι : Type*} [Fintype ι]

/-- The `ℝ`-linear map sending a coefficient vector `b` to the complex number
`∑ i, bᵢ • fᵢ(z)` (with the real scalar action of `ℝ` on `ℂ`). -/
def combC (f : ι → ℝ[X]) (z : ℂ) : (ι → ℝ) →ₗ[ℝ] ℂ :=
  ∑ i, (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight ((complexify (f i)).eval z)

lemma combC_apply (f : ι → ℝ[X]) (z : ℂ) (b : ι → ℝ) :
    combC f z b = ∑ i, (b i) • (complexify (f i)).eval z := by
  classical
  simp [combC, LinearMap.sum_apply]

lemma combC_single [DecidableEq ι] (f : ι → ℝ[X]) (z : ℂ) (i : ι) :
    combC f z (Pi.single i 1) = (complexify (f i)).eval z := by
  classical
  rw [combC_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

/-- Real part of `combC f z`. -/
def reComb (f : ι → ℝ[X]) (z : ℂ) : (ι → ℝ) →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp (combC f z)

/-- Imaginary part of `combC f z`. -/
def imComb (f : ι → ℝ[X]) (z : ℂ) : (ι → ℝ) →ₗ[ℝ] ℝ :=
  Complex.imCLM.toLinearMap.comp (combC f z)

lemma reComb_apply (f : ι → ℝ[X]) (z : ℂ) (b : ι → ℝ) :
    reComb f z b = (combC f z b).re := rfl

lemma imComb_apply (f : ι → ℝ[X]) (z : ℂ) (b : ι → ℝ) :
    imComb f z b = (combC f z b).im := rfl

lemma reComb_single [DecidableEq ι] (f : ι → ℝ[X]) (z : ℂ) (i : ι) :
    reComb f z (Pi.single i 1) = ((complexify (f i)).eval z).re := by
  rw [reComb_apply, combC_single]

lemma imComb_single [DecidableEq ι] (f : ι → ℝ[X]) (z : ℂ) (i : ι) :
    imComb f z (Pi.single i 1) = ((complexify (f i)).eval z).im := by
  rw [imComb_apply, combC_single]

/-- Evaluation of a complexified linear combination of a real family. -/
lemma eval_complexify_sum (f : ι → ℝ[X]) (b : ι → ℝ) (z : ℂ) :
    (complexify (∑ i, C (b i) * f i)).eval z = combC f z b := by
  classical
  rw [combC_apply]
  simp only [complexify, Polynomial.map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C]
  rw [Algebra.smul_def]

/-- Hyperplane avoidance over `ℝ`, with complex values: given a family with no common
complex root, and a nonzero real combination `F` of it, some real combination `G` of the
family does not vanish at any complex root of `F`. -/
lemma exists_avoid_complex_roots (f : ι → ℝ[X])
    (hroot : ∀ z : ℂ, ∃ i, (complexify (f i)).eval z ≠ 0)
    {F : ℝ[X]} (hF : F ≠ 0) :
    ∃ b : ι → ℝ, ∀ z : ℂ, (complexify F).IsRoot z → combC f z b ≠ 0 := by
  classical
  have hfin : Set.Finite {z : ℂ | (complexify F).IsRoot z} :=
    finite_setOfPred_isRoot (complexify_ne_zero.mpr hF)
  set s : Finset ℂ := hfin.toFinset with hs
  have hmem : ∀ z : ℂ, (complexify F).IsRoot z ↔ z ∈ s := by
    intro z
    simp only [hs, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  -- at every complex number, one of the real and imaginary parts is a nonzero functional
  have hpoint : ∀ z : ℂ, reComb f z ≠ 0 ∨ imComb f z ≠ 0 := by
    intro z
    obtain ⟨i, hi⟩ := hroot z
    by_contra hcon
    push Not at hcon
    obtain ⟨hre, him⟩ := hcon
    have h1 : ((complexify (f i)).eval z).re = 0 := by
      rw [← reComb_single f z i, hre]
      rfl
    have h2 : ((complexify (f i)).eval z).im = 0 := by
      rw [← imComb_single f z i, him]
      rfl
    exact hi (Complex.ext h1 h2)
  -- pick, for every root, one of the two nonzero functionals
  have hex : ∀ z ∈ s, ∃ L : (ι → ℝ) →ₗ[ℝ] ℝ,
      L ≠ 0 ∧ (L = reComb f z ∨ L = imComb f z) := by
    intro z _
    rcases hpoint z with hre | him
    · exact ⟨reComb f z, hre, Or.inl rfl⟩
    · exact ⟨imComb f z, him, Or.inr rfl⟩
  choose ell hell using hex
  let ell' : {z // z ∈ s} → (ι → ℝ) →ₗ[ℝ] ℝ := fun zs => ell zs.1 zs.2
  have hell' : ∀ zs : {z // z ∈ s}, ell' zs ≠ 0 := by
    intro zs
    exact (hell zs.1 zs.2).1
  obtain ⟨b, hb⟩ := exists_forall_apply_ne_zero s.attach ell' (fun zs _ => hell' zs)
  refine ⟨b, ?_⟩
  intro z hz
  have hzs : z ∈ s := (hmem z).mp hz
  have hb' : ell' ⟨z, hzs⟩ b ≠ 0 := hb ⟨z, hzs⟩ (Finset.mem_attach s ⟨z, hzs⟩)
  intro hzero
  apply hb'
  have hre : reComb f z b = 0 := by simp [reComb_apply, hzero]
  have him : imComb f z b = 0 := by simp [imComb_apply, hzero]
  rcases (hell z hzs).2 with h | h
  · rw [show ell' ⟨z, hzs⟩ = reComb f z from h]
    exact hre
  · rw [show ell' ⟨z, hzs⟩ = imComb f z from h]
    exact him

/-- **Claim 9 of Paper I** (`lem:bezout`): let `f₁,…,f_s ∈ ℝ[λ]` have degree at most `ω`
and no common complex root.  Then there are *real* polynomials `g_i` with
`natDegree g_i < ω` and `∑ i, g_i f_i = 1`. -/
theorem exists_bezout_family_real {f : ι → ℝ[X]} {ω : ℕ}
    (hω : 1 ≤ ω) (hdeg : ∀ i, (f i).natDegree ≤ ω)
    (hroot : ∀ z : ℂ, ∃ i, (complexify (f i)).eval z ≠ 0) :
    ∃ g : ι → ℝ[X], (∑ i, g i * f i) = 1 ∧ ∀ i, (g i).natDegree < ω := by
  classical
  have hreal : ∀ x : ℝ, ∃ i, (f i).eval x ≠ 0 := by
    intro x
    obtain ⟨i, hi⟩ := hroot (x : ℂ)
    exact ⟨i, fun hx => hi (by rw [eval_complexify_ofReal, hx]; simp)⟩
  obtain ⟨a, ha⟩ := exists_ne_zero_linearCombination f hreal
  set F : ℝ[X] := ∑ i, C (a i) * f i with hF
  have hFdeg : F.natDegree ≤ ω := natDegree_sum_C_mul_le f a ω hdeg
  obtain ⟨b, hb⟩ := exists_avoid_complex_roots f hroot ha
  set G : ℝ[X] := ∑ i, C (b i) * f i with hG
  have hGdeg : G.natDegree ≤ ω := natDegree_sum_C_mul_le f b ω hdeg
  have hno : ∀ z : ℂ, ¬ ((complexify F).IsRoot z ∧ (complexify G).IsRoot z) := by
    intro z hz
    have h1 : combC f z b ≠ 0 := hb z hz.1
    have hz2 : (complexify G).eval z = 0 := hz.2
    rw [hG, eval_complexify_sum] at hz2
    exact h1 hz2
  have hcop : IsCoprime F G := isCoprime_of_no_common_complex_root ha hno
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
          ≤ (C (a i) : ℝ[X]).natDegree + u.natDegree := Polynomial.natDegree_mul_le
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
                  ≤ (C (a i) : ℝ[X]).natDegree + U.natDegree := Polynomial.natDegree_mul_le
                _ ≤ 0 + U.natDegree := by rw [Polynomial.natDegree_C]
                _ < ω := by omega
            · calc (C (b i) * V).natDegree
                  ≤ (C (b i) : ℝ[X]).natDegree + V.natDegree := Polynomial.natDegree_mul_le
                _ ≤ 0 + V.natDegree := by rw [Polynomial.natDegree_C]
                _ < ω := by omega

end family

end

end Q1Paper
