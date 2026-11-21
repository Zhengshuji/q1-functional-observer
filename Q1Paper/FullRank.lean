/-
Q1Paper/FullRank.lean

Paper item: Claim `sec4:lem:fullrank` of `paper/current/paper_III_hyperplane.tex`
("Full-rank leading coefficient; dichotomy on a chart").  This is the paper's main new lemma of
Section 4: a gcd computation performed at the generic parameter certifies the statement at *every*
parameter of the chart, and it is what turns the generic test of `sec4:thm:generic` into a verdict
on a whole chart.

Paper statement (verbatim).  Let `K` be a field, `X = (X₁,…,X_d)`, and let `m₁,…,m_t ∈ K[X,λ]`
satisfy `deg_λ m_i ≤ ω` and
  (★) for every `X ∈ 𝒳_I` there is `i` with `deg_λ m_i(X,·) = ω`.
If `deg_λ gcd(m₁,…,m_t) > 0` in `K(X)[λ]`, then for **every** `X₀` the specialized polynomials
`m_i(X₀,·)` have a nonconstant common factor.  In particular, on a chart of the layer exactly one
of the following holds: either `deg_λ gcd_I m_I = 0`, in which case the chart contains a good point
and its good points form a nonempty Zariski open subset; or `deg_λ gcd_I m_I > 0`, in which case
*every* point of the chart is bad.

Proof (the paper's, formalised below).  Let `g` be the gcd over the function field, taken
primitive in `K[X][λ]` by Gauss's lemma.  Fix `X₀`.  If `g(X₀,·) ≡ 0` then every
`m_i(X₀,·) = g(X₀,·)·h_i(X₀,·) ≡ 0`, contradicting (★).  If `g(X₀,·)` is a nonzero constant then
`deg_λ m_i(X₀,·) ≤ deg_λ h_i ≤ ω_i − deg_λ g ≤ ω − deg_λ g < ω`, again contradicting (★).  Hence
`g(X₀,·)` is nonzero, nonconstant, and divides every `m_i(X₀,·)`.

Dictionary.  `R` is the paper's coordinate ring `K[X₁,…,X_d]` (its fraction field is `K(X)`, denoted
`K` here), `m : ι → R[λ]` are the minors `m_I`, and `ω` is the paper's `ω`.  The declarations that
carry the argument:

* `Q1Paper.specialized_common_factor` — one point `X₀`: a common divisor `g ∈ R[λ]` of positive
  degree of all the `m_i` specialises to a nonconstant common factor, provided (★) holds at `X₀`.
  This is the paper's case analysis verbatim, and it needs no primitivity: any `g ∈ R[λ]` of
  positive degree dividing every `m_i` *in `R[λ]`* works.
* `Q1Paper.exists_primitive_common_dvd` — Gauss's lemma, the only place where the function field
  enters: a common divisor of positive degree over `K(X)[λ]` yields one over `R[λ]` that is
  primitive and of positive degree.
* `Q1Paper.exists_common_factor_of_gcd` — the paper's claim assembled, uniformly over an arbitrary
  index type of points; one `g`, produced once from the function-field data, works at all of them.
* `Q1Paper.exists_eval_ne_zero` — the "proper algebraic subset" half of the picture: a nonzero
  polynomial on a chart has a nonvanishing point, so the locus where a leading coefficient vanishes
  cannot be the whole chart.

The paper states its hypothesis as `deg_λ gcd(m₁,…,m_t) > 0` in `K(X)[λ]`.  In the formalisation
the hypothesis is the equivalent "there is a common divisor of positive degree" (`hgcd` below): a
gcd is only determined up to units, and every common divisor divides a gcd, so the two forms agree
as soon as the `m_i` do not all vanish.  (Mathlib's `Polynomial F` deliberately carries no
`GCDMonoid` instance — see `Mathlib/RingTheory/Polynomial/Content.lean` — so there is no function
`Polynomial.gcd` to state the paper's phrasing with; `IsGCDMonoid` carries the same content.)

What is *not* formalised, and why:
* the chart / Grassmannian description of `𝒳_I` and its Zariski topology (the library has no
  projective-space or Zariski-topology API; the same limitation is recorded in `Strata.lean`).
  Accordingly the Lean statements quantify over an arbitrary index type `P` of points together
  with their specialisation maps `R →+* S`; this is exactly what the paper's proof uses, and it is
  the most general form the argument supports;
* the "good points form a nonempty Zariski open subset" half of the dichotomy — that is the
  separate claim `sec4:thm:generic` (graded separately in `workspace/paper_split/LEAN_GAPS.md`);
  the present lemma only propagates the *bad* branch, which is what the paper uses it for.  The
  emptiness/density statements about the real points of the chart are `sec4:prop:realpoints`,
  paper-level for the same reason;
* the derivation of (★) from `rank H ≡ ω`, i.e. the identification of the coefficient of `λ^ω` in
  an `ω × ω` minor of the pencil `λH − H_A` with the corresponding `ω × ω` minor of `H` (a
  determinant expansion `det (z • M − N) = z ^ ω det M + (lower order)`).  That determinant
  identity and the passage from a rank bound to a nonvanishing minor are ordinary linear algebra,
  but gluing them to the paper's chart matrices is the chart bookkeeping of `sec4:lem:minorcount`,
  graded separately; nothing in the present lemma depends on it.

Base ring.  The formalisation asks for `[NormalizedGCDMonoid R]` (so that contents and primitive
parts exist) and `[IsGCDMonoid R]` (Gauss's lemma).  Both hold for `R = K[X]` (`Polynomial K`) and
for `R = ℤ`.  For several variables `R = MvPolynomial σ K` Mathlib has `IsGCDMonoid` but no
`NormalizedGCDMonoid`, so the multi-variable coordinate ring is not instantiated here; nothing in
the argument depends on the number of variables.
-/

import Mathlib

open Polynomial

namespace Q1Paper

/-! ### The specialisation step at one point -/

section OnePoint

variable {R S ι : Type*} [CommRing R] [IsDomain R] [CommRing S]

/-- **Paper III, Claim `sec4:lem:fullrank`, one point.**  Let `g ∈ R[λ]` be a common divisor of the
polynomials `m i ∈ R[λ]`, of positive `λ`-degree, and suppose `deg_λ (m i) ≤ ω` for all `i`.  If at
the point `φ` the full-rank condition (★) holds — some `m i` specialises to a nonzero polynomial of
exact `λ`-degree `ω` — then `g` specialises to a *nonzero* polynomial of *positive* `λ`-degree which
divides every specialised `m i`.

This is the paper's case analysis verbatim, and it is the reason the lemma needs no primitivity:
the two degenerate alternatives for `g(φ,·)` (identically zero, or a nonzero constant) each
contradict (★). -/
theorem specialized_common_factor (φ : R →+* S) {g : R[X]} {m : ι → R[X]} {ω : ℕ}
    (hgdeg : 1 ≤ g.natDegree) (hdiv : ∀ i, g ∣ m i)
    (hdeg : ∀ i, (m i).natDegree ≤ ω)
    (hfull : ∃ i, (m i).map φ ≠ 0 ∧ ((m i).map φ).natDegree = ω) :
    g.map φ ≠ 0 ∧ 1 ≤ (g.map φ).natDegree ∧ ∀ i, g.map φ ∣ (m i).map φ := by
  classical
  obtain ⟨i₀, hi₀ne, hi₀deg⟩ := hfull
  have hg0 : g ≠ 0 := by rintro rfl; simp at hgdeg
  have hdiv' := hdiv
  choose h hh using hdiv'
  -- the witness `m i₀` is nonzero, hence so is its cofactor
  have hm0 : m i₀ ≠ 0 := by rintro h0; exact hi₀ne (by rw [h0]; simp)
  have hh0 : h i₀ ≠ 0 := by
    rintro hzero
    have hz := hh i₀
    rw [hzero, mul_zero] at hz
    exact hm0 hz
  have hdegmul : (m i₀).natDegree = g.natDegree + (h i₀).natDegree := by
    rw [hh i₀]; exact natDegree_mul hg0 hh0
  have hgle : g.natDegree ≤ (m i₀).natDegree := natDegree_le_of_dvd (hdiv i₀) hm0
  have hdeg₀ : (m i₀).natDegree ≤ ω := hdeg i₀
  -- the cofactor has `λ`-degree `< ω`
  have hcof : (h i₀).natDegree < ω := by omega
  have hzero : (m i₀).map φ = (g.map φ) * ((h i₀).map φ) := by
    rw [hh i₀, Polynomial.map_mul]
  refine ⟨?_, ?_, fun i => map_dvd φ (hdiv i)⟩
  · rintro h0
    exact hi₀ne (by rw [hzero, h0, zero_mul])
  · rcases Nat.eq_zero_or_pos ((g.map φ).natDegree) with h1 | h1
    · -- `g(φ,·)` is a nonzero constant: then `deg_λ (m i₀)(φ,·) ≤ deg_λ h i₀ < ω`
      exfalso
      have hle : ((m i₀).map φ).natDegree ≤ (h i₀).natDegree := by
        rw [hzero]
        calc ((g.map φ) * ((h i₀).map φ)).natDegree
            ≤ (g.map φ).natDegree + ((h i₀).map φ).natDegree := natDegree_mul_le
          _ = ((h i₀).map φ).natDegree := by rw [h1, zero_add]
          _ ≤ (h i₀).natDegree := natDegree_map_le
      omega
    · exact h1

end OnePoint

/-! ### The "proper algebraic subset" step -/

section ProperClosed

variable {K σ : Type*} [CommRing K] [IsDomain K] [Infinite K]

/-- **A nonzero polynomial has a nonvanishing point.**  Equivalently, the zero set of a nonzero
polynomial on an affine chart is a *proper* algebraic subset: the good points of a chart are not
empty.  This is the algebraic content of "the set of parameters where the leading coefficient
vanishes is a proper algebraic subset" in Claim `sec4:lem:fullrank`. -/
theorem exists_eval_ne_zero {p : MvPolynomial σ K} (hp : p ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x p ≠ 0 := by
  by_contra h
  push Not at h
  exact hp (MvPolynomial.funext fun x => by rw [h x, map_zero])

end ProperClosed

/-! ### Unit scaling of divisibility -/

section Scaling

variable {F : Type*} [Field F]

/-- Multiplication by a nonzero constant does not change divisibility in `F[λ]`. -/
theorem C_mul_dvd_iff {u : F} (hu : u ≠ 0) {p q : F[X]} : (C u * p) ∣ q ↔ p ∣ q := by
  have huC : C u * C u⁻¹ = (1 : F[X]) := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hu, Polynomial.C_1]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨C u * s, by rw [hs]; ring⟩
  · rintro ⟨s, hs⟩
    refine ⟨C u⁻¹ * s, ?_⟩
    rw [hs]
    calc p * s = (C u * C u⁻¹) * (p * s) := by rw [huC, one_mul]
      _ = C u * p * (C u⁻¹ * s) := by ring

end Scaling

/-! ### Gauss's lemma: from the function field back to `R[λ]` -/

section Gauss

variable {R K ι : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R] [IsGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Gauss's lemma, denominator-clearing form.**  If a polynomial `g_F ∈ K(X)[λ]` of positive
degree divides every `m i` over the function field, then there is a *primitive* `g ∈ R[λ]` of
positive degree dividing every `m i` in `R[λ]`.

Construction (the paper's "by Gauss's lemma we may take `g` primitive in `K[X][λ]`"): clear
denominators (`IsLocalization.integerNormalization`), divide by the content (`.primPart`), and
descend divisibility with `Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map`. -/
theorem exists_primitive_common_dvd {m : ι → R[X]}
    (hgcd : ∃ gF : K[X], 0 < gF.natDegree ∧ ∀ i, gF ∣ (m i).map (algebraMap R K)) :
    ∃ g : R[X], g.IsPrimitive ∧ 0 < g.natDegree ∧ ∀ i, g ∣ m i := by
  classical
  obtain ⟨gF, hgFdeg, hgFdvd⟩ := hgcd
  have hgF0 : gF ≠ 0 := by rintro rfl; simp at hgFdeg
  -- clear denominators
  set q : R[X] := IsLocalization.integerNormalization (nonZeroDivisors R) gF with hqdef
  obtain ⟨b, hb_mem, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) gF
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb_mem
  have hbmap : algebraMap R K (b : R) ≠ 0 := by
    intro h
    exact hb0 (IsFractionRing.injective R K (by simpa using h))
  have hqmap : q.map (algebraMap R K) = C (algebraMap R K (b : R)) * gF := by
    rw [hb, Algebra.smul_def, IsScalarTower.algebraMap_apply R K K[X], Polynomial.algebraMap_eq]
  have hqne : q ≠ 0 := by
    intro h0
    have hCne : C (algebraMap R K (b : R)) * gF ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact hbmap (by simpa using h1)
      · exact hgF0 h1
    apply hCne
    rw [← hqmap, h0, Polynomial.map_zero]
  -- divide by the content
  set g : R[X] := q.primPart with hgdef
  have hgprim : g.IsPrimitive := q.isPrimitive_primPart
  have hcont0 : q.content ≠ 0 := fun h => hqne (Polynomial.content_eq_zero_iff.mp h)
  have hc0 : algebraMap R K q.content ≠ 0 := by
    intro h
    exact hcont0 (IsFractionRing.injective R K (by simpa using h))
  -- the key identity: `g` differs from `g_F` by a nonzero constant
  have hkey : C (algebraMap R K q.content) * g.map (algebraMap R K)
      = C (algebraMap R K (b : R)) * gF := by
    have h := congrArg (Polynomial.map (algebraMap R K)) (q.eq_C_content_mul_primPart)
    rw [hqmap, Polynomial.map_mul, Polynomial.map_C] at h
    exact h.symm
  have hgmap : g.map (algebraMap R K)
      = C ((algebraMap R K q.content)⁻¹ * algebraMap R K (b : R)) * gF := by
    calc g.map (algebraMap R K)
        = C (algebraMap R K q.content)⁻¹
            * (C (algebraMap R K q.content) * g.map (algebraMap R K)) := by
          rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hc0, Polynomial.C_1, one_mul]
      _ = C (algebraMap R K q.content)⁻¹ * (C (algebraMap R K (b : R)) * gF) := by rw [hkey]
      _ = C ((algebraMap R K q.content)⁻¹ * algebraMap R K (b : R)) * gF := by
          rw [← mul_assoc, ← Polynomial.C_mul]
  have hu0 : (algebraMap R K q.content)⁻¹ * algebraMap R K (b : R) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hc0) hbmap
  refine ⟨g, hgprim, ?_, ?_⟩
  · -- positive degree: `deg g_F ≤ deg (g.map) ≤ deg g`
    have h1 : (g.map (algebraMap R K)).natDegree = gF.natDegree := by
      rw [hgmap, natDegree_C_mul hu0]
    have h2 : (g.map (algebraMap R K)).natDegree ≤ g.natDegree := natDegree_map_le
    omega
  · -- divisibility descends by Gauss's lemma
    intro i
    have hfr : g.map (algebraMap R K) ∣ (m i).map (algebraMap R K) := by
      rw [hgmap]
      exact (C_mul_dvd_iff hu0).mpr (hgFdvd i)
    exact hgprim.dvd_of_fraction_map_dvd_fraction_map hfr

end Gauss

/-! ### The paper's claim, assembled over all points -/

section Assembly

variable {R K S ι P : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R] [IsGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K] [CommRing S]

/-- **Paper III, Claim `sec4:lem:fullrank`.**  Let `m : ι → R[λ]` with `deg_λ (m i) ≤ ω` for all
`i`, and suppose the `m i` have a common divisor of positive `λ`-degree over the function field
`K(X)` (the paper's `deg_λ gcd_I m_I > 0` in `K(X)[λ]`).  Then there is a single `g ∈ R[λ]` of
positive degree which, at *every* point `p` of an arbitrary index set `P` at which the full-rank
condition (★) holds, specialises to a nonconstant common factor of the specialised `m i`.

This is the paper's "a gcd computation performed at a generic parameter certifies the statement at
all parameters": `g` is produced once, from the function-field data, and the specialisation
statement is uniform in the point. -/
theorem exists_common_factor_of_gcd (pts : P → R →+* S) (m : ι → R[X]) (ω : ℕ)
    (hdeg : ∀ i, (m i).natDegree ≤ ω)
    (hgcd : ∃ gF : K[X], 0 < gF.natDegree ∧ ∀ i, gF ∣ (m i).map (algebraMap R K))
    (hfull : ∀ p, ∃ i, (m i).map (pts p) ≠ 0 ∧ ((m i).map (pts p)).natDegree = ω) :
    ∃ g : R[X], 0 < g.natDegree ∧
      ∀ p, g.map (pts p) ≠ 0 ∧ 1 ≤ (g.map (pts p)).natDegree ∧
        ∀ i, g.map (pts p) ∣ (m i).map (pts p) := by
  obtain ⟨g, -, hgdeg, hgdvd⟩ := exists_primitive_common_dvd (K := K) (m := m) hgcd
  exact ⟨g, hgdeg, fun p => specialized_common_factor (pts p) (g := g) (m := m) (ω := ω)
    (Nat.succ_le_of_lt hgdeg) hgdvd hdeg (hfull p)⟩

end Assembly

/-! ### Instantiation check

The hypotheses of `exists_common_factor_of_gcd` are satisfiable: take `R = ℚ[X]` — the paper's
coordinate ring `K[X]` in the case `d = 1`, with `K = ℚ` and function field `ℚ(X)` — and `S = ℚ`.
This is a compile-time check that the typeclass assumptions (`NormalizedGCDMonoid`,
`IsGCDMonoid`, `IsFractionRing`) are met by the polynomial ring over a field. -/

section Instantiation

example (m : Fin 1 → (Polynomial ℚ)[X]) (ω : ℕ)
    (hdeg : ∀ i, (m i).natDegree ≤ ω)
    (hgcd : ∃ gF : (FractionRing (Polynomial ℚ))[X], 0 < gF.natDegree ∧
      ∀ i, gF ∣ (m i).map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))))
    (pts : Unit → (Polynomial ℚ) →+* ℚ)
    (hfull : ∀ p, ∃ i, (m i).map (pts p) ≠ 0 ∧ ((m i).map (pts p)).natDegree = ω) :
    ∃ g : (Polynomial ℚ)[X], 0 < g.natDegree ∧
      ∀ p, g.map (pts p) ≠ 0 ∧ 1 ≤ (g.map (pts p)).natDegree ∧
        ∀ i, g.map (pts p) ∣ (m i).map (pts p) :=
  exists_common_factor_of_gcd pts m ω hdeg hgcd hfull

end Instantiation

end Q1Paper
