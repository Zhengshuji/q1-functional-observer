import Mathlib
import Q1Paper.PaperV.RankMinor

/-!
Q1Paper/PaperV/RhoCounterexample.lean

**Scope.**  This file is the Lean certificate for the counterexample of note `806` against the
`ρ`-criterion of `802`/`803` in Paper V.  It is *not* a formalisation of the whole `THIN-FEAS`
statement, of Theorem 4, of the paper's §VI discussion, or of any other paper claim.  It
formalises one explicit instance (`k = 4`, `q = 3`, `d' = 2`, `t = 2`) and isolates exactly one
failing implication, the **necessity** direction

  `bad at some λ  ⟹  ∃ λ ∈ spec(Z), ρ(λ) < d'`.

Nothing in `Audit.lean`, `Claims.lean`, `MainTheorems.lean`, `paper/` or `docs/` is touched.  The
file only imports `Mathlib` and the already-proved rank–minor bridge `Q1Paper.PaperV.RankMinor`.

## The instance (`806`)

In `V = ℂ⁴` with standard basis `e 0, e 1, e 2, e 3` (0-based; the paper's `e₁, …, e₄` are
`e 0, …, e 3`):

* `H` has rows `e 0`, `e 1 + e 2`, `e 0 + e 1 + e 2`  (paper: `e₁`, `e₂+e₃`, `e₁+e₂+e₃`),
* `T = span {e 0, e 1}`  (paper: `T = span(e₁,e₂)`), with `U = row H`, so `d' = rank H = 2`,
* `Z = diag(0,0,1,0) = diagonal (Pi.single 2 1)`; its spectrum is `spec(Z) = {0,1}`
  (prose only, not formalised),
* fibre rows `G(c)` are `c₀ • e 0`, `c₁ • e 0 + e 1`, `c₂ • e 0 + e 1`.

The pencil is `P(λ,c) = λ H - H Z - G(c)`; `pencil lam = H (lam • 1 - Z)` is its `λH - HZ` part,
and `P c = H - H Z - fibreRow c` is its value at `λ = 1`.

## What is proved

* `fibreRow_mem_rowT`, `fibreRow_add_mulZ_mem_U`: every `fibreRow c i` lies in the fibre, i.e. in
  `T`'s row space and with `fibreRow c i + (H Z) i ∈ U = row H`.
* `P_eq_vecMulVec`, `P_apply_of_ne_zero`, `rank_P_lt_two`: at `λ = 1` every row of `P c` lies in
  `ℂ e 0` (all coordinates `1, 2, 3` vanish), hence `rank (P c) ≤ 1 < 2 = d'` for **every** `c`:
  the whole fibre is bad.  (The paper's gcd statement `gcd(2-minors) = λ - 1` is recorded in this
  comment only, not formalised.)
* `rho_zero`, `rho_one`: with `ρ(λ) = dim span(T ⊓ U, {λ Hᵢ - Hᵢ Z})` realised as the rank of the
  matrix whose first row is a generator `e 0` of `T ⊓ U` and whose remaining rows are those of
  `pencil λ`, one has `ρ(0) = ρ(1) = 2 = d'`.  `rowT_inf_U_eq_span_e0` justifies using `e 0` as
  the generator of `T ⊓ U`.
* `rho_criterion_necessity_fails`: **main theorem.**  Every `c` is bad at `λ = 1`, yet there is no
  `λ ∈ {0,1}` with `ρ(λ) < 2`; hence the implication
  `bad ⟹ ∃ λ ∈ spec(Z), ρ(λ) < d'` is false.  This is the `806` retraction of the necessity
  direction only; it says nothing about sufficiency of the `ρ`-criterion.

No `sorry`, no custom axiom.  The principal results are checked at the end with `#print axioms`;
only Lean's three standard axioms are allowed.
-/

set_option maxHeartbeats 800000

namespace Q1Paper.PaperV

/-! ### The instance `k = 4`, `q = 3`, `d' = 2` -/

/-- The standard basis vector `eᵢ` of `V = ℂ⁴` (0-based: the paper's `e₁` is `e 0`). -/
noncomputable def e (i : Fin 4) : Fin 4 → ℂ := Pi.single i 1

/-- `H` with rows `e 0`, `e 1 + e 2`, `e 0 + e 1 + e 2` (paper: `e₁`, `e₂+e₃`, `e₁+e₂+e₃`). -/
noncomputable def H : Matrix (Fin 3) (Fin 4) ℂ :=
  fun i => ![e 0, e 1 + e 2, e 0 + e 1 + e 2] i

/-- `T = span {e 0, e 1}` (paper: `T = span(e₁,e₂)`), as the matrix of its two generators. -/
noncomputable def T : Matrix (Fin 2) (Fin 4) ℂ := fun i => ![e 0, e 1] i

/-- `Z = diag(0,0,1,0)`: the diagonal matrix with a single `1` in coordinate `2`. -/
noncomputable def Z : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal (Pi.single 2 1)

/-- The row space of a matrix with `m` rows and `4` columns. -/
noncomputable def rowSpan {m : ℕ} (A : Matrix (Fin m) (Fin 4) ℂ) : Submodule ℂ (Fin 4 → ℂ) :=
  Submodule.span ℂ (Set.range fun i => A i)

/-- `U = row H`. -/
noncomputable def U : Submodule ℂ (Fin 4 → ℂ) := rowSpan H

/-- `row T`, the subspace `T` of the paper. -/
noncomputable def rowT : Submodule ℂ (Fin 4 → ℂ) := rowSpan T

/-- The parameterized fibre rows `c₀ • e 0`, `c₁ • e 0 + e 1`, `c₂ • e 0 + e 1`
(paper: `(c₁,0,0,0)`, `(c₂,1,0,0)`, `(c₃,1,0,0)`). -/
noncomputable def fibreRow (c : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 4) ℂ :=
  fun i => ![c 0 • e 0, c 1 • e 0 + e 1, c 2 • e 0 + e 1] i

/-- The `λ`-part `H (λ • 1 - Z)` of the pencil. -/
noncomputable def pencil (lam : ℂ) : Matrix (Fin 3) (Fin 4) ℂ := H * (lam • 1 - Z)

/-- The value `P(c) = H - H Z - G(c)` of the pencil at `λ = 1`. -/
noncomputable def P (c : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 4) ℂ := H - H * Z - fibreRow c

/-! ### Row-space membership of the fibre rows -/

theorem e0_mem_rowT : e 0 ∈ rowT := by
  rw [rowT, rowSpan]
  exact Submodule.subset_span (Set.mem_range_self 0)

theorem e1_mem_rowT : e 1 ∈ rowT := by
  rw [rowT, rowSpan]
  exact Submodule.subset_span (Set.mem_range_self 1)

theorem e0_mem_U : e 0 ∈ U := by
  rw [U, rowSpan]
  exact Submodule.subset_span (Set.mem_range_self 0)

theorem e1e2_mem_U : e 1 + e 2 ∈ U := by
  rw [U, rowSpan]
  exact Submodule.subset_span (Set.mem_range_self 1)

/-- The coordinate functional `x ↦ x i` on `ℂ⁴`. -/
abbrev coord (i : Fin 4) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj i

theorem rowT_coord_two {x : Fin 4 → ℂ} (hx : x ∈ rowT) : x 2 = 0 := by
  have hle : rowT ≤ (coord 2).ker := by
    rw [rowT, rowSpan]
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    fin_cases i <;> simp [T, e]
  exact hle hx

theorem rowT_coord_three {x : Fin 4 → ℂ} (hx : x ∈ rowT) : x 3 = 0 := by
  have hle : rowT ≤ (coord 3).ker := by
    rw [rowT, rowSpan]
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    fin_cases i <;> simp [T, e]
  exact hle hx

theorem U_coord_diff {x : Fin 4 → ℂ} (hx : x ∈ U) : x 1 - x 2 = 0 := by
  have hle : U ≤ (coord 1 - coord 2).ker := by
    rw [U, rowSpan]
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    fin_cases i <;> simp [H, e]
  exact hle hx

theorem U_coord_three {x : Fin 4 → ℂ} (hx : x ∈ U) : x 3 = 0 := by
  have hle : U ≤ (coord 3).ker := by
    rw [U, rowSpan]
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    fin_cases i <;> simp [H, e]
  exact hle hx

theorem mem_rowT_iff (v : Fin 4 → ℂ) : v ∈ rowT ↔ v 2 = 0 ∧ v 3 = 0 := by
  constructor
  · intro hv; exact ⟨rowT_coord_two hv, rowT_coord_three hv⟩
  · rintro ⟨h2, h3⟩
    have hv : v = v 0 • e 0 + v 1 • e 1 := by
      funext j
      fin_cases j <;> simp [e, h2, h3]
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ e0_mem_rowT)
      (Submodule.smul_mem _ _ e1_mem_rowT)

theorem mem_U_iff (v : Fin 4 → ℂ) : v ∈ U ↔ v 1 = v 2 ∧ v 3 = 0 := by
  constructor
  · intro hv
    have h3 : v 3 = 0 := U_coord_three hv
    exact ⟨sub_eq_zero.mp (U_coord_diff hv), h3⟩
  · rintro ⟨h12, h3⟩
    have hv : v = v 0 • e 0 + v 1 • (e 1 + e 2) := by
      funext j
      fin_cases j <;> simp [e, h12, h3]
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ e0_mem_U)
      (Submodule.smul_mem _ _ e1e2_mem_U)

/-- **(2, first half.)** Every row of the parameterized fibre matrix lies in `T`'s row space. -/
theorem fibreRow_mem_rowT (c : Fin 3 → ℂ) (i : Fin 3) : fibreRow c i ∈ rowT := by
  rw [mem_rowT_iff]
  constructor <;> fin_cases i <;> simp [fibreRow, e]

/-- **(2, second half.)** `fibreRow c i + (H Z) i ∈ U = row H`, the per-row fibre condition
`x + Hᵢ Z ∈ U`. -/
theorem fibreRow_add_mulZ_mem_U (c : Fin 3 → ℂ) (i : Fin 3) :
    fibreRow c i + (H * Z) i ∈ U := by
  rw [mem_U_iff]
  constructor <;> fin_cases i <;> simp [fibreRow, H, Z, e]

/-! ### Badness at `λ = 1`: the whole fibre has rank at most `1` -/

/-- Entrywise form of `pencil lam = H (lam • 1 - Z)`. -/
@[simp] theorem pencil_apply (lam : ℂ) (i : Fin 3) (j : Fin 4) :
    pencil lam i j = lam * H i j - (H * Z) i j := by
  simp [pencil, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]

/-- Entrywise form of `P c = H - H Z - fibreRow c`. -/
@[simp] theorem P_apply (c : Fin 3 → ℂ) (i : Fin 3) (j : Fin 4) :
    P c i j = H i j - (H * Z) i j - fibreRow c i j := rfl

/-- **(3.)** `P(c)` is a rank-one `vecMulVec` matrix: its rows are `(1-c₀) e 0`, `(-c₁) e 0`,
`(1-c₂) e 0`. -/
theorem P_eq_vecMulVec (c : Fin 3 → ℂ) :
    P c = Matrix.vecMulVec ![1 - c 0, -c 1, 1 - c 2] (e 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_apply, fibreRow, H, Z, e, Matrix.vecMulVec_apply] <;> ring

/-- Off the `0`-th coordinate every entry of `P c` vanishes: the coordinate form of
"every row of `P c` lies in `ℂ e 0`". -/
theorem P_apply_of_ne_zero (c : Fin 3 → ℂ) (i : Fin 3) {j : Fin 4} (hj : j ≠ 0) :
    P c i j = 0 := by
  rw [P_eq_vecMulVec]
  simp [Matrix.vecMulVec_apply, e, Pi.single_apply, hj]

/-- Every row of `P c` lies in `span {e 0}`. -/
theorem P_row_mem_span_e0 (c : Fin 3 → ℂ) (i : Fin 3) :
    P c i ∈ Submodule.span ℂ ({e 0} : Set (Fin 4 → ℂ)) := by
  have hrow : P c i = ![1 - c 0, -c 1, 1 - c 2] i • e 0 := by
    rw [P_eq_vecMulVec]
    funext j
    simp [Matrix.vecMulVec_apply, Pi.smul_apply]
  rw [hrow]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- **(3.)** At `λ = 1` the pencil has rank at most `1 < 2 = d'`, for every parameter `c`. -/
theorem rank_P_lt_two (c : Fin 3 → ℂ) : (P c).rank < 2 := by
  have h : (P c).rank ≤ 1 := by
    rw [P_eq_vecMulVec]
    exact Matrix.rank_vecMulVec_le _ _
  omega

/-! ### The `ρ`-invariant at `λ = 0` and `λ = 1` -/

/-- A row spanning `T ⊓ U` followed by the rows of `pencil lam = H (lam • 1 - Z)`. -/
noncomputable def rhoMat (lam : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i => ![e 0, pencil lam 0, pencil lam 1, pencil lam 2] i

/-- `ρ(λ) = dim span(T ⊓ U, {λ Hᵢ - Hᵢ Z})`, computed as a matrix rank. -/
noncomputable def rho (lam : ℂ) : ℕ := (rhoMat lam).rank

/-- **`T ⊓ U = span {e 0}`.**  This justifies using `e 0` as the generator of `T ⊓ U`. -/
theorem rowT_inf_U_eq_span_e0 :
    rowT ⊓ U = Submodule.span ℂ ({e 0} : Set (Fin 4 → ℂ)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxU⟩ := Submodule.mem_inf.mp hx
    have h2 : x 2 = 0 := rowT_coord_two hxT
    have h3 : x 3 = 0 := rowT_coord_three hxT
    have h1 : x 1 = 0 := by
      have h12 : x 1 - x 2 = 0 := U_coord_diff hxU
      rw [h2] at h12
      exact sub_eq_zero.mp h12
    have hxeq : x = x 0 • e 0 := by
      funext j
      fin_cases j <;> simp [e, h1, h2, h3]
    rw [hxeq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro x hx
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact Submodule.span_le.mpr (by rintro y rfl; exact e0_mem_rowT) hx
    · exact Submodule.span_le.mpr (by rintro y rfl; exact e0_mem_U) hx

/-- `rhoMat 0` has rows `e 0`, `0`, `-e 2`, `-e 2`. -/
theorem rhoMat_zero : rhoMat 0 = fun i => ![e 0, 0, -e 2, -e 2] i := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rhoMat, H, Z, e]

/-- `rhoMat 1` has rows `e 0`, `e 0`, `e 1`, `e 0 + e 1`. -/
theorem rhoMat_one : rhoMat 1 = fun i => ![e 0, e 0, e 1, e 0 + e 1] i := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rhoMat, H, Z, e] <;> ring

/-- `rank A ≤ card s` when the columns of `A` outside `s` vanish. -/
theorem rank_le_card_of_support_cols {m : ℕ} (A : Matrix (Fin m) (Fin 4) ℂ) (s : Finset (Fin 4))
    (hz : ∀ j, j ∉ s → ∀ i, A i j = 0) : A.rank ≤ s.card := by
  have h := Matrix.rank_le_card_of_support_subset (Matrix.transpose A) s ?_
  · rwa [Matrix.rank_transpose] at h
  · intro j hj
    by_contra hjs
    apply hj
    funext i
    simpa [Matrix.transpose_apply] using hz j hjs i

theorem rhoMat_zero_le_two : (rhoMat 0).rank ≤ 2 := by
  have h := rank_le_card_of_support_cols (rhoMat 0) ({0, 2} : Finset (Fin 4)) ?_
  · simpa using h
  · intro j hj i
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨hj0, hj2⟩ := hj
    fin_cases i <;> fin_cases j <;> simp_all [rhoMat, H, Z, e]

theorem rhoMat_one_le_two : (rhoMat 1).rank ≤ 2 := by
  have h := rank_le_card_of_support_cols (rhoMat 1) ({0, 1} : Finset (Fin 4)) ?_
  · simpa using h
  · intro j hj i
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨hj0, hj1⟩ := hj
    fin_cases i <;> fin_cases j <;> simp_all [rhoMat, H, Z, e] <;> ring

/-- Row and column selection `0 ↦ a`, `1 ↦ b`. -/
abbrev pick (a b : Fin 4) : Fin 2 → Fin 4 := ![a, b]

/-- The `2 × 2` minor of `rhoMat 0` on rows `0,2` and columns `0,2` is `-1 ≠ 0`. -/
theorem rhoMat_zero_minor :
    ((rhoMat 0).submatrix (pick 0 2) (pick 0 2)).det ≠ 0 := by
  rw [Matrix.det_fin_two]
  simp [Matrix.submatrix, pick, rhoMat, H, Z, e]

/-- The `2 × 2` minor of `rhoMat 1` on rows `0,2` and columns `0,1` is `1 ≠ 0`. -/
theorem rhoMat_one_minor :
    ((rhoMat 1).submatrix (pick 0 2) (pick 0 1)).det ≠ 0 := by
  rw [Matrix.det_fin_two]
  simp [Matrix.submatrix, pick, rhoMat, H, Z, e] <;> ring

/-- `ρ(0) = 2 = d'`. -/
theorem rho_zero : rho 0 = 2 := by
  refine le_antisymm rhoMat_zero_le_two ?_
  exact le_rank_of_det_submatrix_ne_zero _ (pick 0 2) (pick 0 2) rhoMat_zero_minor

/-- `ρ(1) = 2 = d'`. -/
theorem rho_one : rho 1 = 2 := by
  refine le_antisymm rhoMat_one_le_two ?_
  exact le_rank_of_det_submatrix_ne_zero _ (pick 0 2) (pick 0 1) rhoMat_one_minor

/-! ### The failure of the necessity direction -/

/-- `ρ` takes the value `2 = d'` on the spectrum `{0,1}` of `Z`. -/
theorem rho_eq_two {lam : ℂ} (hlam : lam ∈ ({0, 1} : Finset ℂ)) : rho lam = 2 := by
  rw [Finset.mem_insert, Finset.mem_singleton] at hlam
  rcases hlam with rfl | rfl
  · exact rho_zero
  · exact rho_one

/-- **No spectral witness.**  There is no `λ ∈ {0,1}` with `ρ(λ) < d' = 2`. -/
theorem no_small_rho_on_spectrum :
    ¬ ∃ lam ∈ ({0, 1} : Finset ℂ), rho lam < 2 := by
  rintro ⟨lam, hlam, hlt⟩
  rw [rho_eq_two hlam] at hlt
  omega

/-- **The necessity direction fails.**  Applying the criterion's necessity to the fibre point
`c = 0` (bad by `rank_P_lt_two`) would produce `λ ∈ {0,1}` with `ρ(λ) < 2`, contradicting
`no_small_rho_on_spectrum`. -/
theorem rho_necessity_fails :
    ¬ ∀ c : Fin 3 → ℂ, (P c).rank < 2 →
      ∃ lam ∈ ({0, 1} : Finset ℂ), rho lam < 2 := by
  intro h
  exact no_small_rho_on_spectrum (h 0 (rank_P_lt_two 0))

/-- **The `806` Lean certificate (main theorem).**  The whole fibre is bad at `λ = 1`
(`rank (P c) ≤ 1 < 2` for every `c`), yet no `λ ∈ {0,1}` has `ρ(λ) < 2`.  Hence the necessity
direction of the `ρ`-criterion fails; this says nothing about its sufficiency. -/
theorem rho_criterion_necessity_fails :
    (∀ c : Fin 3 → ℂ, (P c).rank < 2) ∧
      (¬ ∃ lam ∈ ({0, 1} : Finset ℂ), rho lam < 2) ∧
      (¬ ∀ c : Fin 3 → ℂ, (P c).rank < 2 →
        ∃ lam ∈ ({0, 1} : Finset ℂ), rho lam < 2) :=
  ⟨rank_P_lt_two, no_small_rho_on_spectrum, rho_necessity_fails⟩

end Q1Paper.PaperV

#print axioms Q1Paper.PaperV.rho_zero
#print axioms Q1Paper.PaperV.rho_one
#print axioms Q1Paper.PaperV.rank_P_lt_two
#print axioms Q1Paper.PaperV.fibreRow_add_mulZ_mem_U
#print axioms Q1Paper.PaperV.rho_criterion_necessity_fails
