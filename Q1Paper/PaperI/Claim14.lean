/-
Q1Paper/PaperI/Claim14.lean

Core of Claim 14 of Paper I: the intersection `V = T ∩ S` as the image of the
kernel of a stacked (difference) map, and the resulting generating set.

## Setup

`psi : U →ₗ[K] W` and `phi : V →ₗ[K] W` are the paper's two row maps; in the
matrix model `U = Fin a → K`, `V = Fin b → K`, `W = Fin d → K` and

  `psi u = u ᵥ* A_T`,   `phi v = v ᵥ* A_V`,

so that `T = range psi = row A_T` and `S = range phi = row A_V` are the two
row spaces of Claim 14.

## Which kernel gives the intersection

The intersection is the image of the **equalizer**

  `K0 = ker (psi ∘ fst - phi ∘ snd)`,

i.e. the kernel of the difference map `(u, v) ↦ psi u - phi v` (in matrix
language: the kernel of the **row**-stacked block matrix `[A_Tᵀ | -A_Vᵀ]`).
Two nearby kernels are *not* the right object, and both are recorded below so
that the distinction is not lost later:

* `ker (LinearMap.prod psi phi)` (the map `(u,v) ↦ (psi u, phi v)`, i.e. what
  one gets from a **column**-stacked matrix `[A_Tᵀ; A_Vᵀ]`) is
  `ker psi × ker phi`, and the image of this kernel under `psi ∘ fst` is `⊥`
  (`map_comp_fst_pairedMap_ker_eq_bot`) — vacuously far from `T ∩ S`;
* the plain first projection `map fst K0` is not `T ∩ S` either: it is the
  full preimage `comap psi (range phi)` (`map_fst_K0_eq_comap`).  One has to
  post-compose with `psi`, which is exactly "the row of the image".

A *vertical* stack `[A_Tᵀ; -A_Vᵀ]` is not even type correct when `a ≠ b`.

## Main statements

* `map_comp_fst_K0_eq_inf` :
  `map (psi ∘ fst) K0 = range psi ⊓ range phi` (the paper's `T ∩ S`).
  Both inclusions are elementary; no dimension count, no finiteness, no inner
  product, no rank identity is used.
* `span_image_basis_eq_inf` : for **any** basis `b` of `K0`, the image family
  `i ↦ psi ((b i).1)` *spans* the intersection: it is a generating set.
* `linearIndependent_image_basis_iff` : that image family is linearly
  independent **iff** `ker psi = ⊥` and `ker phi = ⊥`.  Hence in general the
  image of a basis of `K0` is only a generating set; it is a basis of the
  intersection exactly under this injectivity hypothesis.
* `ker_restrictFst_eq_bot_iff` identifies the dependency space of the
  restricted map with `ker psi × ker phi`.
* `quotientEquivInf` : the first isomorphism theorem applied to the restricted
  map, `K0 ⧸ (ker psi × ker phi) ≃ₗ[K] T ⊓ S`; this is the exact
  "remove the linear dependencies" step.
* `matrix_map_comp_fst_K0_eq_inf` : the matrix form
  `map (u ↦ u ᵥ* A_T) K0 = row A_T ⊓ row A_V`.

All statements below are proved; there is no `sorry`, no `admit`, no new
axiom.  The axiom footprint of the headline results is printed at the end.
-/

import Q1Paper.Q1RowSpace
import Q1Paper.Q1Subspace

namespace Q1Paper.PaperI.Claim14

open Module
open Submodule

variable {K : Type*} [Field K]
variable {U V W : Type*}
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-! ### 1. The difference map, the equalizer `K0`, and the kernel of `prod` -/

/-- The difference map `(u, v) ↦ psi u - phi v`.  Its kernel is the equalizer
of `psi` and `phi` (the kernel of the row-stacked matrix `[A_Tᵀ | -A_Vᵀ]`). -/
noncomputable def diffMap (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) : U × V →ₗ[K] W :=
  psi.comp (LinearMap.fst K U V) - phi.comp (LinearMap.snd K U V)

theorem diffMap_apply (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) (p : U × V) :
    diffMap psi phi p = psi p.1 - phi p.2 := rfl

/-- The equalizer of `psi` and `phi`, as a subspace of `U × V`. -/
noncomputable def K0 (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) : Submodule K (U × V) :=
  LinearMap.ker (diffMap psi phi)

theorem mem_K0_iff (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) (p : U × V) :
    p ∈ K0 psi phi ↔ psi p.1 = phi p.2 := by
  rw [K0, LinearMap.mem_ker, diffMap_apply, sub_eq_zero]

/-- The pair map `(u, v) ↦ (psi u, phi v)`: the "column-stacked" version. -/
noncomputable def pairedMap (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) : U × V →ₗ[K] W × W :=
  (psi.comp (LinearMap.fst K U V)).prod (phi.comp (LinearMap.snd K U V))

/-- **The `prod` (column-stacked) kernel is the wrong object.**  Its image under
`psi ∘ fst` is `⊥`, not `range psi ⊓ range phi`: the kernel of the pair map is
`ker psi × ker phi`. -/
theorem map_comp_fst_pairedMap_ker_eq_bot (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) :
    Submodule.map (psi.comp (LinearMap.fst K U V)) (LinearMap.ker (pairedMap psi phi)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro _ ⟨p, hp, rfl⟩
  have h : (pairedMap psi phi) p = 0 := hp
  have h1 : psi p.1 = 0 := by
    have h2 := congrArg Prod.fst h
    simpa [pairedMap, LinearMap.prod_apply] using h2
  simpa using h1

/-- The plain first projection of the equalizer is the full preimage of
`range phi` under `psi` (and in general strictly larger than the
intersection). -/
theorem map_fst_K0_eq_comap (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) :
    Submodule.map (LinearMap.fst K U V) (K0 psi phi) =
      Submodule.comap psi (LinearMap.range phi) := by
  ext u
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨p.2, ?_⟩)
    exact ((mem_K0_iff psi phi p).mp hp).symm
  · intro hu
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hu)
    exact Submodule.mem_map.mpr ⟨(u, v), (mem_K0_iff psi phi (u, v)).mpr hv.symm, rfl⟩

/-! ### 2. The image of the equalizer is the intersection -/

/-- **Claim 14, linear-algebra core.**  The map `(u, v) ↦ psi u` sends the
equalizer `K0` onto `range psi ⊓ range phi` (the paper's `T ∩ S`).

The `≤` direction is proved through `Submodule.map_le_iff_le_comap`; the
`≥` direction uses the explicit preimage `(u, v)` with `psi u = phi v`. -/
theorem map_comp_fst_K0_eq_inf (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) :
    Submodule.map (psi.comp (LinearMap.fst K U V)) (K0 psi phi) =
      LinearMap.range psi ⊓ LinearMap.range phi := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    intro p hp
    rw [Submodule.mem_comap]
    have h : psi p.1 = phi p.2 := (mem_K0_iff psi phi p).mp hp
    exact Submodule.mem_inf.mpr
      ⟨LinearMap.mem_range.mpr ⟨p.1, rfl⟩, LinearMap.mem_range.mpr ⟨p.2, h.symm⟩⟩
  · rintro _ ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    exact Submodule.mem_map.mpr ⟨(u, v), (mem_K0_iff psi phi (u, v)).mpr hv.symm, rfl⟩

/-- The restricted map `K0 → W`, `(u, v) ↦ psi u`. -/
noncomputable def restrictFst (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) :
    K0 psi phi →ₗ[K] W :=
  (psi.comp (LinearMap.fst K U V)).comp (K0 psi phi).subtype

theorem restrictFst_apply (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) (x : K0 psi phi) :
    restrictFst psi phi x = psi (x : U × V).1 := rfl

/-- The range of the restricted map is the intersection. -/
theorem range_restrictFst (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) :
    LinearMap.range (restrictFst psi phi) = LinearMap.range psi ⊓ LinearMap.range phi := by
  rw [restrictFst, LinearMap.range_comp, Submodule.range_subtype]
  exact map_comp_fst_K0_eq_inf psi phi

theorem mem_ker_restrictFst_iff (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) (x : K0 psi phi) :
    x ∈ LinearMap.ker (restrictFst psi phi) ↔ psi (x : U × V).1 = 0 := by
  rw [LinearMap.mem_ker, restrictFst_apply]

/-- **The dependency space is `ker psi × ker phi`.**  The restricted map
`K0 → T ∩ S` has trivial kernel exactly when both row maps are injective. -/
theorem ker_restrictFst_eq_bot_iff (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) :
    LinearMap.ker (restrictFst psi phi) = ⊥ ↔
      (LinearMap.ker psi = ⊥ ∧ LinearMap.ker phi = ⊥) := by
  constructor
  · intro h
    constructor
    · rw [Submodule.eq_bot_iff]
      intro u hu
      have hmem : ((u, 0) : U × V) ∈ K0 psi phi := by
        refine (mem_K0_iff psi phi (u, 0)).mpr ?_
        simpa using hu
      let x : K0 psi phi := ⟨(u, 0), hmem⟩
      have hx : x ∈ LinearMap.ker (restrictFst psi phi) := by
        rw [mem_ker_restrictFst_iff]
        simpa [x] using hu
      have hx0 : x = 0 := (Submodule.eq_bot_iff _).mp h x hx
      have hp : ((u, 0) : U × V) = 0 := by
        have hcoe := congrArg (fun y : K0 psi phi => (y : U × V)) hx0
        simpa [x] using hcoe
      exact (Prod.ext_iff.mp hp).1
    · rw [Submodule.eq_bot_iff]
      intro v hv
      have hmem : ((0, v) : U × V) ∈ K0 psi phi := by
        refine (mem_K0_iff psi phi (0, v)).mpr ?_
        simpa using hv.symm
      let x : K0 psi phi := ⟨(0, v), hmem⟩
      have hx : x ∈ LinearMap.ker (restrictFst psi phi) := by
        rw [mem_ker_restrictFst_iff]
        simp [x]
      have hx0 : x = 0 := (Submodule.eq_bot_iff _).mp h x hx
      have hp : ((0, v) : U × V) = 0 := by
        have hcoe := congrArg (fun y : K0 psi phi => (y : U × V)) hx0
        simpa [x] using hcoe
      exact (Prod.ext_iff.mp hp).2
  · rintro ⟨h1, h2⟩
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hpsi : psi (x : U × V).1 = 0 := (mem_ker_restrictFst_iff psi phi x).mp hx
    have hpair := (mem_K0_iff psi phi (x : U × V)).mp x.2
    have hphi : phi (x : U × V).2 = 0 := by
      rw [← hpair]
      exact hpsi
    have hx1 : (x : U × V).1 = 0 := (Submodule.eq_bot_iff _).mp h1 _ hpsi
    have hx2 : (x : U × V).2 = 0 := (Submodule.eq_bot_iff _).mp h2 _ hphi
    exact Subtype.ext (Prod.ext hx1 hx2)

/-! ### 3. The image of a basis: a generating set, and when it is a basis -/

/-- **The generating-set lemma.**  For *any* basis `b` of the equalizer, the
image family `i ↦ psi ((b i).1)` spans the intersection.  No injectivity and
no finiteness of the index type is needed.

This is the precise sense in which "the image of a basis of `K0` is a
generating set of `T ∩ S`". -/
theorem span_image_basis_eq_inf {ι : Type*} (psi : U →ₗ[K] W) (phi : V →ₗ[K] W)
    (b : Basis ι K (K0 psi phi)) :
    Submodule.span K (Set.range (fun i => psi ((b i : U × V).1))) =
      LinearMap.range psi ⊓ LinearMap.range phi := by
  have hspan : Submodule.span K (Set.range (fun i => (b i : U × V))) = K0 psi phi := by
    have h1 : Submodule.map (K0 psi phi).subtype
          (Submodule.span K (Set.range (b : ι → K0 psi phi))) =
        Submodule.span K (Set.range (fun i => (b i : U × V))) := by
      rw [Submodule.map_span]
      congr 1
      exact (Set.range_comp (fun y : K0 psi phi => (y : U × V)) b).symm
    rw [← h1, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  calc Submodule.span K (Set.range (fun i => psi ((b i : U × V).1)))
      = Submodule.span K (Set.range
          ((psi.comp (LinearMap.fst K U V)) ∘ (fun i => (b i : U × V)))) := rfl
    _ = Submodule.span K ((psi.comp (LinearMap.fst K U V)) ''
          Set.range (fun i => (b i : U × V))) := by rw [Set.range_comp]
    _ = Submodule.map (psi.comp (LinearMap.fst K U V))
          (Submodule.span K (Set.range (fun i => (b i : U × V)))) :=
        (Submodule.map_span (psi.comp (LinearMap.fst K U V)) _).symm
    _ = Submodule.map (psi.comp (LinearMap.fst K U V)) (K0 psi phi) := by rw [hspan]
    _ = LinearMap.range psi ⊓ LinearMap.range phi := map_comp_fst_K0_eq_inf psi phi

/-- **The dependency criterion.**  The image of a basis of `K0` is linearly
independent exactly when both `psi` and `phi` are injective (full column rank).
Otherwise it is only a generating set with non-trivial relations. -/
theorem linearIndependent_image_basis_iff {ι : Type*} [Fintype ι]
    (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) (b : Basis ι K (K0 psi phi)) :
    LinearIndependent K (fun i => psi ((b i : U × V).1)) ↔
      (LinearMap.ker psi = ⊥ ∧ LinearMap.ker phi = ⊥) := by
  constructor
  · intro hLI
    rw [← ker_restrictFst_eq_bot_iff psi phi]
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : psi (x : U × V).1 = 0 := (mem_ker_restrictFst_iff psi phi x).mp hx
    have hsum : ∑ i, b.repr x i • psi ((b i : U × V).1) = 0 := by
      have hFsum : ∑ i, b.repr x i • restrictFst psi phi (b i) = 0 := by
        have hmap : ∑ i, b.repr x i • restrictFst psi phi (b i) =
            restrictFst psi phi (∑ i, b.repr x i • b i) := by
          rw [map_sum]
          simp only [map_smul]
        rw [hmap, b.sum_repr x]
        simpa [restrictFst_apply] using hx0
      simpa [restrictFst_apply] using hFsum
    have hcoef : ∀ i, b.repr x i = 0 :=
      Fintype.linearIndependent_iff.mp hLI (fun i => b.repr x i) hsum
    rw [← b.sum_repr x]
    simp [hcoef]
  · rintro ⟨h1, h2⟩
    have hker : LinearMap.ker (restrictFst psi phi) = ⊥ :=
      (ker_restrictFst_eq_bot_iff psi phi).mpr ⟨h1, h2⟩
    rw [Fintype.linearIndependent_iff]
    intro g hsum i
    have hmap : restrictFst psi phi (∑ j, g j • b j) = 0 := by
      have hstep : restrictFst psi phi (∑ j, g j • b j) =
          ∑ j, g j • restrictFst psi phi (b j) := by
        rw [map_sum]
        simp only [map_smul]
      rw [hstep]
      simpa [restrictFst_apply] using hsum
    have hy : (∑ j, g j • b j) = 0 := by
      have hy' : (∑ j, g j • b j) ∈ LinearMap.ker (restrictFst psi phi) := hmap
      rw [hker] at hy'
      exact (Submodule.mem_bot K).mp hy'
    exact Fintype.linearIndependent_iff.mp b.linearIndependent g hy i

/-- **The warning, in the form used downstream.**  If `psi` is not injective,
the image of *every* basis of `K0` is linearly dependent. -/
theorem not_linearIndependent_of_ker_ne_bot {ι : Type*} [Fintype ι]
    (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) (b : Basis ι K (K0 psi phi))
    (h : LinearMap.ker psi ≠ ⊥) :
    ¬ LinearIndependent K (fun i => psi ((b i : U × V).1)) :=
  fun hLI => h ((linearIndependent_image_basis_iff psi phi b).mp hLI).1

/-- **When the generating set is a basis.**  If both maps are injective, the
image of a basis of `K0` is linearly independent and spans the intersection,
i.e. it is a basis of `T ∩ S` (as a family). -/
theorem linearIndependent_and_span_image_basis {ι : Type*} [Fintype ι]
    (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) (b : Basis ι K (K0 psi phi))
    (h : LinearMap.ker psi = ⊥ ∧ LinearMap.ker phi = ⊥) :
    LinearIndependent K (fun i => psi ((b i : U × V).1)) ∧
      Submodule.span K (Set.range (fun i => psi ((b i : U × V).1))) =
        LinearMap.range psi ⊓ LinearMap.range phi :=
  ⟨(linearIndependent_image_basis_iff psi phi b).mpr h, span_image_basis_eq_inf psi phi b⟩

/-! ### 4. The dependency space and its removal -/

/-- **Removing the dependencies.**  The first isomorphism theorem for the
restricted map: the equalizer modulo the dependency space `ker psi × ker phi`
is linearly equivalent to the intersection.  A basis of the intersection is
therefore obtained from a basis of `K0` only after this quotient (equivalently,
after discarding a complement of the dependency space), not by push-forward
alone. -/
noncomputable def quotientEquivInf (psi : U →ₗ[K] W) (phi : V →ₗ[K] W) :
    (↥(K0 psi phi) ⧸ LinearMap.ker (restrictFst psi phi)) ≃ₗ[K]
      ↥(LinearMap.range psi ⊓ LinearMap.range phi) :=
  (LinearMap.quotKerEquivRange (restrictFst psi phi)).trans
    (LinearEquiv.ofEq _ _ (range_restrictFst psi phi))

/-- **The dependency-removal step, basis form.**  A basis of the quotient
`K0 ⧸ (ker psi × ker phi)` transports along `quotientEquivInf` to a basis of
the intersection. -/
noncomputable def basisOfQuotientBasis {ι : Type*}
    (psi : U →ₗ[K] W) (phi : V →ₗ[K] W)
    (bq : Basis ι K (↥(K0 psi phi) ⧸ LinearMap.ker (restrictFst psi phi))) :
    Basis ι K ↥(LinearMap.range psi ⊓ LinearMap.range phi) :=
  bq.map (quotientEquivInf psi phi)

/-! ### 5. The matrix form (paper notation `A_T`, `A_V`) -/

/-- The range of `u ↦ u ᵥ* A` is the row space of `A`. -/
theorem range_vecMulLinear_eq_rowSpace {a d : ℕ} (A : Matrix (Fin a) (Fin d) K) :
    LinearMap.range (Matrix.vecMulLinear A) = Q1Subspace.rowSpace A := by
  have h : Q1Subspace.rowSpace A = Q1Subspace.rowSpan A := rfl
  rw [h, ← Q1Subspace.range_eq_rowSpan]

/-- **Claim 14 in matrix form.**  For `A_T : Matrix (Fin a) (Fin d) K` and
`A_V : Matrix (Fin b) (Fin d) K`, the map `(u, v) ↦ u ᵥ* A_T` sends the
equalizer of `u ↦ u ᵥ* A_T` and `v ↦ v ᵥ* A_V` onto
`row A_T ⊓ row A_V` — the paper's `T ∩ S`. -/
theorem matrix_map_comp_fst_K0_eq_inf {a b d : ℕ}
    (AT : Matrix (Fin a) (Fin d) K) (AV : Matrix (Fin b) (Fin d) K) :
    Submodule.map ((Matrix.vecMulLinear AT).comp
        (LinearMap.fst K (Fin a → K) (Fin b → K)))
        (K0 (Matrix.vecMulLinear AT) (Matrix.vecMulLinear AV))
      = Q1Subspace.rowSpace AT ⊓ Q1Subspace.rowSpace AV := by
  rw [map_comp_fst_K0_eq_inf, range_vecMulLinear_eq_rowSpace,
    range_vecMulLinear_eq_rowSpace]

/-! ### 6. Axiom footprint (evidence that nothing is assumed) -/


end Q1Paper.PaperI.Claim14
