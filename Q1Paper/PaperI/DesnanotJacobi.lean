
import Q1Paper.PaperI.BareissBase
import Q1Paper.PaperI.CauchyBinet
import Q1Paper.PaperI.MinorFamilyBridge

/-!
Q1Paper/PaperI/DesnanotJacobi.lean

**The bordered Desnanot–Jacobi (Sylvester) identity** — the one piece the Bareiss
formalisation of Paper I was missing (`Q1Paper/PaperI/BareissBase.lean` proves the
`k = 0, 1` instances `sylvester_two`, `sylvester_three` only).

Main results (over a field `K`, with no hypothesis on the matrix, no injectivity and
no invertibility assumptions):

* `dj_block` — the identity in block form.  For `k : ℕ`, blocks
  `A₁₁ : Matrix (Fin k) (Fin k) K`, `B : Matrix (Fin k) (Fin 2) K`,
  `C : Matrix (Fin 2) (Fin k) K`, `D : Matrix (Fin 2) (Fin 2) K`, and the four
  **bordered `(k+1) × (k+1)` minors** `bBorder u v = det A(I ∪ {u}, J ∪ {v})`,
  `u v : Fin 2`:

    `det (fromBlocks A₁₁ B C D) * det A₁₁ = bBorder 0 0 * bBorder 1 1 - bBorder 0 1 * bBorder 1 0`.

  Here `A₁₁` is the inner `k × k` minor `det A(I,J)`; the two `inr` indices of the
  `⊕` are the four extra indices outside `I` and `J` (`u` and `v` each range over two
  values).

* `desnanot_jacobi_minors` — the general index-tuple form on `Fin n`: for **arbitrary**
  maps `r c : Fin k ⊕ Fin 2 → Fin n` enumerating the rows and columns (the first `k`
  of each being `I` resp. `J`, the last two being the extras),

    `det A(r,c) * det A(r∘inl, c∘inl)`
      `= det A(r₀,c₀) * det A(r₁,c₁) - det A(r₀,c₁) * det A(r₁,c₀)`,

  where `r₀, r₁` (resp. `c₀, c₁`) are `r` (resp. `c`) with only the `u`-th extra index
  adjoined.

* `desnanot_jacobi_prefix` — the principal-prefix spelling on `Fin (k+2)`:
  `I = J = {0, …, k-1}`, extras `k` and `k+1`, all index sets in increasing order.
  This is the instance the Bareiss step at pivot `k+2` needs.

Proof route (Schur complement + one deformation; no Cauchy–Binet):

* `dj_block_of_invertible` — over any commutative ring, with the top-left block
  invertible: expand `det A` by `Matrix.det_fromBlocks₁₁` as
  `det A₁₁ * det (D - C A₁₁⁻¹ B)`; the four bordered minors are `(k+1) × (k+1)` block
  matrices whose determinant expands the same way; close with `Matrix.det_fin_two` and
  `ring`;
* `dj_block` — over a field, for **arbitrary** `A₁₁`: deform `A₁₁` to
  `charmatrix (-A₁₁) = X • 1 + A₁₁` over `K[X]`.  Its determinant is the (monic, hence
  nonzero) characteristic polynomial `(-A₁₁).charpoly`, so the identity holds over the
  fraction field `FractionRing K[X]` by the invertible case; it descends to `K[X]` by
  injectivity of `K[X] → FractionRing K[X]` (`dj_of_map_injective`) and specialises back
  at `X = 0` (`dj_map` with `Polynomial.evalRingHom 0`, using `charmatrix M ↦ -M`);
* the index-tuple and prefix forms are transports of `dj_block` along
  `submatrix` / `finSumFinEquiv`, determinants being invariant under reindexing
  (`Matrix.det_submatrix_equiv_self`).

No `sorry`, no `admit`, no new axioms (the only axioms used are `propext`,
`Classical.choice`, `Quot.sound`).  Check with
  `lake env lean Q1Paper/PaperI/DesnanotJacobi.lean`
-/


open Matrix Polynomial

namespace Q1Paper.PaperI

/-! ## 1.  Transport of block expressions along ring homomorphisms -/

/-- Entrywise mapping of a ring hom commutes with `Matrix.fromBlocks`. -/
lemma fromBlocks_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {l m n o : Type*} (A : Matrix n l R) (B : Matrix n m R) (C : Matrix o l R) (D : Matrix o m R) :
    (fromBlocks A B C D).map φ = fromBlocks (A.map φ) (B.map φ) (C.map φ) (D.map φ) := by
  ext i j
  cases i <;> cases j <;> rfl

/-- `φ` commutes with `det`, in the `.map` spelling. -/
lemma map_det_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : Type*}
    [Fintype n] [DecidableEq n] (M : Matrix n n R) : φ M.det = (M.map φ).det :=
  RingHom.map_det φ M

/-! ## 2.  Bordered minors of a block matrix -/

/-- The **bordered `(k+1) × (k+1)` minor** of the block matrix `fromBlocks A₁₁ B C D`
obtained by adjoining the row `u` (an `inr` index, i.e. an index outside the block `A₁₁`)
and the column `v`: this is `det A(I ∪ {u}, J ∪ {v})` in the notation of the identity. -/
noncomputable def bBorder (k : ℕ) {R : Type*} [CommRing R] (A₁₁ : Matrix (Fin k) (Fin k) R)
    (B : Matrix (Fin k) (Fin 2) R) (C : Matrix (Fin 2) (Fin k) R) (D : Matrix (Fin 2) (Fin 2) R)
    (u v : Fin 2) : R :=
  (fromBlocks A₁₁ (B.submatrix id (fun _ : Fin 1 => v)) (C.submatrix (fun _ : Fin 1 => u) id)
    (D.submatrix (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))).det

/-- `bBorder` commutes with a ring homomorphism. -/
lemma bBorder_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ)
    (A₁₁ : Matrix (Fin k) (Fin k) R) (B : Matrix (Fin k) (Fin 2) R) (C : Matrix (Fin 2) (Fin k) R)
    (D : Matrix (Fin 2) (Fin 2) R) (u v : Fin 2) :
    bBorder k (A₁₁.map φ) (B.map φ) (C.map φ) (D.map φ) u v = φ (bBorder k A₁₁ B C D u v) := by
  unfold bBorder
  simp only [map_det_map, fromBlocks_map, submatrix_map]

/-- **Forward transport** of the block identity along an arbitrary ring homomorphism. -/
lemma dj_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ)
    (A₁₁ : Matrix (Fin k) (Fin k) R) (B : Matrix (Fin k) (Fin 2) R) (C : Matrix (Fin 2) (Fin k) R)
    (D : Matrix (Fin 2) (Fin 2) R)
    (H : (fromBlocks A₁₁ B C D).det * A₁₁.det
      = bBorder k A₁₁ B C D 0 0 * bBorder k A₁₁ B C D 1 1
        - bBorder k A₁₁ B C D 0 1 * bBorder k A₁₁ B C D 1 0) :
    (fromBlocks (A₁₁.map φ) (B.map φ) (C.map φ) (D.map φ)).det * (A₁₁.map φ).det
      = bBorder k (A₁₁.map φ) (B.map φ) (C.map φ) (D.map φ) 0 0
          * bBorder k (A₁₁.map φ) (B.map φ) (C.map φ) (D.map φ) 1 1
        - bBorder k (A₁₁.map φ) (B.map φ) (C.map φ) (D.map φ) 0 1
          * bBorder k (A₁₁.map φ) (B.map φ) (C.map φ) (D.map φ) 1 0 := by
  simpa only [map_sub, map_mul, map_det_map, ← bBorder_map, fromBlocks_map] using congrArg φ H

/-- **Backward transport** of the block identity along an injective ring homomorphism. -/
lemma dj_of_map_injective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (k : ℕ)
    (A₁₁ : Matrix (Fin k) (Fin k) R) (B : Matrix (Fin k) (Fin 2) R) (C : Matrix (Fin 2) (Fin k) R)
    (D : Matrix (Fin 2) (Fin 2) R)
    (H : (fromBlocks (A₁₁.map φ) (B.map φ) (C.map φ) (D.map φ)).det * (A₁₁.map φ).det
      = bBorder k (A₁₁.map φ) (B.map φ) (C.map φ) (D.map φ) 0 0
          * bBorder k (A₁₁.map φ) (B.map φ) (C.map φ) (D.map φ) 1 1
        - bBorder k (A₁₁.map φ) (B.map φ) (C.map φ) (D.map φ) 0 1
          * bBorder k (A₁₁.map φ) (B.map φ) (C.map φ) (D.map φ) 1 0) :
    (fromBlocks A₁₁ B C D).det * A₁₁.det
      = bBorder k A₁₁ B C D 0 0 * bBorder k A₁₁ B C D 1 1
        - bBorder k A₁₁ B C D 0 1 * bBorder k A₁₁ B C D 1 0 := by
  refine hφ ?_
  simpa only [map_sub, map_mul, map_det_map, ← bBorder_map, fromBlocks_map] using H

/-! ## 3.  The identity with invertible top-left block -/

/-- **Bordered Desnanot–Jacobi, invertible top-left block.**  Over any commutative ring,
if `A₁₁` is invertible then

`det (fromBlocks A₁₁ B C D) * det A₁₁ = bBorder 0 0 * bBorder 1 1 - bBorder 0 1 * bBorder 1 0`.

Proof: `Matrix.det_fromBlocks₁₁` for `A` and for each of the four bordered minors (a
one-column/one-row Schur complement), then `Matrix.det_fin_two` and `ring`. -/
theorem dj_block_of_invertible (k : ℕ) {R : Type*} [CommRing R]
    (A₁₁ : Matrix (Fin k) (Fin k) R) [Invertible A₁₁] (B : Matrix (Fin k) (Fin 2) R)
    (C : Matrix (Fin 2) (Fin k) R) (D : Matrix (Fin 2) (Fin 2) R) :
    (fromBlocks A₁₁ B C D).det * A₁₁.det
      = bBorder k A₁₁ B C D 0 0 * bBorder k A₁₁ B C D 1 1
        - bBorder k A₁₁ B C D 0 1 * bBorder k A₁₁ B C D 1 0 := by
  have e : ∀ (u v : Fin 2), bBorder k A₁₁ B C D u v = A₁₁.det * (D - C * ⅟A₁₁ * B) u v := by
    intro u v
    rw [bBorder, det_fromBlocks₁₁ A₁₁ _ _ _, Matrix.det_fin_one]
    simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.submatrix_apply]
  rw [det_fromBlocks₁₁ A₁₁ B C D, e 0 0, e 0 1, e 1 0, e 1 1, Matrix.det_fin_two]
  ring

/-- The same, over a field, under the hypothesis `det A₁₁ ≠ 0`. -/
theorem dj_block_of_det_ne_zero (k : ℕ) {K : Type*} [Field K]
    (A₁₁ : Matrix (Fin k) (Fin k) K) (B : Matrix (Fin k) (Fin 2) K)
    (C : Matrix (Fin 2) (Fin k) K) (D : Matrix (Fin 2) (Fin 2) K) (h : A₁₁.det ≠ 0) :
    (fromBlocks A₁₁ B C D).det * A₁₁.det
      = bBorder k A₁₁ B C D 0 0 * bBorder k A₁₁ B C D 1 1
        - bBorder k A₁₁ B C D 0 1 * bBorder k A₁₁ B C D 1 0 := by
  letI : Invertible A₁₁ := Matrix.invertibleOfIsUnitDet A₁₁ (isUnit_iff_ne_zero.mpr h)
  exact dj_block_of_invertible k A₁₁ B C D

/-! ## 4.  The identity in general (no hypothesis on `A₁₁`) -/

/-- **Bordered Desnanot–Jacobi (block form).**  For a field `K`, a natural number `k`
and arbitrary blocks `A₁₁ B C D`:

`det (fromBlocks A₁₁ B C D) * det A₁₁ = bBorder 0 0 * bBorder 1 1 - bBorder 0 1 * bBorder 1 0`.

No invertibility hypothesis: the singular case is reached by deforming `A₁₁` to
`charmatrix (-A₁₁) = X • 1 + A₁₁` over `K[X]` and specialising `X = 0`. -/
theorem dj_block (k : ℕ) {K : Type*} [Field K]
    (A₁₁ : Matrix (Fin k) (Fin k) K) (B : Matrix (Fin k) (Fin 2) K)
    (C : Matrix (Fin 2) (Fin k) K) (D : Matrix (Fin 2) (Fin 2) K) :
    (fromBlocks A₁₁ B C D).det * A₁₁.det
      = bBorder k A₁₁ B C D 0 0 * bBorder k A₁₁ B C D 1 1
        - bBorder k A₁₁ B C D 0 1 * bBorder k A₁₁ B C D 1 0 := by
  by_cases h : A₁₁.det = 0
  · -- deform the top-left block to `A₁₁ + X • 1` over `K[X]`
    set A' : Matrix (Fin k) (Fin k) (Polynomial K) := Matrix.charmatrix (-A₁₁) with hA'def
    set B' : Matrix (Fin k) (Fin 2) (Polynomial K) := B.map (algebraMap K (Polynomial K)) with hB'def
    set C' : Matrix (Fin 2) (Fin k) (Polynomial K) := C.map (algebraMap K (Polynomial K)) with hC'def
    set D' : Matrix (Fin 2) (Fin 2) (Polynomial K) := D.map (algebraMap K (Polynomial K)) with hD'def
    have hchar : A'.det = (-A₁₁).charpoly := by rw [hA'def]; exact coeff_inj.mp rfl
    have hA'det : A'.det ≠ 0 := by
      rw [hchar]
      exact (Matrix.charpoly_monic (-A₁₁)).ne_zero
    -- the identity over the fraction field of `K[X]`
    have hFkey := dj_block_of_det_ne_zero k
      (A'.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))))
      (B'.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))))
      (C'.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))))
      (D'.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))))
      (by
        rw [← map_det_map]
        exact fun h0 => hA'det (IsFractionRing.injective (Polynomial K)
          (FractionRing (Polynomial K)) (by rw [h0, map_zero])))
    -- descend to `K[X]`
    have key : (fromBlocks A' B' C' D').det * A'.det
        = bBorder k A' B' C' D' 0 0 * bBorder k A' B' C' D' 1 1
          - bBorder k A' B' C' D' 0 1 * bBorder k A' B' C' D' 1 0 :=
      dj_of_map_injective (algebraMap (Polynomial K) (FractionRing (Polynomial K)))
        (IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))) k A' B' C' D' hFkey
    -- specialise `X = 0`, where `charmatrix (-A₁₁) ↦ A₁₁`
    have hA'g : A'.map (Polynomial.evalRingHom (0 : K)) = A₁₁ := by
      rw [hA'def]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.charmatrix, Matrix.map_apply, hij]
    have hB'g : B'.map (Polynomial.evalRingHom (0 : K)) = B := by
      rw [hB'def]
      ext i j
      simp [Matrix.map_apply]
    have hC'g : C'.map (Polynomial.evalRingHom (0 : K)) = C := by
      rw [hC'def]
      ext i j
      simp [Matrix.map_apply]
    have hD'g : D'.map (Polynomial.evalRingHom (0 : K)) = D := by
      rw [hD'def]
      ext i j
      simp [Matrix.map_apply]
    have hspec := dj_map (Polynomial.evalRingHom (0 : K)) k A' B' C' D' key
    simpa only [hA'g, hB'g, hC'g, hD'g] using hspec
  · exact dj_block_of_det_ne_zero k A₁₁ B C D h

/-! ## 5.  The identity for an arbitrary pair of index tuples on `Fin n` -/

section Tuple

variable {K : Type*} [Field K] {n : ℕ}

/-- The first `k` indices of a `Fin k ⊕ Fin 2` enumeration: the index set `I` (resp. `J`). -/
def aIdx {k : ℕ} (r : Fin k ⊕ Fin 2 → Fin n) : Fin k → Fin n := fun i => r (Sum.inl i)

/-- The `k+1` indices obtained by adjoining the `u`-th extra index: the index set
`I ∪ {u}` (resp. `J ∪ {v}`), in the order given by `r`. -/
def bIdx {k : ℕ} (r : Fin k ⊕ Fin 2 → Fin n) (u : Fin 2) : Fin k ⊕ Fin 1 → Fin n :=
  fun x => r (Sum.map id (fun _ : Fin 1 => u) x)

/-- **Bordered Desnanot–Jacobi for an arbitrary pair of index tuples.**  Let
`r c : Fin k ⊕ Fin 2 → Fin n` enumerate `k+2` rows and `k+2` columns; write
`A(r, c) = det A(r, c)` for the determinant of the submatrix on those rows and columns,
in the order given by `r` and `c`.  Then

`A(r,c) * A(r∘inl, c∘inl) = A(r₀,c₀) * A(r₁,c₁) - A(r₀,c₁) * A(r₁,c₀)`,

where `r_u := bIdx r u` is `r` with only the `u`-th extra index kept, i.e. this is the
bordered identity with inner sets `I = r(inl ·)`, `J = c(inl ·)` and the four extra
indices `r(inr 0), r(inr 1), c(inr 0), c(inr 1)` — all four outside `I` and `J`.

Nothing is assumed about `r` and `c` (not even injectivity): degenerate index tuples
make both sides degenerate consistently, exactly as in `sylvester_two`.

The minors are read in the order given by `r` and `c` (that is what the determinant of
a `submatrix` computes).  Rewriting the identity in the convention "indices in
increasing order" costs the product of the row and column permutation signs, which
equals `(-1)^([i>p]+[j>q])`; that conversion is *not* formalised here (for the prefix
form below the extras are already increasing, so no sign appears). -/
theorem desnanot_jacobi_minors (k : ℕ) (A : Matrix (Fin n) (Fin n) K)
    (r c : Fin k ⊕ Fin 2 → Fin n) :
    (A.submatrix r c).det * (A.submatrix (aIdx r) (aIdx c)).det
      = (A.submatrix (bIdx r 0) (bIdx c 0)).det * (A.submatrix (bIdx r 1) (bIdx c 1)).det
        - (A.submatrix (bIdx r 0) (bIdx c 1)).det * (A.submatrix (bIdx r 1) (bIdx c 0)).det := by
  -- the block decomposition of `A.submatrix r c`
  have hfrom : fromBlocks (A.submatrix (aIdx r) (aIdx c))
      (A.submatrix (aIdx r) (fun t => c (Sum.inr t)))
      (A.submatrix (fun t => r (Sum.inr t)) (aIdx c))
      (A.submatrix (fun t => r (Sum.inr t)) (fun t => c (Sum.inr t)))
      = A.submatrix r c := by
    ext i j
    cases i <;> cases j <;> rfl
  -- each bordered minor is the corresponding submatrix of `A`
  have hbord : ∀ u v : Fin 2,
      bBorder k (A.submatrix (aIdx r) (aIdx c))
        (A.submatrix (aIdx r) (fun t => c (Sum.inr t)))
        (A.submatrix (fun t => r (Sum.inr t)) (aIdx c))
        (A.submatrix (fun t => r (Sum.inr t)) (fun t => c (Sum.inr t))) u v
      = (A.submatrix (bIdx r u) (bIdx c v)).det := by
    intro u v
    rw [bBorder]
    congr 1
    ext i j
    cases i <;> cases j <;> rfl
  have key := dj_block k (A.submatrix (aIdx r) (aIdx c))
    (A.submatrix (aIdx r) (fun t => c (Sum.inr t)))
    (A.submatrix (fun t => r (Sum.inr t)) (aIdx c))
    (A.submatrix (fun t => r (Sum.inr t)) (fun t => c (Sum.inr t)))
  rw [hfrom] at key
  rw [hbord 0 0, hbord 1 1, hbord 0 1, hbord 1 0] at key
  exact key

end Tuple

/-! ## 6.  The principal-prefix form on `Fin (k+2)` -/

section Prefix

variable {K : Type*} [Field K]

/-- The **increasing enumeration** of `{0, …, k-1}` inside `Fin (k+2)`. -/
def pEmb (k : ℕ) : Fin k → Fin (k + 2) := fun i => ⟨i.val, by omega⟩

/-- The increasing enumeration of `{0, …, k}` inside `Fin (k+2)`. -/
def pCast (k : ℕ) : Fin (k + 1) → Fin (k + 2) := fun i => ⟨i.val, by omega⟩

/-- The increasing enumeration of `{0, …, k-1, k+1}` inside `Fin (k+2)`: the prefix of
length `k+1` with its last entry `k` replaced by `k+1` (so `i ↦ i` for `i < k` and
`k ↦ k+1`).  It is written as the image of the corresponding `Fin k ⊕ Fin 1` index under
`finSumFinEquiv`, which is what the transport proof uses. -/
def pSwap (k : ℕ) : Fin (k + 1) → Fin (k + 2) :=
  fun i => finSumFinEquiv (Sum.map id (fun _ : Fin 1 => (1 : Fin 2)) (finSumFinEquiv.symm i))

lemma pEmb_eq (k : ℕ) : pEmb k = fun i => finSumFinEquiv (Sum.inl i) := by
  funext i
  exact Fin.ext rfl

lemma pCast_char (k : ℕ) (i : Fin k ⊕ Fin 1) :
    pCast k (finSumFinEquiv i)
      = finSumFinEquiv (Sum.map id (fun _ : Fin 1 => (0 : Fin 2)) i) := by
  rcases i with a | t
  · exact Fin.ext rfl
  · have ht : t = 0 := Subsingleton.elim t 0
    subst ht
    exact Fin.ext rfl

lemma pSwap_char (k : ℕ) (i : Fin k ⊕ Fin 1) :
    pSwap k (finSumFinEquiv i)
      = finSumFinEquiv (Sum.map id (fun _ : Fin 1 => (1 : Fin 2)) i) := by
  simp only [pSwap, Equiv.symm_apply_apply]

/-- **Bordered Desnanot–Jacobi, principal-prefix form.**  For `A : Matrix (Fin (k+2)) (Fin (k+2)) K`
over a field `K`:

`det A * det A({0,…,k-1}, {0,…,k-1})`
  `= det A({0,…,k}, {0,…,k}) * det A({0,…,k-1,k+1}, {0,…,k-1,k+1})`
  `  - det A({0,…,k}, {0,…,k-1,k+1}) * det A({0,…,k-1,k+1}, {0,…,k})`,

every index set being taken in increasing order (`pEmb`, `pCast`, `pSwap` are the
increasing enumerations of `{0,…,k-1}`, `{0,…,k}` and `{0,…,k-1,k+1}`).  This is the
`I = J = {0, …, k-1}`, `i = j = k`, `p = q = k+1` instance of the bordered
Desnanot–Jacobi identity — exactly the identity the Bareiss step at pivot `k+2` needs
(`k = 0` is the `2 × 2` instance `bStepNum_zero_eq_minor2`). -/
theorem desnanot_jacobi_prefix (k : ℕ) (A : Matrix (Fin (k + 2)) (Fin (k + 2)) K) :
    A.det * (A.submatrix (pEmb k) (pEmb k)).det
      = (A.submatrix (pCast k) (pCast k)).det * (A.submatrix (pSwap k) (pSwap k)).det
        - (A.submatrix (pCast k) (pSwap k)).det * (A.submatrix (pSwap k) (pCast k)).det := by
  -- reindex `A` to `Fin k ⊕ Fin 2` and cut it into blocks
  set M : Matrix (Fin k ⊕ Fin 2) (Fin k ⊕ Fin 2) K :=
    A.submatrix finSumFinEquiv finSumFinEquiv with hM
  set A₁₁ : Matrix (Fin k) (Fin k) K := M.submatrix (fun i => Sum.inl i) (fun i => Sum.inl i)
    with hA₁₁def
  set Bb : Matrix (Fin k) (Fin 2) K := M.submatrix (fun i => Sum.inl i) (fun i => Sum.inr i)
    with hBbdef
  set Cc : Matrix (Fin 2) (Fin k) K := M.submatrix (fun i => Sum.inr i) (fun i => Sum.inl i)
    with hCcdef
  set Dd : Matrix (Fin 2) (Fin 2) K := M.submatrix (fun i => Sum.inr i) (fun i => Sum.inr i)
    with hDddef
  have hblocks : M = fromBlocks A₁₁ Bb Cc Dd := by
    rw [hA₁₁def, hBbdef, hCcdef, hDddef]
    ext i j
    cases i <;> cases j <;> rfl
  -- a bordered `(k+1) × (k+1)` minor of `A` is the corresponding `bBorder` of the blocks
  have hminor : ∀ (u v : Fin 2) (fr fc : Fin (k + 1) → Fin (k + 2)),
      (∀ i : Fin k ⊕ Fin 1,
        fr (finSumFinEquiv i) = finSumFinEquiv (Sum.map id (fun _ : Fin 1 => u) i)) →
      (∀ i : Fin k ⊕ Fin 1,
        fc (finSumFinEquiv i) = finSumFinEquiv (Sum.map id (fun _ : Fin 1 => v) i)) →
      (A.submatrix fr fc).det = bBorder k A₁₁ Bb Cc Dd u v := by
    intro u v fr fc hr hc
    have hassoc : (A.submatrix fr fc).submatrix
        (finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1))
        (finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1))
        = M.submatrix (Sum.map id (fun _ : Fin 1 => u)) (Sum.map id (fun _ : Fin 1 => v)) := by
      ext i j
      rw [Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.submatrix_apply, hM,
        Matrix.submatrix_apply, hr i, hc j]
    have hblocks' : M.submatrix (Sum.map id (fun _ : Fin 1 => u))
        (Sum.map id (fun _ : Fin 1 => v))
        = fromBlocks A₁₁ (Bb.submatrix id (fun _ : Fin 1 => v))
            (Cc.submatrix (fun _ : Fin 1 => u) id)
            (Dd.submatrix (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) := by
      rw [hblocks]
      ext i j
      cases i <;> cases j <;> rfl
    calc (A.submatrix fr fc).det
        = ((A.submatrix fr fc).submatrix
            (finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1))
            (finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1))).det :=
          (det_submatrix_equiv_self (finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1)) _).symm
      _ = (M.submatrix (Sum.map id (fun _ : Fin 1 => u))
            (Sum.map id (fun _ : Fin 1 => v))).det := by rw [hassoc]
      _ = bBorder k A₁₁ Bb Cc Dd u v := by rw [bBorder, hblocks']
  have h00 : (A.submatrix (pCast k) (pCast k)).det = bBorder k A₁₁ Bb Cc Dd 0 0 :=
    hminor 0 0 (pCast k) (pCast k) (fun i => pCast_char k i) (fun i => pCast_char k i)
  have h11 : (A.submatrix (pSwap k) (pSwap k)).det = bBorder k A₁₁ Bb Cc Dd 1 1 :=
    hminor 1 1 (pSwap k) (pSwap k) (fun i => pSwap_char k i) (fun i => pSwap_char k i)
  have h01 : (A.submatrix (pCast k) (pSwap k)).det = bBorder k A₁₁ Bb Cc Dd 0 1 :=
    hminor 0 1 (pCast k) (pSwap k) (fun i => pCast_char k i) (fun i => pSwap_char k i)
  have h10 : (A.submatrix (pSwap k) (pCast k)).det = bBorder k A₁₁ Bb Cc Dd 1 0 :=
    hminor 1 0 (pSwap k) (pCast k) (fun i => pSwap_char k i) (fun i => pCast_char k i)
  -- the inner `k × k` minor is `A₁₁`, and `det A` is `M.det`
  have hinner : (A.submatrix (pEmb k) (pEmb k)).det = A₁₁.det := by
    have h1 : A.submatrix (pEmb k) (pEmb k)
        = M.submatrix (fun i => Sum.inl i) (fun i => Sum.inl i) := by
      ext i j
      simp only [Matrix.submatrix_apply, hM, pEmb_eq]
    rw [h1, hA₁₁def]
  -- assemble
  have key := dj_block k A₁₁ Bb Cc Dd
  rw [← hblocks] at key
  rw [hM, det_submatrix_equiv_self (finSumFinEquiv : Fin k ⊕ Fin 2 ≃ Fin (k + 2)) A] at key
  rw [← hinner] at key
  rw [← h00, ← h11, ← h01, ← h10] at key
  exact key

end Prefix

end Q1Paper.PaperI
