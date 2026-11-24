import Q1Paper.Q1RowSpace
import Q1Paper.PaperI.Claims38
import Q1Paper.PaperI.CompressionMatrix
import Q1Paper.PaperI.RankFactorization
import Q1Paper.Window
import Q1Paper.PaperI.Claim11Final

/-!
# Chart completeness, step 1

The external review of the algorithm verification asks, before anything else, for the
**equivalence between the original feasibility problem and the finite chart system** of
`eq:phi`.  The forward direction (`Feasible L → a Φ-point`) decomposes into small steps; this
file proves the first and most specific one.

With `N` a matrix whose columns lie in `ker[C; CA]` (so `C N = 0` and `C A N = 0`), `H = L N`,
`H_A = L A N`, the paper's `(5a)` — in row-space form
`row[LA; L; CA; C] = row[L; CA; C]` — implies

  `row(H_A) ≤ row(H)`.

This is exactly what lets **one** matrix `B` serve both `H = X B` and `H_A = G B` in `eq:phi`
(items (iii) and (iv)); without it the two factorizations would need different `B`.

The proof is the paper's one-liner: `(5a)` gives `row(LA) ≤ row[L; CA; C]`; right-multiplying by
`N` turns each row space into its image under `vecMulLinear N`, and `[L; CA; C] * N` is
`[H; 0; 0]` because `N` annihilates `C` and `C A`.
-/

namespace Q1Paper.ScratchChartComplete

open Q1Paper Q1Subspace Q1Paper.PaperI Q1Paper.PaperI.RankFactorization

variable {K : Type*} [Field K]
variable {p q n k : ℕ}

/-- **Chart completeness, step 1.**  If `N` annihilates `C` and `C A`, and `(5a)` holds in
row-space form, then `row(L A N) ≤ row(L N)`. -/
theorem row_LA_mul_le_row_L_mul (A : Matrix (Fin n) (Fin n) K) (C : Matrix (Fin p) (Fin n) K)
    (L : Matrix (Fin q) (Fin n) K) (N : Matrix (Fin n) (Fin k) K)
    (hCN : C * N = 0) (hCAN : C * A * N = 0)
    (h5a : rowSpace (Matrix.fromRows (L * A) (Matrix.fromRows L (Matrix.fromRows (C * A) C)))
        = rowSpace (Matrix.fromRows L (Matrix.fromRows (C * A) C))) :
    rowSpace (L * A * N) ≤ rowSpace (L * N) := by
  -- (5a) gives `row(L A) ≤ row[L; CA; C]`
  have hle : rowSpace (L * A) ≤ rowSpace (Matrix.fromRows L (Matrix.fromRows (C * A) C)) := by
    calc rowSpace (L * A)
        ≤ rowSpace (L * A) ⊔ rowSpace (Matrix.fromRows L (Matrix.fromRows (C * A) C)) :=
          le_sup_left
      _ = rowSpace (Matrix.fromRows (L * A) (Matrix.fromRows L (Matrix.fromRows (C * A) C))) :=
          (rowSpace_fromRows _ _).symm
      _ = rowSpace (Matrix.fromRows L (Matrix.fromRows (C * A) C)) := h5a
  -- push the inclusion through right multiplication by `N`
  have hmap := Submodule.map_mono (f := Matrix.vecMulLinear N) hle
  rw [← rowSpace_mul_eq_map, ← rowSpace_mul_eq_map] at hmap
  -- `[L; CA; C] * N = [L N; (CA) N; C N] = [H; 0; 0]`, whose row space is `row(H)`
  rw [Matrix.fromRows_mul, Matrix.fromRows_mul, rowSpace_fromRows, rowSpace_fromRows,
    hCN, hCAN] at hmap
  have hzero : rowSpace (0 : Matrix (Fin p) (Fin k) K) = ⊥ := by
    rw [Q1Subspace.rowSpace, Submodule.span_eq_bot]
    rintro _ ⟨i, rfl⟩
    rfl
  rw [hzero] at hmap
  simpa using hmap

/-- **Chart completeness, steps 2–3.**  If `row(H_A) ≤ row(H)` and `rank H = ω`, there are
`X` (`m × ω`), `B` (`ω × k`) and `G` (`m × ω`) with

  `H = X * B`,  `H_A = G * B`,  `rank X = ω`,

and a left inverse `X_L` of `X`.  This is items (iii)/(iv) of `eq:phi` in matrix form: the single
`B` serves both factorizations, which is what the chart system requires.

`B` has a right inverse (`B * B_R = 1`), so `rank B = ω`; that is what makes `G` exist, since by
`exists_factor_of_rowSpace_le` the inclusion gives `H_A = F * H = F * (X * B) = (F * X) * B`. -/
theorem exists_chart_factorization {m k ω : ℕ} (H HA : Matrix (Fin m) (Fin k) K)
    (hrank : H.rank = ω) (hle : Q1Subspace.rowSpace HA ≤ Q1Subspace.rowSpace H) :
    ∃ (X : Matrix (Fin m) (Fin ω) K) (B : Matrix (Fin ω) (Fin k) K)
      (G : Matrix (Fin m) (Fin ω) K) (XL : Matrix (Fin ω) (Fin m) K),
      X * B = H ∧ G * B = HA ∧ XL * X = 1 ∧ X.rank = ω := by
  obtain ⟨X, B, XL, BR, hXB, hXL, _hBR⟩ := exists_rank_factorization_of_rank H hrank
  obtain ⟨F, hF⟩ := exists_factor_of_rowSpace_le H HA hle
  refine ⟨X, B, F * X, XL, hXB, ?_, hXL, ?_⟩
  · rw [hF, ← hXB, Matrix.mul_assoc]
  · have h1 : H.rank ≤ X.rank := by
      rw [← hXB]
      exact Matrix.rank_mul_le_left _ _
    have h2 : X.rank ≤ ω := by
      simpa using Matrix.rank_le_width (A := X)
    omega

/-! ## Steps 4–5: the whole `eq:phi` point, from the two row-space conditions

`claim11_iff_gram` supplies step 4 (`(5b)` gives the Gram certificate `x`), so with steps 1–3 done
the five items of `eq:phi` can be produced in one go.  The statement below is the forward direction
of the equivalence, at the level of the compressed pair `(H, H_A)`; tying `H = L N`,
`H_A = L A N` to a feasible `L` is the remaining step. -/

/-- **Chart completeness, steps 4–5.**  If `rank H = ω ≥ 1`, `row(H_A) ≤ row(H)` and the pencil
`λH − H_A` has rank `ω` at every complex `λ`, then there are `X`, `B`, `G` and `x` with

  `rank X = ω`,  `X * B = H`,  `G * B = H_A`,  `Zᵀ Z x = e₀`,

where `Z` is the window matrix of the maximal minors of `λH − H_A`.  These are items (i), (iii),
(iv) and (v) of `eq:phi`; item (ii) is the rank-consistency system, carried by
`claim8_rank_consistency`. -/
theorem exists_phi_point {q k ω : ℕ} (H HA : Matrix (Fin q) (Fin k) ℝ)
    (hω : 1 ≤ ω) (hωr : H.rank = ω)
    (h5a : Q1Subspace.rowSpace HA ≤ Q1Subspace.rowSpace H)
    (h5b : ∀ z : ℂ, (z • H.map (algebraMap ℝ ℂ) - HA.map (algebraMap ℝ ℂ)).rank = ω) :
    ∃ (X : Matrix (Fin q) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
      (G : Matrix (Fin q) (Fin ω) ℝ) (x : Fin (2 * ω) → ℝ),
      X.rank = ω ∧ X * B = H ∧ G * B = HA ∧
      Matrix.mulVec
        (Matrix.transpose (windowMatrix (@minorFamily q k ω H HA) ω) *
          windowMatrix (@minorFamily q k ω H HA) ω) x =
        windowOne (K := ℝ) ω := by
  obtain ⟨F, hF⟩ := exists_factor_of_rowSpace_le H HA h5a
  obtain ⟨X, B, G, XL, hXB, hGB, hXL, hXrank⟩ := exists_chart_factorization H HA hωr h5a
  obtain ⟨x, hx⟩ := (claim11_iff_gram (q := q) (k := k) (ω := ω) H HA hω hωr ⟨F, hF⟩).mp h5b
  exact ⟨X, B, G, x, hXrank, hXB, hGB, hx⟩

/-! ## The backward direction, step 1

Given a chart point `H = X B`, `H_A = G B` with `X_L X = 1`, the row inclusion
`row(H_A) ≤ row(H)` — the hypothesis of step 1 in the forward direction — comes back for free.
This is what makes the chart system *sound*: every point satisfying items (iii)/(iv) of `eq:phi`
satisfies the compressed `(5a)`. -/

/-- **Backward step: the chart point satisfies the compressed `(5a)`.**  If `H = X * B`,
`H_A = G * B` and `X_L * X = 1`, then `row(H_A) ≤ row(H)`.  Indeed
`H_A = G B = G (X_L X) B = (G X_L) (X B) = (G X_L) H`, and a product's row space is contained in
that of its right factor. -/
theorem rowSpace_le_of_chart_factorization {m k ω : ℕ}
    (H HA : Matrix (Fin m) (Fin k) K) (X : Matrix (Fin m) (Fin ω) K)
    (B : Matrix (Fin ω) (Fin k) K) (G : Matrix (Fin m) (Fin ω) K)
    (XL : Matrix (Fin ω) (Fin m) K)
    (hH : X * B = H) (hHA : G * B = HA) (hXL : XL * X = 1) :
    Q1Subspace.rowSpace HA ≤ Q1Subspace.rowSpace H := by
  have h1 : (G * XL) * (X * B) = G * B := by
    rw [← Matrix.mul_assoc (G * XL) X B, Matrix.mul_assoc G XL X, hXL, Matrix.mul_one]
  have h : HA = (G * XL) * H := by
    calc HA = G * B := hHA.symm
      _ = (G * XL) * (X * B) := h1.symm
      _ = (G * XL) * H := by rw [hH]
  rw [h]
  exact rowSpace_mul_le _ _

/-! ## The backward direction, step 2: compressed conditions imply the original ones

Both bridges in `CompressionMatrix` are **biconditional**:
`rawAlgebraic_iff_rowSpace` and `rawSpectral_iff_compressed`.  So for any `L` whose compressed
data are `H = L N` and `H_A = L A N`, the two compressed conditions give the paper's `(5a)` and
`(5b)`.  This isolates the only remaining step of the backward direction: producing such an `L`
from a chart point. -/

/-- **Compressed conditions imply the original ones.**  With `N` spanning `ker[C; CA]`, the
compressed `(5a)` (a row-space inclusion) and the compressed `(5b)` (constant pencil rank) give
`rawAlgebraic` and `rawSpectral` for `L`, i.e. the paper's `(5a)` and `(5b)`. -/
theorem raw_of_compressed {p q n k : Type*} [Fintype p] [Fintype q] [Fintype n] [Fintype k]
    (C : Matrix p n K) (A : Matrix n n K)
    (L : Matrix q n K) (N : Matrix n k K)
    (hN : N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker)
    (h5a : Q1Subspace.rowSpace (L * A * N) ≤ Q1Subspace.rowSpace (L * N))
    (h5b : compressedSpectral (L * N) (L * A * N)) :
    rawAlgebraic C (C * A) L (L * A) ∧ rawSpectral C (C * A) L (L * A) :=
  ⟨(Q1Paper.PaperI.rawAlgebraic_iff_rowSpace C (C * A) L (L * A) N hN).mpr h5a,
    (Q1Paper.PaperI.rawSpectral_iff_compressed C (C * A) L (L * A) N hN).mpr h5b⟩

/-! ## The backward direction, step 3: producing `L` from a chart point

`L` is built row by row: the `i`-th row `u_i` must satisfy `u_i N = H_i` and `u_i (A N) = H_A,i`.
Such a `u_i` exists exactly when the pair `(H_i, H_A,i)` lies in the image of
`u ↦ (u N, u A N)`, which is the row space of the pair matrix `[N  A N]` — precisely the
defining property of the chart's `T`. -/

/-- **Chart completeness, backward step 3.**  If every pair `(H i, H_A i)` is of the form
`(u N, u (A N))`, then there is a single `L` with `L * N = H` and `L * (A * N) = H_A`. -/
theorem exists_L_of_pairs {q n k : ℕ}
    (N AN : Matrix (Fin n) (Fin k) K) (H HA : Matrix (Fin q) (Fin k) K)
    (h : ∀ i : Fin q, ∃ u : Fin n → K,
        Matrix.vecMul u N = H i ∧ Matrix.vecMul u AN = HA i) :
    ∃ L : Matrix (Fin q) (Fin n) K, L * N = H ∧ L * AN = HA := by
  choose u hu using h
  refine ⟨Matrix.of (fun i j => u i j), ?_, ?_⟩
  · ext i l
    rw [Matrix.mul_apply]
    exact congrFun (hu i).1 l
  · ext i l
    rw [Matrix.mul_apply]
    exact congrFun (hu i).2 l

/-- **Chart completeness, backward step 3 with the prescribed rows.**  The paper's observer is
`L = [L₀; R]`: its first `r₀` rows are fixed to `L₀`.  Building `L` as `fromRows L0 L'` makes that
structural rather than a side condition, and the two matrix equations split by block. -/
theorem exists_L_pinned {r0 q' n k : ℕ}
    (N AN : Matrix (Fin n) (Fin k) K) (L0 : Matrix (Fin r0) (Fin n) K)
    (H' HA' : Matrix (Fin q') (Fin k) K)
    (h : ∀ i : Fin q', ∃ u : Fin n → K,
        Matrix.vecMul u N = H' i ∧ Matrix.vecMul u AN = HA' i) :
    ∃ L' : Matrix (Fin q') (Fin n) K,
      Matrix.fromRows L0 L' * N = Matrix.fromRows (L0 * N) H' ∧
      Matrix.fromRows L0 L' * AN = Matrix.fromRows (L0 * AN) HA' := by
  obtain ⟨L', h1, h2⟩ := exists_L_of_pairs N AN H' HA' h
  exact ⟨L', by rw [Matrix.fromRows_mul, h1], by rw [Matrix.fromRows_mul, h2]⟩

/-! ## The bidirectional assembly: `PhiPoint`

`eq:phi` has five items.  Items (i), (iii), (iv), (v) are `rank X = ω`, `X B = H`, `G B = H_A`
and `Zᵀ Z x = e₀`; item (ii) is the rank-consistency system, which `claim8_rank_consistency`
identifies (per row of `H_A`, on `Hᵀ`) with the row inclusion `row(H_A) ≤ row(H)`.

Packaging them in a structure makes the two directions explicit: the forward direction produces a
`PhiPoint` from the two row-space conditions, the backward direction consumes one to get the
compressed `(5a)` back. -/

/-- A point of `eq:phi` at the compressed level. -/
structure PhiPoint {q k : ℕ} (H HA : Matrix (Fin q) (Fin k) ℝ) (ω : ℕ) where
  /-- item (iii): the left factor -/
  X : Matrix (Fin q) (Fin ω) ℝ
  /-- item (iii): the common right factor -/
  B : Matrix (Fin ω) (Fin k) ℝ
  /-- item (iv): the factor of `H_A` -/
  G : Matrix (Fin q) (Fin ω) ℝ
  /-- the left inverse of `X`, which is what makes the chart point sound -/
  XL : Matrix (Fin ω) (Fin q) ℝ
  /-- item (v): the Gram certificate -/
  x : Fin (2 * ω) → ℝ
  /-- item (i) -/
  rankX : X.rank = ω
  /-- item (iii) -/
  hH : X * B = H
  /-- item (iv) -/
  hHA : G * B = HA
  /-- the left inverse of `X` -/
  hXL : XL * X = 1
  /-- item (v) -/
  gram : (Matrix.transpose (windowMatrix (@minorFamily q k ω H HA) ω) *
      windowMatrix (@minorFamily q k ω H HA) ω).mulVec x = windowOne (K := ℝ) ω

/-- **Forward direction.**  The two row-space conditions produce a `PhiPoint`: items (i), (iii),
(iv) and (v) come from `exists_phi_point`, and item (ii) is the row inclusion itself. -/
theorem phiPoint_of_conditions {q k ω : ℕ} (H HA : Matrix (Fin q) (Fin k) ℝ)
    (hω : 1 ≤ ω) (hωr : H.rank = ω)
    (h5a : Q1Subspace.rowSpace HA ≤ Q1Subspace.rowSpace H)
    (h5b : ∀ z : ℂ, (z • H.map (algebraMap ℝ ℂ) - HA.map (algebraMap ℝ ℂ)).rank = ω) :
    Nonempty (PhiPoint H HA ω) := by
  obtain ⟨X, B, G, XL, hH, hHA, hXL, hXrank⟩ := exists_chart_factorization H HA hωr h5a
  obtain ⟨F, hF⟩ := exists_factor_of_rowSpace_le H HA h5a
  obtain ⟨x, hx⟩ :=
    (Q1Paper.PaperI.claim11_iff_gram (q := q) (k := k) (ω := ω) H HA hω hωr ⟨F, hF⟩).mp h5b
  exact ⟨{ X := X, B := B, G := G, XL := XL, x := x, rankX := hXrank, hH := hH, hHA := hHA,
           hXL := hXL, gram := hx }⟩

/-- **Backward direction.**  Any `PhiPoint` gives the compressed `(5a)` back. -/
theorem rowSpace_le_of_phiPoint {q k ω : ℕ} {H HA : Matrix (Fin q) (Fin k) ℝ}
    (P : PhiPoint H HA ω) : Q1Subspace.rowSpace HA ≤ Q1Subspace.rowSpace H :=
  rowSpace_le_of_chart_factorization H HA P.X P.B P.G P.XL P.hH P.hHA P.hXL

/-- A `PhiPoint` exhibits `H_A = F * H` — the factor `claim11_iff_gram` asks for. -/
theorem factor_of_phiPoint {q k ω : ℕ} {H HA : Matrix (Fin q) (Fin k) ℝ}
    (P : PhiPoint H HA ω) : ∃ F : Matrix (Fin q) (Fin q) ℝ, HA = F * H := by
  have h1 : (P.G * P.XL) * (P.X * P.B) = P.G * P.B := by
    rw [← Matrix.mul_assoc (P.G * P.XL) P.X P.B, Matrix.mul_assoc P.G P.XL P.X, P.hXL,
      Matrix.mul_one]
  refine ⟨P.G * P.XL, ?_⟩
  calc HA = P.G * P.B := P.hHA.symm
    _ = (P.G * P.XL) * (P.X * P.B) := h1.symm
    _ = (P.G * P.XL) * H := by rw [P.hH]

/-- **The backward direction's final step.**  If `ω = rank (L N)` and a `PhiPoint` is given for the
compressed data of `L`, then `L` satisfies the paper's `(5a)` and `(5b)`.

The one subtlety: `claim11_iff_gram` states (5b) over the **complex** numbers (the paper's
condition, cf. the complex-λ convention), while `compressedSpectral` quantifies over the base field.
The implication goes the easy way — specialise `z = ↑λ` and use that complexification preserves the
rank (`rank_map_ofReal`). -/
theorem feasible_of_phiPoint {p q n k ω : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin q) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (hN : N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker)
    (hω : 1 ≤ ω) (hHr : (L * N).rank = ω) (P : PhiPoint (L * N) (L * A * N) ω) :
    rawAlgebraic C (C * A) L (L * A) ∧ rawSpectral C (C * A) L (L * A) := by
  have h5a : Q1Subspace.rowSpace (L * A * N) ≤ Q1Subspace.rowSpace (L * N) :=
    rowSpace_le_of_phiPoint P
  have h5b : compressedSpectral (L * N) (L * A * N) := by
    intro lam
    have hg := (Q1Paper.PaperI.claim11_iff_gram (q := q) (k := k) (ω := ω)
      (L * N) (L * A * N) hω hHr (factor_of_phiPoint P)).mpr ⟨P.x, P.gram⟩
    have hspec := hg (algebraMap ℝ ℂ lam)
    have key : (lam • (L * N) - L * A * N).map (algebraMap ℝ ℂ) =
        algebraMap ℝ ℂ lam • (L * N).map (algebraMap ℝ ℂ) -
          (L * A * N).map (algebraMap ℝ ℂ) := by
      ext i j
      simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, map_sub, map_mul]
    rw [← key, rank_map_ofReal] at hspec
    rw [hspec, hHr]
  exact raw_of_compressed C A L N hN h5a h5b

end Q1Paper.ScratchChartComplete