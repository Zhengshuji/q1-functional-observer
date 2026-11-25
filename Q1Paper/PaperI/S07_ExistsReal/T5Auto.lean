
import Q1Paper.PaperI.S07_ExistsReal.T5DecC
import Q1Paper.PaperI.S01_Compression.KernelBasis

/-!
Q1Paper/PaperI/S07_ExistsReal/T5Auto.lean

**Theorem 5 of Paper I with no abstract hypothesis.**

`PaperI/T5DecC.lean` proves

* `DECℂ_iff_exists_compressed`, and
* `DECℂ_iff_exists_encodes`,

but both take as hypotheses an *already chosen* basis matrix `N` of `ker [CA; C]`:

  `(hN : N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker)`  and
  `(hNk : N.rank = k)`.

`PaperI/KernelBasis.lean` shows such an `N` exists for `k = finrank ℝ (ker [CA; C])`
(`exists_kernel_basis_matrix_of_finrank`), and `exists_kernel_basis_matrix` produces
`k` and `N` together.

This file composes the two: the kernel basis becomes an existential `∃ k N` in the
statement, so the last abstract hypothesis of Theorem 5 disappears.

Main results:

* `DECℂ_iff_exists_compressed_auto`  — compressed form, `∃ k N` in the statement;
* `DECℂ_iff_exists_encodes_auto`     — polynomial-system (`encodes`) form, `∃ k N`.

Complete: every declaration below compiles; nothing is postulated.
-/


namespace Q1Paper

namespace Thm5

/-- **`DECℂ` in compressed form, without the abstract kernel-basis hypothesis.**

The paper's decision problem (real design, complex ranks, `λ : ℂ`) holds exactly
when *some* `k` and *some* full-column-rank matrix `N` whose range is `ker [CA; C]`
allow a real `R` making the compressed pair `([L₀;R] N, [L₀;R] A N)` satisfy (5a)
over `ℝ` and (5b) at every complex parameter.  Compared with
`DECℂ_iff_exists_compressed`, the hypotheses `hN`, `hNk` have become part of an
existential, supplied by `exists_kernel_basis_matrix_of_finrank`. -/
theorem DECℂ_iff_exists_compressed_auto
    {p r0 r n : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) :
    PaperI.DECℂ C A L0 r ↔
      ∃ (k : ℕ) (N : Matrix (Fin n) (Fin k) ℝ),
        N.rank = k ∧
        N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker ∧
        ∃ R : Matrix (Fin r) (Fin n) ℝ,
          PaperI.compressedAlgebraic (Matrix.fromRows L0 R * N) (Matrix.fromRows L0 R * A * N) ∧
          PaperI.compressedSpectral
            ((Matrix.fromRows L0 R * N).map (algebraMap ℝ ℂ))
            ((Matrix.fromRows L0 R * A * N).map (algebraMap ℝ ℂ)) := by
  classical
  constructor
  · -- Forward: build the kernel basis at `k = finrank ℝ (ker [CA; C])`.
    intro hDEC
    obtain ⟨N, hNk, hN⟩ :=
      exists_kernel_basis_matrix_of_finrank (p := p) (n := n)
        (k := Module.finrank ℝ ((Matrix.fromRows (C * A) C).mulVecLin.ker)) C A rfl
    obtain ⟨R, hAlg, hSpec⟩ :=
      (DECℂ_iff_exists_compressed C A L0 N hN hNk).mp hDEC
    exact ⟨_, N, hNk, hN, R, hAlg, hSpec⟩
  · -- Reverse: apply the existing equivalence at the given `N`.
    rintro ⟨k, N, hNk, hN, R, hAlg, hSpec⟩
    exact (DECℂ_iff_exists_compressed C A L0 N hN hNk).mpr ⟨R, hAlg, hSpec⟩

/-- **Theorem 5 of Paper I, complex form, without the abstract kernel-basis
hypothesis.**

`DECℂ` holds exactly when the paper's polynomial system `Φ_ω` has a real solution
for some `ω`, with *some* `k` and *some* full-column-rank matrix `N` whose range is
`ker [CA; C]`.  Obtained by composing `DECℂ_iff_exists_compressed_auto` with
`exists_encodes_iff` (through `DECℂ_iff_exists_encodes`). -/
theorem DECℂ_iff_exists_encodes_auto
    {p r0 r n : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (L0 : Matrix (Fin r0) (Fin n) ℝ) :
    PaperI.DECℂ C A L0 r ↔
      ∃ (k : ℕ) (N : Matrix (Fin n) (Fin k) ℝ), N.rank = k ∧
        N.mulVecLin.range = (Matrix.fromRows (C * A) C).mulVecLin.ker ∧
        ∃ (ω : ℕ) (X G : Matrix (Fin r0 ⊕ Fin r) (Fin ω) ℝ) (B : Matrix (Fin ω) (Fin k) ℝ)
          (XL : Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ) (BR : Matrix (Fin k) (Fin ω) ℝ)
          (S : Fin (2 * ω - 2 + 1) → Matrix (Fin ω) (Fin r0 ⊕ Fin r) ℝ),
          encodes C A L0 N X G B XL BR S := by
  classical
  constructor
  · -- Forward: build the kernel basis at `k = finrank ℝ (ker [CA; C])`.
    intro hDEC
    obtain ⟨N, hNk, hN⟩ :=
      exists_kernel_basis_matrix_of_finrank (p := p) (n := n)
        (k := Module.finrank ℝ ((Matrix.fromRows (C * A) C).mulVecLin.ker)) C A rfl
    obtain ⟨ω, X, G, B, XL, BR, S, hSys⟩ :=
      (DECℂ_iff_exists_encodes C A L0 N hN hNk).mp hDEC
    exact ⟨_, N, hNk, hN, ω, X, G, B, XL, BR, S, hSys⟩
  · -- Reverse: apply the existing equivalence at the given `N`.
    rintro ⟨k, N, hNk, hN, ω, X, G, B, XL, BR, S, hSys⟩
    exact (DECℂ_iff_exists_encodes C A L0 N hN hNk).mpr ⟨ω, X, G, B, XL, BR, S, hSys⟩

end Thm5

end Q1Paper

