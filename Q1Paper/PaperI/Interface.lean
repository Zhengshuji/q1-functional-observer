/-
Q1Paper/PaperI/Interface.lean

Formal statement layer of Paper I (Sections II-III).

The paper's objects are defined here exactly as they appear in the paper:

* `rawAlgebraic`  : condition (5a) on the row-stacked matrix `[LA; L; CA; C]`;
* `rawSpectral`   : condition (5b), the pencil condition for every `lambda`;
* `compressedAlgebraic`, `compressedSpectral` : the same conditions on the
  compressed blocks `H = L N` and `H_A = L A N`;
* `DEC`, `MINDEC` : the decision problems.

Only definitions are given.  The equivalence between the raw and the compressed
conditions (Claim 2 of the paper) is the target of the next file in this
directory, `CompressionMatrix.lean`; it is not proved yet, and this file
deliberately contains no theorem, so that nothing unproved enters the build.
-/

import Mathlib

namespace Q1Paper.PaperI

open Matrix

variable {K : Type*} [Field K]

/-- Condition (5a) of the paper, in its raw form:
`rank [LA; L; CA; C] = rank [L; CA; C]`. -/
def rawAlgebraic {p q n : Type*} [Fintype p] [Fintype q] [Fintype n]
    (C CA : Matrix p n K) (L LA : Matrix q n K) : Prop :=
  (Matrix.fromRows LA (Matrix.fromRows L (Matrix.fromRows CA C))).rank =
    (Matrix.fromRows L (Matrix.fromRows CA C)).rank

/-- Condition (5b) of the paper, in its raw form:
`rank [lambda L - LA; CA; C] = rank [L; CA; C]` for every `lambda`. -/
def rawSpectral {p q n : Type*} [Fintype p] [Fintype q] [Fintype n]
    (C CA : Matrix p n K) (L LA : Matrix q n K) : Prop :=
  ∀ lam : K,
    (Matrix.fromRows (lam • L - LA) (Matrix.fromRows CA C)).rank =
      (Matrix.fromRows L (Matrix.fromRows CA C)).rank

/-- The algebraic condition in compressed form: `rank [H_A; H] = rank H`. -/
def compressedAlgebraic {q k : Type*} [Fintype q] [Fintype k]
    (H HA : Matrix q k K) : Prop :=
  (Matrix.fromRows HA H).rank = H.rank

/-- The spectral condition in compressed form:
`rank (lambda H - H_A) = rank H` for every `lambda`. -/
def compressedSpectral {q k : Type*} [Fintype q] [Fintype k]
    (H HA : Matrix q k K) : Prop :=
  ∀ lam : K, (lam • H - HA).rank = H.rank

/-- The compressed blocks `H = L N` and `H_A = L A N` of a free-row block `L`. -/
def compressedH {q n k : Type*} [Fintype q] [Fintype n] [Fintype k]
    (L : Matrix q n K) (N : Matrix n k K) : Matrix q k K :=
  L * N

/-- `H_A = L A N`. -/
def compressedHA {q n k : Type*} [Fintype q] [Fintype n] [Fintype k]
    (L : Matrix q n K) (A : Matrix n n K) (N : Matrix n k K) : Matrix q k K :=
  L * A * N

/-- `DEC` with `r` free rows: there is `R` of size `r x n` such that
`L = [L0; R]` satisfies (5a) and (5b).  The prescribed order is `q = r0 + r`. -/
def DEC {p r0 n : ℕ}
    (C : Matrix (Fin p) (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (L0 : Matrix (Fin r0) (Fin n) K) (r : ℕ) : Prop :=
  ∃ R : Matrix (Fin r) (Fin n) K,
    let L := Matrix.fromRows L0 R
    rawAlgebraic C (C * A) L (L * A) ∧ rawSpectral C (C * A) L (L * A)

/-- `MINDEC(Q)`: some order `q = r0 + r <= Q` is feasible. -/
def MINDEC {p r0 n : ℕ}
    (C : Matrix (Fin p) (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (L0 : Matrix (Fin r0) (Fin n) K) (Q : ℕ) : Prop :=
  ∃ r : ℕ, r0 + r ≤ Q ∧ DEC C A L0 r

end Q1Paper.PaperI
