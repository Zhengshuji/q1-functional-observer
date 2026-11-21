/-
Q1Paper/MinOrder.lean

Paper II, Proposition 1: the dimension count behind the minimum-order bound
`t_min ≤ 2 ℓ`.

Paper II sets

  `t_min = min { dim (W / W₀) : W feasible }`

and proves `q_min = r₀ + t_min` and `t_min ≤ 2 ℓ`.  The predicate `feasible` is the
paper's `DEC`, and this library has **no** `DEC` predicate (the same limitation is
recorded in `Q1Paper/MonotoneBlocks.lean`, "What is not here").  Hence neither
`t_min` (a minimum over the feasible set) nor `q_min` can be stated here, and the
identification `q_min = r₀ + t_min` is out of reach.  What *is* formalisable, and
what carries the search bound used everywhere downstream, is the dimension count
for an individual `W`:

  if `W₀ ≤ W`, `π₂ W ≤ π₁ W` and `dim (π₁ W) ≤ ℓ`, then `dim (W / W₀) ≤ 2 ℓ`.

The proof is three inequalities:

  `dim (W / W₀) = dim W - dim W₀ ≤ dim W ≤ dim (π₁ W) + dim (π₂ W) ≤ 2 dim (π₁ W) ≤ 2 ℓ`,

where the middle inequality is `finrank_le_pi1_add_pi2` from
`Q1Paper/Q1Projection.lean` and the next one uses `π₂ W ≤ π₁ W`.

Contents.
* `submoduleOfLe` — `W₀` regarded as a submodule of `W`; the paper's `W / W₀` is
  the quotient by this submodule.
* `t` — the paper's `t = dim (W / W₀)` (for `W₀ ≤ W`; see `t_eq_finrank_sub`).
* `finrank_quotient_eq_finrank_sub` — `dim (W / W₀) = dim W - dim W₀`.
* `t_eq_finrank_sub` — the same for `t`, the form asked for in the to-do list.
* `finrank_le_two_mul_of_pi2_le_pi1` — `dim W ≤ 2 ω` (the structural bound, with
  `π₂ W ≤ π₁ W` rather than `π₁ W = π₂ W`).
* `finrank_le_two_mul_ell` — `dim W ≤ 2 ℓ`, with no reference to `W₀` at all.
* `t_le_two_mul` — **the paper's `t ≤ 2 ℓ`**, pointwise in `W`.
* `exists_mem_t_le_two_mul` — `t_min ≤ 2 ℓ` with the feasible set abstracted as an
  arbitrary nonempty set.
* `finrank_quotient_le_two_mul` — the same statement in quotient form.

Because `t ≤ 2 ℓ` holds for *every* `W` satisfying the three hypotheses, it holds
in particular on the feasible set, and any minimum of `t` over a nonempty feasible
set is `≤ 2 ℓ`.  Stating that minimum requires the missing `DEC` predicate, so it is
not stated; the pointwise bound is the whole formalisable content.

The bound needs no hypothesis on `W₀` beyond `W₀ ≤ W` (and even that is needed only
to identify `t` with `dim W - dim W₀`): `finrank W₀` is a natural number, so
`finrank W₀ ≥ 0` is automatic.  The hypothesis `π₂ W ≤ π₁ W` cannot be dropped:
without it `dim W` may be as large as `2 ℓ` while `π₁ W` is small only because the
second projection is large.
-/

import Q1Paper.Q1Projection

namespace Q1Subspace

open Module

variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-! ### 1. `W₀` inside `W`, and the paper's `t` -/

/-- `W₀` regarded as a submodule of `W`.  For `W₀ ≤ W` this is the kernel of the
quotient map `W → W / W₀`, i.e. the submodule by which the paper's quotient
`W / W₀` is taken. -/
def submoduleOfLe {W₀ W : Submodule K (F × F)} (_h : W₀ ≤ W) : Submodule K ↥W :=
  W₀.comap W.subtype

/-- The paper's `t = dim (W / W₀)`, read as the dimension of the quotient of `W` by
`W₀`.  (For `W₀ ≰ W` the definition still makes sense: it quotients by `W₀ ∩ W`.
On the paper's feasible set one has `W₀ ≤ W`, and then `t_eq_finrank_sub` identifies
this with `dim W - dim W₀`.) -/
noncomputable def t (W₀ W : Submodule K (F × F)) : ℕ :=
  finrank K (↥W ⧸ W₀.comap W.subtype)

/-! ### 2. The quotient-dimension identity -/

/-- **Quotient-dimension identity.**  For `W₀ ≤ W`,
`dim (W / W₀) = dim W - dim W₀`.  This is Mathlib's
`Submodule.finrank_quotient` applied to `W₀` viewed inside `W`, together with
`dim (W₀ ∩ W) = dim W₀` for `W₀ ≤ W`
(`Submodule.comapSubtypeEquivOfLe`). -/
theorem finrank_quotient_eq_finrank_sub [FiniteDimensional K F]
    {W₀ W : Submodule K (F × F)} (h : W₀ ≤ W) :
    finrank K (↥W ⧸ submoduleOfLe h) = finrank K ↥W - finrank K ↥W₀ := by
  have hdim : finrank K ↥(submoduleOfLe h) = finrank K ↥W₀ :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe h)
  rw [Submodule.finrank_quotient (N := submoduleOfLe h), hdim]

/-- **The paper's `t` is `dim W - dim W₀`.**  This is the `t = dim (W / W₀)` half of
the to-do list, stated for the definition `t` above. -/
theorem t_eq_finrank_sub [FiniteDimensional K F] {W₀ W : Submodule K (F × F)}
    (h : W₀ ≤ W) : t W₀ W = finrank K ↥W - finrank K ↥W₀ :=
  finrank_quotient_eq_finrank_sub h

/-! ### 3. The structural upper bound `dim W ≤ 2 ω` -/

/-- **Structural upper bound, `π₂ W ≤ π₁ W` form.**  If the second projection of `W`
is contained in the first (the paper's algebraic condition), then
`dim W ≤ 2 dim (π₁ W)`.  This sharpens
`Q1Subspace.finrank_le_two_mul_of_pi1_eq_pi2` from equality of the projections to
containment, which is the hypothesis the paper actually uses before the spectral
condition at zero upgrades it to equality. -/
theorem finrank_le_two_mul_of_pi2_le_pi1 [FiniteDimensional K F]
    {W : Submodule K (F × F)} (h : pi2 W ≤ pi1 W) :
    finrank K ↥W ≤ 2 * finrank K ↥(pi1 W) := by
  have hb := finrank_le_pi1_add_pi2 W
  have hm : finrank K ↥(pi2 W) ≤ finrank K ↥(pi1 W) := Submodule.finrank_mono h
  omega

/-- **Structural upper bound, equal-projection form**, as a consequence of the
containment form. -/
theorem finrank_le_two_mul_of_pi1_eq_pi2' [FiniteDimensional K F]
    {W : Submodule K (F × F)} (h : pi1 W = pi2 W) :
    finrank K ↥W ≤ 2 * finrank K ↥(pi1 W) :=
  finrank_le_two_mul_of_pi2_le_pi1 (le_of_eq h.symm)

/-! ### 4. `ell` alone bounds `dim W` -/

/-- **`dim W ≤ 2 ℓ`**, with no reference to `W₀`: if `π₂ W ≤ π₁ W` and
`dim (π₁ W) ≤ ℓ`, then `W` itself has dimension at most `2 ℓ`.  This is the
`W₀`-free form of the bound. -/
theorem finrank_le_two_mul_ell [FiniteDimensional K F]
    {W : Submodule K (F × F)} (h : pi2 W ≤ pi1 W) {ell : ℕ}
    (hell : finrank K ↥(pi1 W) ≤ ell) :
    finrank K ↥W ≤ 2 * ell := by
  have hW := finrank_le_two_mul_of_pi2_le_pi1 h
  omega

/-! ### 5. The paper's bound `t ≤ 2 ℓ` -/

/-- **The paper's dimension bound `t ≤ 2 ℓ`.**  For every `W ≤ F × F` with
`π₂ W ≤ π₁ W` and `dim (π₁ W) ≤ ℓ`, the quotient dimension `t = dim (W / W₀)` is at
most `2 ℓ`.

No hypothesis on `W₀` is needed for the inequality: the quotient of `W` by a
submodule has dimension at most `dim W` regardless of `W₀`.  The hypothesis
`W₀ ≤ W` is needed only to read `t` as `dim W - dim W₀`
(`t_eq_finrank_sub`).  Since the bound is pointwise in `W`, it holds on any feasible
set, so any minimum of `t` over a nonempty feasible set is `≤ 2 ℓ`; formalising that
minimum itself needs the paper's `DEC` predicate, which is not in this library. -/
theorem t_le_two_mul [FiniteDimensional K F] (W₀ W : Submodule K (F × F))
    (h : pi2 W ≤ pi1 W) {ell : ℕ} (hell : finrank K ↥(pi1 W) ≤ ell) :
    t W₀ W ≤ 2 * ell := by
  have hq : t W₀ W ≤ finrank K ↥W :=
    Submodule.finrank_quotient_le (W₀.comap W.subtype)
  have hW : finrank K ↥W ≤ 2 * ell := finrank_le_two_mul_ell h hell
  omega

/-- **`t_min ≤ 2 ℓ` with the feasible set abstracted as a set.**  If `S` is any
nonempty family of subspaces all satisfying the paper's dimension hypotheses, then
some member of `S` has `t ≤ 2 ℓ` — i.e. the minimum of `t` over `S` is at most
`2 ℓ`.  This is the paper's `t_min ≤ 2 ℓ` with the paper's feasible set represented
by an arbitrary nonempty set `S`; a concrete feasibility notion (`DEC`) is not
available in this library, and none is invented here. -/
theorem exists_mem_t_le_two_mul [FiniteDimensional K F]
    (W₀ : Submodule K (F × F)) {ell : ℕ} {S : Set (Submodule K (F × F))}
    (hne : S.Nonempty) (hpi : ∀ W ∈ S, pi2 W ≤ pi1 W)
    (hell : ∀ W ∈ S, finrank K ↥(pi1 W) ≤ ell) :
    ∃ W ∈ S, t W₀ W ≤ 2 * ell := by
  obtain ⟨W, hW⟩ := hne
  exact ⟨W, hW, t_le_two_mul W₀ W (hpi W hW) (hell W hW)⟩

/-- **`t ≤ 2 ℓ` in quotient form**: the same bound with `W / W₀` written as the
explicit quotient `↥W ⧸ submoduleOfLe h`, under the paper's hypothesis `W₀ ≤ W`. -/
theorem finrank_quotient_le_two_mul [FiniteDimensional K F]
    {W₀ W : Submodule K (F × F)} (h : W₀ ≤ W) (hpi : pi2 W ≤ pi1 W)
    {ell : ℕ} (hell : finrank K ↥(pi1 W) ≤ ell) :
    finrank K (↥W ⧸ submoduleOfLe h) ≤ 2 * ell :=
  t_le_two_mul W₀ W hpi hell

/-- **`t ≤ 2 ℓ` under `π₁ W = π₂ W`**, the version matching the output of
`Q1Subspace.pi1_eq_pi2_of_le_of_finrank_eq` (paper's Step 3). -/
theorem t_le_two_mul_of_pi1_eq_pi2 [FiniteDimensional K F] (W₀ W : Submodule K (F × F))
    (h : pi1 W = pi2 W) {ell : ℕ} (hell : finrank K ↥(pi1 W) ≤ ell) :
    t W₀ W ≤ 2 * ell :=
  t_le_two_mul W₀ W (le_of_eq h.symm) hell

end Q1Subspace
