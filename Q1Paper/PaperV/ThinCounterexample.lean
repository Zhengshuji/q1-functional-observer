import Mathlib

/-!
Q1Paper/PaperV/ThinCounterexample.lean

**Scope.**  This is a Lean certificate for two small but decisive points of the retraction
`805` of `803` in the feasibility geometry of Paper V.  It is *not* a formalisation of the whole
`THIN-FEAS` statement, of Theorem 4, or of the paper's §VI examples: the file proves only the
set-theoretic `B`-criterion core (Task A) and one explicit linear-algebra counterexample
(Task B).  Nothing in `Audit.lean`, `Claims.lean`, `MainTheorems.lean`, `paper/` or `docs/` is
touched or imported beyond `Mathlib`.

## Task A: why `C ∩ B = S` cannot replace `C ⊆ B`

`803` proposed the pointwise criterion `C ⊆ B ↔ C ∩ B = S`.  If `C` is a **proper** subset of
`S`, then `C ∩ B ⊆ C ⊂ S`, so the right-hand side is *unsatisfiable*:
`inter_ne_of_ssubset` proves `C ∩ B ≠ S` for every `B`.  Hence the biconditional degenerates
to `¬ C ⊆ B`: it holds exactly for those `B` with `C ⊄ B`, the opposite of what a criterion for
`C ⊆ B` needs.  The literal pointwise statement
`∀ B, ¬ (C ⊆ B ↔ C ∩ B = S)` is itself **false** (take `B = ∅` when `C ⊄ B`), so the correct
"not equivalent" formulation is the uniform one, `not_forall_iff_of_ssubset`, proved below.
The file also machine-checks a concrete counterexample, `literal_pointwise_form_false`.

The exact statement requested in the task,
`C ⊂ S → ¬ (C ⊆ B ↔ C ∩ B = S)`, therefore needs the side condition `C ⊆ B` under which the
`803` criterion is meant to be applied; that corrected pointwise form is
`not_iff_of_subset_of_ssubset`.

## Task B: the `Z'' = e₀ e₂ᵀ` thin-stratum example

Work in `V = Fin 4 → ℂ`, with standard basis vectors `e₀, e₁, e₂, e₃` (`stdE 0`, ...,
`stdE 3`).  For `s t u : ℂ` put

* `v(s,t,u) = s • e₀ + (1 + t) • e₁ + e₂ + u • e₃`,
* `U(s,t,u) = span {e₀, v(s,t,u)}`,
* `T = span {e₀, e₁}`.

The paper's row-space compatibility condition is `U Z'' ⊆ U + T` with `Z'' = e₀ e₂ᵀ`.  Because
`e₀ ∈ U`, acting on row vectors gives `U Z'' = span {e₂}`; in the column-vector model used here
this is exactly `e₂ ∈ U(s,t,u) + T`.  (`sup_thinU_thinT_eq_span` records
`U(s,t,u) ⊔ T = span {e₀, e₁, v(s,t,u)}`.)  The theorem `thinE2_mem_sup_iff` proves

  `e₂ ∈ U(s,t,u) ⊔ T ↔ u = 0`.

Thus `C_a = {u = 0}` is a proper closed subset of the parameter space, and every general point
`u ≠ 0` is incompatible.  This is the Lean certificate of the paper-side computation, not a
formalisation of the surrounding §VI(A) discussion.

No `sorry`, no custom axiom.  The two principal results are checked at the end with
`#print axioms`; only Lean's standard axioms are allowed.
-/

set_option maxHeartbeats 800000

namespace Q1Paper.PaperV

/-! ### Task A: the set-theoretic core -/

variable {X : Type*} {S C B : Set X}

/-- **The irreducible set-theoretic fact.**  If `C` is a proper subset of `S`, then `C ∩ B`
is never `S`, for any `B`.  Indeed `C ∩ B ⊆ C ⊂ S`. -/
theorem inter_ne_of_ssubset (h : C ⊂ S) (B : Set X) : C ∩ B ≠ S := by
  intro hEq
  have hSC : S ⊆ C := by
    rw [← hEq]
    exact Set.inter_subset_left
  exact h.2 hSC

/-- **The requested pointwise form, with its missing side condition.**  If `C ⊂ S` and
`C ⊆ B`, then `C ⊆ B ↔ C ∩ B = S` fails: its left side is true while its right side is
unsatisfiable.  This is the literal `805` retraction statement for the `B`'s on which `803`'s
criterion was meant to apply (`B = S` is one such `B`). -/
theorem not_iff_of_subset_of_ssubset (h : C ⊂ S) (hCB : C ⊆ B) :
    ¬ (C ⊆ B ↔ C ∩ B = S) := by
  intro hiff
  exact inter_ne_of_ssubset h B (hiff.mp hCB)

/-- **Corrected "not equivalent" statement.**  For `C ⊂ S` there is no `B`-independent
equivalence `C ⊆ B ↔ C ∩ B = S`: the identity fails at `B = S`, where `C ⊆ S` holds but
`C ∩ S = C ≠ S`.  This is the formal content of "`C ∩ B = S` cannot be equivalent to `C ⊆ B`". -/
theorem not_forall_iff_of_ssubset (h : C ⊂ S) :
    ¬ ∀ B : Set X, (C ⊆ B ↔ C ∩ B = S) := by
  intro hiff
  have h1 : C ∩ S = S := (hiff S).mp h.1
  have hSC : S ⊆ C := by
    rw [← h1]
    exact Set.inter_subset_left
  exact h.2 hSC

/-- **The literal pointwise negation is false.**  Specialised to `X = Bool`, the statement
`∀ S C B, C ⊂ S → ¬ (C ⊆ B ↔ C ∩ B = S)` fails for `S = univ`, `C = {true}`, `B = ∅`: here
`C ⊂ S`, yet `C ⊆ B` and `C ∩ B = S` are both false, so the biconditional is true.  This is why
Task A is stated as `not_forall_iff_of_ssubset`, not as a pointwise negation for every `B`. -/
theorem literal_pointwise_form_false :
    ¬ (∀ (S C B : Set Bool), C ⊂ S → ¬ (C ⊆ B ↔ C ∩ B = S)) := by
  intro h
  have hproper : ({true} : Set Bool) ⊂ Set.univ := by
    refine ⟨?_, ?_⟩
    · intro x _
      exact Set.mem_univ x
    · intro hsub
      have hf : false ∈ ({true} : Set Bool) := hsub (Set.mem_univ false)
      simp at hf
  have hiff : (({true} : Set Bool) ⊆ (∅ : Set Bool) ↔
      ({true} : Set Bool) ∩ ∅ = Set.univ) := by
    constructor
    · intro hsub
      have ht : true ∈ (∅ : Set Bool) := hsub (by simp)
      simp at ht
    · intro heq
      have ht : true ∈ ({true} : Set Bool) ∩ (∅ : Set Bool) := by
        rw [heq]
        exact Set.mem_univ true
      simp at ht
  exact (h Set.univ {true} ∅ hproper) hiff

/-! ### Task B: the explicit `Z'' = e₀ e₂ᵀ` counterexample -/

/-- The standard basis vector `eᵢ` of `V = Fin 4 → ℂ`. -/
noncomputable def stdE (i : Fin 4) : Fin 4 → ℂ := Pi.single i 1

/-- `v(s,t,u) = s • e₀ + (1 + t) • e₁ + e₂ + u • e₃`. -/
noncomputable def stdV (s t u : ℂ) : Fin 4 → ℂ :=
  s • stdE 0 + (1 + t) • stdE 1 + stdE 2 + u • stdE 3

/-- `U(s,t,u) = span {e₀, v(s,t,u)}`. -/
noncomputable def thinU (s t u : ℂ) : Submodule ℂ (Fin 4 → ℂ) :=
  Submodule.span ℂ {stdE 0, stdV s t u}

/-- `T = span {e₀, e₁}`. -/
noncomputable def thinT : Submodule ℂ (Fin 4 → ℂ) :=
  Submodule.span ℂ {stdE 0, stdE 1}

/-- The sum `U(s,t,u) + T` is the span of `{e₀, e₁, v(s,t,u)}`; this is the subspace appearing
in the compatibility condition `U Z'' ⊆ U + T` (with `Z'' = e₀ e₂ᵀ`, so `U Z'' = span {e₂}`). -/
theorem sup_thinU_thinT_eq_span (s t u : ℂ) :
    thinU s t u ⊔ thinT =
      Submodule.span ℂ ({stdE 0, stdE 1, stdV s t u} : Set (Fin 4 → ℂ)) := by
  have hset : ({stdE 0, stdV s t u} ∪ {stdE 0, stdE 1} : Set (Fin 4 → ℂ)) =
      {stdE 0, stdE 1, stdV s t u} := by
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [thinU, thinT, ← Submodule.span_union, hset]

/-- **Task B.**  For the family `v(s,t,u) = s • e₀ + (1+t) • e₁ + e₂ + u • e₃`,
`e₂ ∈ U(s,t,u) ⊔ T` holds exactly when `u = 0`.  The forward direction reads the coefficients
of `e₂` and `e₃`: from `e₂ = α • e₀ + β • e₁ + γ • v` one gets `γ = 1` (coefficient of `e₂`)
and `γ u = 0` (coefficient of `e₃`).  Conversely `u = 0` gives
`e₂ = (-s) • e₀ + (-(1+t)) • e₁ + 1 • v(s,t,0)`. -/
theorem thinE2_mem_sup_iff (s t u : ℂ) :
    stdE 2 ∈ thinU s t u ⊔ thinT ↔ u = 0 := by
  rw [sup_thinU_thinT_eq_span, Submodule.mem_span_triple]
  constructor
  · rintro ⟨a, b, c, h⟩
    have h2 : c = 1 := by
      have := congrFun h 2
      simpa [stdE, stdV] using this
    have h3 : c * u = 0 := by
      have := congrFun h 3
      simpa [stdE, stdV] using this
    rw [h2] at h3
    simpa using h3
  · intro hu
    refine ⟨-s, -(1 + t), 1, ?_⟩
    funext i
    fin_cases i <;> simp [stdE, stdV, hu]

end Q1Paper.PaperV

#print axioms Q1Paper.PaperV.not_forall_iff_of_ssubset
#print axioms Q1Paper.PaperV.thinE2_mem_sup_iff
