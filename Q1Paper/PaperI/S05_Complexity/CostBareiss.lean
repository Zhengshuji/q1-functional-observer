
import Q1Paper.PaperI.S05_Complexity.CostCore
import Q1Paper.PaperI.S05_Complexity.BareissBase

/-!
Q1Paper/PaperI/S05_Complexity/CostBareiss.lean

**Binding the cost model (`Q1Complexity`, `PaperI/CostCore.lean`) to the Bareiss
algorithm (`PaperI/BareissBase.lean`): a real instance of a complexity theorem.**

The computation.  For a `2 × 2` rational matrix `A` the first (and only) Bareiss
step produces the entry

  `(A 0 0 * A 1 1 - A 1 0 * A 0 1) / 1`,

which is `bStepNum A 0 1 1` (`BareissBase.lean`) and equals `A.det`
(`bareiss_two_two` is the integer version; `Matrix.det_fin_two` is the expansion).
This file *compiles that computation into a `Prog`* of the cost model and proves
the four statements a complexity claim needs, all from the `run` semantics
(nothing is assumed):

1. `bstep2Prog_value`           : `(run (bstep2Prog A) s).2.1 = A 0 0 * A 1 1 - A 0 1 * A 1 0`;
   `bstep2Prog_value_eq_det`    : that value is `A.det`;
   `bstep2Prog_value_eq_bStepNum`: and it is `bStepNum A 0 1 1`, the paper's
   fraction-free numerator.
2. `bstep2Prog_alg`             : `(run (bstep2Prog A) s).2.2.alg = 3`
   (two multiplications, one subtraction; `pure` costs nothing).
3. `bstep2Prog_bit_le`          : the derived bit cost is at most
   `ratBitCost .mul (A 0 0) (A 1 1) + ratBitCost .mul (A 0 1) (A 1 0)
      + ratBitCost .sub (A 0 0 * A 1 1) (A 0 1 * A 1 0)`,
   the *composed bound*: each summand is the cost of one primitive as derived
   from the values it actually touches.
4. `batchProg_bit_le_sum`       : the same three operations, run once per `2 × 2`
   matrix in an `n`-tuple (`Prog.forFin` over `Fin n`), satisfy
   `(run (batchProg Avec) s).2.2.bit ≤ ∑ k : Fin n, batchBound Avec k`
   (`run_forFin_bit_eq_sum`), and
   `batchProg_bit_le_uniform` turns that into the uniform polynomial bound
   `n * (2*β + 2 * fieldOpBitCost .mul β β + fieldOpBitCost .sub (2*β) (2*β))`
   when every input entry has at most `β` bits (`run_bit_le_sum`, with
   `fieldOpBitCost_mono` and `batchBound_le` as the ingredients).
   Companion statements: `batchProg_alg` (`n * 5` operations), and
   `loadBody_out` (each iteration writes the determinant of *its own* matrix
   into the result register).

Fidelity of the encoding.  The register machine has one state operand per
primitive, so the computed products are read back from the register file:
`coreOps_state_rM1`, `coreOps_state_rM2`, `coreOps_state_rOut` show that the
first product is what the subtraction consumes, and `bstep2Prog_reg_out` shows
that the returned value is exactly the register content (with `s rA00 = A 0 0`),
so the output is not an unperformed folded constant.

Modelling note (why the loop body starts with two `write`s).  Since a primitive
has exactly one state operand (`Primitive.fieldOpMix` computes
`dst ← (state lhs) op q`), a loop iteration that must work from *its own*
operands has to place them in the register file first; the two `write`
primitives do that, and they are what makes the per-iteration cost independent of
the state the iteration starts in.  The three domain operations that follow are
literally the body of `bstep2Prog` (`coreOps`), so the loop runs *the same*
Bareiss step `n` times.

No `sorry`, no `admit`, no new axioms.  Check with
  `lake env lean Q1Paper/PaperI/CostBareiss.lean`
-/


open Q1Paper.PaperI

namespace Q1Complexity
namespace BareissCost

/-! ## 1.  The register file -/

/-- Registers are natural numbers: a state is a register file `ℕ → ℚ`. -/
abbrev Reg : Type := ℕ

/-- Register holding the operand `A 0 0`. -/
@[simp] def rA00 : Reg := 0

/-- Register holding the operand `A 0 1`. -/
@[simp] def rA01 : Reg := 1

/-- Register receiving the first product `A 0 0 * A 1 1`. -/
@[simp] def rM1 : Reg := 2

/-- Register receiving the second product `A 0 1 * A 1 0`. -/
@[simp] def rM2 : Reg := 3

/-- Register receiving the Bareiss numerator. -/
@[simp] def rOut : Reg := 4

/-- Addition of `Cost` values written out on the components; a `rfl` lemma that
lets `simp` normalise composed costs. -/
theorem cost_add_mk (a b c d : ℕ) : (⟨a, b⟩ : Cost) + ⟨c, d⟩ = ⟨a + c, b + d⟩ := rfl

/-- The run of a program followed by a (free) `pure` that returns a constant:
the cost is exactly the cost of the program. -/
theorem run_bind_pure {σ : Type} [DecidableEq σ] {α β : Type} [Fintype α]
    (f : Prog σ α) (a : β) (s : St σ) :
    run (.bind f (fun _ => .pure a)) s = ((run f s).1, a, (run f s).2.2) := by
  rw [run_bind]
  simp [run_pure, Cost.add_zero]

/-! ## 2.  The three domain operations of the first Bareiss step -/

/-- **The body of the first Bareiss step, as three domain operations.**

`coreOps A` performs, in this order,
* `rM1 ← (state rA00) * (A 1 1)`         (`A 0 0 * A 1 1`),
* `rM2 ← (state rA01) * (A 1 0)`         (`A 0 1 * A 1 0`),
* `rOut ← (state rM1) - (A 0 1 * A 1 0)` (`A 0 0 * A 1 1 - A 0 1 * A 1 0`).

No cost is supplied: every cost is derived by `run` from the values the
primitives touch.  Note the third operation reads the *register* `rM1`, i.e. the
product actually computed by the first operation, and not a folded constant. -/
def coreOps (A : Matrix (Fin 2) (Fin 2) ℚ) : Prog Reg Unit :=
  .bind (.primitive (.fieldOpMix FieldOp.mul rA00 (A 1 1) rM1)) (fun _ =>
    .bind (.primitive (.fieldOpMix FieldOp.mul rA01 (A 1 0) rM2)) (fun _ =>
      .primitive (.fieldOpMix FieldOp.sub rM1 (A 0 1 * A 1 0) rOut)))

/-- **The compiled first Bareiss step for a `2 × 2` rational matrix**, with a
`ℚ`-valued output: the three domain operations above, followed by a (free)
`pure` that returns the paper's expression.  `bstep2Prog_reg_out` below proves
that the value returned is *also* the content of the register `rOut` computed by
the three operations, so the output is not an unperformed folded constant. -/
def bstep2Prog (A : Matrix (Fin 2) (Fin 2) ℚ) : Prog Reg ℚ :=
  .bind (coreOps A) (fun _ => .pure (A 0 0 * A 1 1 - A 0 1 * A 1 0))

/-! ## 3.  Running the three operations -/

/-- **The effect of `coreOps A`.**  The final state, the (unit) value and the
cost are all computed by `run`: the two products land in `rM1`, `rM2`, the
subtraction in `rOut`, and the bit cost is the sum of the three costs derived
from the actual operands. -/
theorem coreOps_run (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    run (coreOps A) s =
      (Function.update
          (Function.update
            (Function.update s rM1 (s rA00 * (A 1 1))) rM2 (s rA01 * (A 1 0)))
          rOut (s rA00 * (A 1 1) - A 0 1 * (A 1 0)),
        (),
        ⟨3, ratBitCost FieldOp.mul (s rA00) (A 1 1)
            + ratBitCost FieldOp.mul (s rA01) (A 1 0)
            + ratBitCost FieldOp.sub (s rA00 * (A 1 1)) (A 0 1 * (A 1 0))⟩) := by
  simp [coreOps, run_bind, run_primitive, evalPrimitive, applyFieldOp, Function.update,
    cost_add_mk, Nat.add_assoc]

/-- The three operations cost exactly three algorithmic steps. -/
theorem coreOps_alg (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (coreOps A) s).2.2.alg = 3 := by
  rw [coreOps_run]

/-- The bit cost of the three operations, as derived from the state they start
in. -/
theorem coreOps_bit (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (coreOps A) s).2.2.bit
      = ratBitCost FieldOp.mul (s rA00) (A 1 1)
        + ratBitCost FieldOp.mul (s rA01) (A 1 0)
        + ratBitCost FieldOp.sub (s rA00 * (A 1 1)) (A 0 1 * (A 1 0)) := by
  rw [coreOps_run]

/-- The first product is really computed: `rM1` holds `(state rA00) * A 1 1`,
i.e. `A 0 0 * A 1 1` once the operand has been loaded. -/
theorem coreOps_state_rM1 (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (coreOps A) s).1 rM1 = s rA00 * (A 1 1) := by
  rw [coreOps_run]
  simp [Function.update]

/-- The second product is really computed: `rM2` holds `(state rA01) * A 1 0`,
i.e. `A 0 1 * A 1 0` once the operand has been loaded. -/
theorem coreOps_state_rM2 (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (coreOps A) s).1 rM2 = s rA01 * (A 1 0) := by
  rw [coreOps_run]
  simp [Function.update]

/-- The subtraction is really performed, on the computed first product: `rOut`
holds `(state rA00) * A 1 1 - A 0 1 * A 1 0`, i.e. the Bareiss numerator
`A 0 0 * A 1 1 - A 0 1 * A 1 0` once the operand has been loaded. -/
theorem coreOps_state_rOut (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (coreOps A) s).1 rOut = s rA00 * (A 1 1) - A 0 1 * (A 1 0) := by
  rw [coreOps_run]
  simp [Function.update]

/-! ## 4.  Running the compiled step -/

/-- **The run of `bstep2Prog`.**  The output value is the Bareiss numerator; the
cost is the cost of the three operations (the trailing `pure` is free); the final
state still holds the computed entry in `rOut`. -/
theorem bstep2Prog_run (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    run (bstep2Prog A) s =
      (Function.update
          (Function.update
            (Function.update s rM1 (s rA00 * (A 1 1))) rM2 (s rA01 * (A 1 0)))
          rOut (s rA00 * (A 1 1) - A 0 1 * (A 1 0)),
        A 0 0 * A 1 1 - A 0 1 * A 1 0,
        ⟨3, ratBitCost FieldOp.mul (s rA00) (A 1 1)
            + ratBitCost FieldOp.mul (s rA01) (A 1 0)
            + ratBitCost FieldOp.sub (s rA00 * (A 1 1)) (A 0 1 * (A 1 0))⟩) := by
  have h : run (bstep2Prog A) s
      = ((run (coreOps A) s).1, A 0 0 * A 1 1 - A 0 1 * A 1 0, (run (coreOps A) s).2.2) := by
    simp [bstep2Prog, run_bind_pure]
  rw [h, coreOps_run]

/-! ### 4.1  (1) Correctness -/

/-- **The output value is the paper's quantity** `A 0 0 * A 1 1 - A 0 1 * A 1 0`
(the numerator of the first Bareiss step). -/
theorem bstep2Prog_value (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (bstep2Prog A) s).2.1 = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  rw [bstep2Prog_run]

/-- **The output value is the determinant of the `2 × 2` matrix.** -/
theorem bstep2Prog_value_eq_det (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (bstep2Prog A) s).2.1 = A.det := by
  rw [bstep2Prog_value, Matrix.det_fin_two]

/-- **The output value is the paper's fraction-free numerator**
`bStepNum A 0 1 1 = A 0 0 * A 1 1 - A 1 0 * A 0 1` (`BareissBase.lean`). -/
theorem bstep2Prog_value_eq_bStepNum (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (bstep2Prog A) s).2.1 = bStepNum A 0 1 1 := by
  rw [bstep2Prog_value, bStepNum]
  ring

/-- **The value is the step-`0` bordered `2 × 2` minor** (`bMinor2`, and via
`bStepNum_zero_eq_minor2` the entry the Bareiss tableau starts from). -/
theorem bstep2Prog_value_eq_bMinor2 (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (bstep2Prog A) s).2.1 = bMinor2 A 0 1 1 := by
  rw [bstep2Prog_value_eq_bStepNum]
  exact bStepNum_zero_eq_minor2 A 1 1

/-- **The value returned is the value computed in the register file**: the
`pure` output agrees with the content of `rOut` produced by the three domain
operations.  This is what rules out reading the output as an unperformed folded
constant. -/
theorem bstep2Prog_reg_out (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg)
    (h00 : s rA00 = A 0 0) :
    (run (bstep2Prog A) s).1 rOut = (run (bstep2Prog A) s).2.1 := by
  rw [bstep2Prog_run, h00]
  simp [Function.update]

/-- The register content is the determinant as well. -/
theorem bstep2Prog_reg_out_eq_det (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg)
    (h00 : s rA00 = A 0 0) :
    (run (bstep2Prog A) s).1 rOut = A.det := by
  rw [bstep2Prog_reg_out A s h00, bstep2Prog_value_eq_det]

/-- The compiled step agrees with the Bareiss algorithm's step (`bStep` with the
previous pivot `1`), i.e. with the entry the algorithm actually produces. -/
theorem bstep2Prog_value_eq_bStep (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (bstep2Prog A) s).2.1 = bStep A 1 0 1 1 := by
  rw [bStep, bStepNum, bstep2Prog_value, div_one]
  ring

/-! ### 4.2  (2) Domain-operation count -/

/-- **The program performs exactly three domain operations** (two
multiplications and one subtraction), as counted by `run` from the semantics. -/
theorem bstep2Prog_alg (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (bstep2Prog A) s).2.2.alg = 3 := by
  rw [bstep2Prog_run]

/-! ### 4.3  (3) The composed bit-cost bound -/

/-- **The bit cost of the compiled step, before specialising the state.** -/
theorem bstep2Prog_bit (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (bstep2Prog A) s).2.2.bit
      = ratBitCost FieldOp.mul (s rA00) (A 1 1)
        + ratBitCost FieldOp.mul (s rA01) (A 1 0)
        + ratBitCost FieldOp.sub (s rA00 * (A 1 1)) (A 0 1 * (A 1 0)) := by
  rw [bstep2Prog_run]

/-- **(3) The composed bound.**  If the state holds the two operands
(`s rA00 = A 0 0`, `s rA01 = A 0 1`), the derived bit cost of the whole step is
at most the sum of the three derived field-operation costs.  (It is in fact
*equal*; `bstep2Prog_bit` is the equality form.) -/
theorem bstep2Prog_bit_le (A : Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg)
    (h00 : s rA00 = A 0 0) (h01 : s rA01 = A 0 1) :
    (run (bstep2Prog A) s).2.2.bit
      ≤ ratBitCost FieldOp.mul (A 0 0) (A 1 1)
        + ratBitCost FieldOp.mul (A 0 1) (A 1 0)
        + ratBitCost FieldOp.sub (A 0 0 * A 1 1) (A 0 1 * A 1 0) := by
  rw [bstep2Prog_bit, h00, h01]

/-! ## 5.  (4) The `forFin` generalisation: `n` independent `2 × 2` steps -/

/-- The bound of the `k`-th iteration: the two loads (`write` of `A 0 0` and
`A 0 1`) followed by the three domain operations of the Bareiss step. -/
def batchBound {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ) (k : Fin n) : ℕ :=
  bitLenRat (Avec k 0 0) + bitLenRat (Avec k 0 1)
    + ratBitCost FieldOp.mul (Avec k 0 0) (Avec k 1 1)
    + ratBitCost FieldOp.mul (Avec k 0 1) (Avec k 1 0)
    + ratBitCost FieldOp.sub (Avec k 0 0 * (Avec k 1 1)) (Avec k 0 1 * (Avec k 1 0))

/-- **One loop iteration**: load the two operands of the `k`-th matrix into the
register file, then run the same three domain operations as `bstep2Prog`. -/
def loadBody {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ) (k : Fin n) :
    Prog Reg Unit :=
  .bind (.write rA00 (Avec k 0 0)) (fun _ =>
    .bind (.write rA01 (Avec k 0 1)) (fun _ => coreOps (Avec k)))

/-- **The `forFin` loop** computing the first Bareiss step of every matrix in the
`n`-tuple. -/
def batchProg {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ) : Prog Reg Unit :=
  .forFin (loadBody Avec)

/-- **The effect and cost of one iteration.**  The two loads put the operands in
place, so the cost does not depend on the state the iteration starts in. -/
theorem loadBody_run {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ) (k : Fin n)
    (t : St Reg) :
    run (loadBody Avec k) t =
      (Function.update
          (Function.update
            (Function.update
              (Function.update (Function.update t rA00 (Avec k 0 0)) rA01 (Avec k 0 1))
              rM1 (Avec k 0 0 * (Avec k 1 1)))
            rM2 (Avec k 0 1 * (Avec k 1 0)))
          rOut (Avec k 0 0 * (Avec k 1 1) - Avec k 0 1 * (Avec k 1 0)),
        (),
        ⟨5, batchBound Avec k⟩) := by
  simp [loadBody, run_bind, run_write, coreOps_run, batchBound, Function.update,
    cost_add_mk, Nat.add_assoc]

/-- The bit cost of one iteration is `batchBound`, independently of the state. -/
theorem loadBody_bit {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ) (k : Fin n)
    (t : St Reg) :
    (run (loadBody Avec k) t).2.2.bit = batchBound Avec k := by
  rw [loadBody_run]

/-- One iteration performs five operations: two loads and three domain
operations. -/
theorem loadBody_alg {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ) (k : Fin n)
    (t : St Reg) :
    (run (loadBody Avec k) t).2.2.alg = 5 := by
  rw [loadBody_run]

/-- **The loop cost is exactly the sum of the per-iteration bounds**
(`run_forFin_bit_eq_sum`), because every iteration's cost is state-independent. -/
theorem batchProg_bit_eq_sum {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ)
    (s : St Reg) :
    (run (batchProg Avec) s).2.2.bit = ∑ k : Fin n, batchBound Avec k := by
  rw [batchProg, run_forFin_bit_eq_sum]
  exact Finset.sum_congr rfl (fun k _ => loadBody_bit Avec k _)

/-- **(4) The `forFin` bound**: the bit cost of the `n` independent Bareiss steps
is at most the sum of the per-step bounds. -/
theorem batchProg_bit_le_sum {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ)
    (s : St Reg) :
    (run (batchProg Avec) s).2.2.bit ≤ ∑ k : Fin n, batchBound Avec k :=
  le_of_eq (batchProg_bit_eq_sum Avec s)

/-- The loop performs five operations per iteration, `n` times. -/
theorem batchProg_alg {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ) (s : St Reg) :
    (run (batchProg Avec) s).2.2.alg = n * 5 := by
  rw [batchProg, run_alg_eq_primitiveCount]
  calc ∑ k : Fin n, (run (loadBody Avec k) (statesOf n (loadBody Avec) s k)).2.2.alg
      = ∑ _k : Fin n, 5 := Finset.sum_congr rfl (fun k _ => loadBody_alg Avec k _)
    _ = n * 5 := by simp [Finset.sum_const]

/-- **Every iteration computes the determinant of its own matrix** into the
register `rOut`: the loop is a loop of correct Bareiss steps. -/
theorem loadBody_out {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ) (k : Fin n)
    (t : St Reg) :
    (run (loadBody Avec k) t).1 rOut = (Avec k).det := by
  rw [loadBody_run, Matrix.det_fin_two]
  simp [Function.update]

/-! ## 6.  From the sum bound to a uniform polynomial bound -/

/-- `fieldOpBitCost` is monotone in both bit lengths. -/
theorem fieldOpBitCost_mono (op : FieldOp) {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    fieldOpBitCost op a b ≤ fieldOpBitCost op a' b' := by
  cases op with
  | add =>
      simp only [fieldOpBitCost]
      have h2 : a + b + 1 ≤ a' + b' + 1 := by omega
      have h3 : (a + b + 1) ^ 2 ≤ (a' + b' + 1) ^ 2 := Nat.pow_le_pow_left h2 2
      omega
  | sub =>
      simp only [fieldOpBitCost]
      have h2 : a + b + 1 ≤ a' + b' + 1 := by omega
      have h3 : (a + b + 1) ^ 2 ≤ (a' + b' + 1) ^ 2 := Nat.pow_le_pow_left h2 2
      omega
  | mul =>
      simp only [fieldOpBitCost]
      have h1 : a * b ≤ a' * b' := Nat.mul_le_mul ha hb
      have h2 : a * b + a + b + 1 ≤ a' * b' + a' + b' + 1 := by omega
      have h3 : (a * b + a + b + 1) ^ 2 ≤ (a' * b' + a' + b' + 1) ^ 2 :=
        Nat.pow_le_pow_left h2 2
      omega
  | div =>
      simp only [fieldOpBitCost]
      have h1 : a * b ≤ a' * b' := Nat.mul_le_mul ha hb
      have h2 : a * b + a + b + 1 ≤ a' * b' + a' + b' + 1 := by omega
      have h3 : (a * b + a + b + 1) ^ 2 ≤ (a' * b' + a' + b' + 1) ^ 2 :=
        Nat.pow_le_pow_left h2 2
      omega
  | inv =>
      simp only [fieldOpBitCost]
      have h2 : a + 1 ≤ a' + 1 := by omega
      have h3 : (a + 1) ^ 2 ≤ (a' + 1) ^ 2 := Nat.pow_le_pow_left h2 2
      omega

/-- **The per-iteration bound in terms of a uniform bit length `β`.**  If every
entry of every matrix in the tuple has at most `β` bits, one iteration costs at
most `2β` (the two loads) plus the two products and the subtraction, each
dominated by `fieldOpBitCost` at `β` (the subtraction's operands are products,
hence have at most `2β` bits). -/
theorem batchBound_le {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ) (β : ℕ)
    (hβ : ∀ (k : Fin n) (i j : Fin 2), bitLenRat (Avec k i j) ≤ β) (k : Fin n) :
    batchBound Avec k
      ≤ 2 * β + 2 * fieldOpBitCost FieldOp.mul β β
        + fieldOpBitCost FieldOp.sub (2 * β) (2 * β) := by
  have h00 : bitLenRat (Avec k 0 0) ≤ β := hβ k 0 0
  have h01 : bitLenRat (Avec k 0 1) ≤ β := hβ k 0 1
  have h11 : bitLenRat (Avec k 1 1) ≤ β := hβ k 1 1
  have h10 : bitLenRat (Avec k 1 0) ≤ β := hβ k 1 0
  have hm1 : ratBitCost FieldOp.mul (Avec k 0 0) (Avec k 1 1)
      ≤ fieldOpBitCost FieldOp.mul β β :=
    le_trans (ratBitCost_le_fieldOpBitCost _ _ _) (fieldOpBitCost_mono _ h00 h11)
  have hm2 : ratBitCost FieldOp.mul (Avec k 0 1) (Avec k 1 0)
      ≤ fieldOpBitCost FieldOp.mul β β :=
    le_trans (ratBitCost_le_fieldOpBitCost _ _ _) (fieldOpBitCost_mono _ h01 h10)
  have hp1 : bitLenRat (Avec k 0 0 * (Avec k 1 1)) ≤ 2 * β := by
    have h := bitLenRat_mul (Avec k 0 0) (Avec k 1 1)
    omega
  have hp2 : bitLenRat (Avec k 0 1 * (Avec k 1 0)) ≤ 2 * β := by
    have h := bitLenRat_mul (Avec k 0 1) (Avec k 1 0)
    omega
  have hs : ratBitCost FieldOp.sub (Avec k 0 0 * (Avec k 1 1)) (Avec k 0 1 * (Avec k 1 0))
      ≤ fieldOpBitCost FieldOp.sub (2 * β) (2 * β) :=
    le_trans (ratBitCost_le_fieldOpBitCost _ _ _) (fieldOpBitCost_mono _ hp1 hp2)
  simp only [batchBound]
  omega

/-- **(4') The uniform polynomial bound.**  For `n` independent `2 × 2` rational
matrices whose entries all have at most `β` bits, the loop's derived bit cost is
at most `n` times an explicit polynomial in `β`:

`n * (2β + 2 · fieldOpBitCost .mul β β + fieldOpBitCost .sub (2β) (2β))`.

This is the `run_bit_le_sum` form of the bound: the per-iteration bound is
uniform over the iterations. -/
theorem batchProg_bit_le_uniform {n : ℕ} (Avec : Fin n → Matrix (Fin 2) (Fin 2) ℚ)
    (s : St Reg) (β : ℕ) (hβ : ∀ (k : Fin n) (i j : Fin 2), bitLenRat (Avec k i j) ≤ β) :
    (run (batchProg Avec) s).2.2.bit
      ≤ n * (2 * β + 2 * fieldOpBitCost FieldOp.mul β β
          + fieldOpBitCost FieldOp.sub (2 * β) (2 * β)) := by
  have hB : ∀ k : Fin n,
      (run (loadBody Avec k) (statesOf n (loadBody Avec) s k)).2.2.bit
        ≤ 2 * β + 2 * fieldOpBitCost FieldOp.mul β β
          + fieldOpBitCost FieldOp.sub (2 * β) (2 * β) := by
    intro k
    rw [loadBody_bit]
    exact batchBound_le Avec β hβ k
  have h := run_bit_le_sum n (loadBody Avec) s
    (2 * β + 2 * fieldOpBitCost FieldOp.mul β β
      + fieldOpBitCost FieldOp.sub (2 * β) (2 * β)) hB
  simpa [batchProg] using h

end BareissCost
end Q1Complexity
