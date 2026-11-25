/-
Q1Paper/PaperII/Read.lean

Reading entry for Paper II's Lean development, in the paper's order.

Paper II's mathematics runs: the subspace sandwich (Paper I's Claims 4–6, reused
through the column split `Φ`) → the decision predicate `DECℂ` (real designs,
complex ranks) → monotonicity, saturation and the minimum order `q_min = r₀ + t_min`
→ the spectral lower bound `rank[U₀;V₀] + 1 ≤ s₀ + t` and its tightness criterion.
The modules below appear in that order.

* `Interface.lean` — the column split `Φ`, the quotient dimension `t`, `IsFeasible`.
* `Sandwich.lean` — `W₀`, `T`, `W`, and the forward sandwich (real designs).
* `Monotone.lean` — `DECℂ r → DECℂ r'`.
* `LowerBound.lean` — Proposition 2 and the numerical half of Proposition 3.
* `Converse.lean` — the converse sandwich for complex designs.
* `Saturate.lean` — saturation and monotonicity for complex designs.
* `MinOrder.lean` — `t_min` and `q_min = r₀ + t_min` (complex designs), `t_min ≤ 2ℓ`.
* `GraphExtension.lean` — `W(G,b)`, its pencil, and the `(G,b)` direction of Prop 3.
* `GraphExtract.lean` — the converse of Prop 3: `W = W(G,b)`.
* `Realification.lean` — the real-compression lemma and the real-design version of
  saturation and of the minimum order.

The paper item → declaration table is `Claims.lean` (narrated) and
`ClaimsCheck.lean` (machine-checked); the axiom footprint is `Audit.lean`.
-/

import Q1Paper.PaperII.Interface
import Q1Paper.PaperII.Sandwich
import Q1Paper.PaperII.Monotone
import Q1Paper.PaperII.LowerBound
import Q1Paper.PaperII.Converse
import Q1Paper.PaperII.Saturate
import Q1Paper.PaperII.MinOrder
import Q1Paper.PaperII.GraphExtension
import Q1Paper.PaperII.GraphExtract
import Q1Paper.PaperII.Realification
