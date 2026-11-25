# Paper II: module map

What each module of `Q1Paper/PaperII/` proves, how large it is, and which paper
items it carries.  Companion to `PAPER_II_PROOF_MAP.md` (paper item → declaration).

Scope: the `DEC` items are the field-generic predicate over `ℂ` (complex free
blocks).  `DECℂ` (real designs) has its forward direction and monotonicity; its
converse is the open real-compression lemma.

| module | purpose | lines | declarations | paper items |
|---|---|---|---|---|
| `Interface.lean` | the column split `Φ` between the row(`[N AN]`) and pair encodings; the quotient dimension `t`; the feasibility predicate and its bridge to the compressed conditions | 181 | 13 | §II `t`, the encoding bridge |
| `Sandwich.lean` | complexifications `Ac/L0c/Rc/Lc`; `W₀`, `T`, `W`; the forward sandwich | 147 | 12 | Claim 4 (forward), `DECℂ` |
| `Monotone.lean` | padding a real design with zero rows; `DECℂ r → DECℂ r'` | 165 | 4 | Claim 5 (monotone, `DECℂ`) |
| `LowerBound.lean` | `rank[U₀;V₀] ≤ ω` and the spectral lower bound `a + 1 ≤ s₀ + t` | 85 | 4 | Prop 2 |
| `Converse.lean` | the converse sandwich for complex designs (via `claim4_converse` and `Φ`) | 138 | 4 | Claim 4 (converse, `DEC`) |
| `Saturate.lean` | the forward sandwich for complex designs; saturation `DEC r ↔ DEC m`; monotonicity | 125 | 4 | Claim 5 (saturation/monotone, `DEC`) |
| `MinOrder.lean` | `t_min : WithTop ℕ`; `t_min ≤ r ↔ DEC (r₀+r)`; `t_min ≤ 2ℓ` | 136 | 7 | Prop 1 |
| `MainTheorems.lean` | import entry point | 22 | 0 | — |
| `Claims.lean` | the paper items in the paper's order, as narration | 76 | 0 | — |
| `ClaimsCheck.lean` | one `#check` per claim (machine-checked index) | 41 | 0 | — |
| `Realification.lean` | real-design bridges, `real_compress`, `feasible_to_decC`, `decC_saturates`, `tMinC_le_iff_decC` | — | — | Claim 5 / Prop 1 (`DECℂ`) |
| `GraphExtension.lean` | `W(G,b)`, its pencil, feasibility, `t_eq_of_graph` | — | — | Prop 3 (`(G,b)` direction) |
| `GraphExtract.lean` | `projU`, kernel dimension, `exists_graph_representation` | — | — | Prop 3 (converse) |
| `Audit.lean` | the axiom footprint of all declarations | — | 0 | — |

## How to check it

```bash
lake build Q1Paper.PaperII.MainTheorems
lake env lean Q1Paper/PaperII/ClaimsCheck.lean
lake env lean Q1Paper/PaperII/Audit.lean > /tmp/paperII_audit.log
python3 scripts/check_paperI_axioms.py /tmp/paperII_audit.log Q1Paper/PaperII/Audit.lean
```

## What is deliberately not here

* `DECℂ` saturation / minimum order: now proved in `PaperII/Realification.lean`
  (`real_compress`, `feasible_to_decC`, `decC_saturates`, `tMinC_le_iff_decC`), so
  this bullet is historical.
* Prop 3 (tightness), Theorem 4 (interface counting), the OPT/FIND corollaries,
  and the appendix instance: see `PAPER_II_PROOF_MAP.md` §"Not formalised".
