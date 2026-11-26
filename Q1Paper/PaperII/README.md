# Paper II in Lean

The Lean 4 formalisation of *Minimum-order functional observers: an interface between decision,
optimisation and construction* (Paper II).  Every mathematical assertion of the paper that is not
a citation to the companion paper has a machine-checked declaration here; this directory is the
whole of that formalisation.

## Verification

From the project root (`~/WorkSpace/lean4/Q1Paper`, toolchain `leanprover/lean4:v4.35.0`):

| command | what it checks |
|---|---|
| `lake build Q1Paper.PaperII.MainTheorems` | the whole development compiles |
| `lake build Q1Paper.PaperII.Read.All` | every declaration named in the reading entries resolves |
| `lake env lean Q1Paper/PaperII/ClaimsCheck.lean` | every name in the claim table resolves |
| `lake env lean Q1Paper/PaperII/Audit.lean` | one `#print axioms` per declaration |
| `python scripts/check_paperI_axioms.py <log> Q1Paper/PaperII/Audit.lean` | the axiom audit |
| `python scripts/generate_audit.py --check` | `Audit.lean` is up to date |
| `python scripts/generate_paperII_modules.py --check` | `MODULES.md` is up to date |
| `python scripts/generate_paperII_claims.py --check` | `CLAIMS.md` is up to date and every name in it is checked |
| `python scripts/check_consistency.py` | docstring paths, module mentions and declaration references resolve |

## Axiom policy

Only `propext`, `Classical.choice` and `Quot.sound` are allowed.  Of the audited declarations 184
depend on exactly that set and one (`bisectGo`, a computable definition) depends on nothing at
all; any declaration outside the policy fails `check_paperI_axioms.py`.

## Reading order

`Read/S01`–`Read/S07` follow the paper's order, one `#check` per step and no proofs:

| entry | paper section | carries |
|---|---|---|
| `S01_Standing` | §I–II | the standing results of Paper I, the pair encoding, `t`, `IsFeasible` |
| `S02_Sandwich` | §III | the sandwich (`DEC` and `DECℂ`), monotonicity, saturation |
| `S03_MinOrder` | §III | the minimum order `q_min = r₀ + t_min`, attainment, `t_min ≤ 2ℓ` |
| `S04_LowerBound` | §III | the spectral lower bound `a + 1 − s₀ ≤ t_min` |
| `S05_Tightness` | §III | Proposition 3 for complex designs, packaged as a single `↔` |
| `S06_RealDesigns` | §III | the real-design specification `DECℂ` and Proposition 3 for it |
| `S07_Algorithms` | §V | the `O(log(ℓ+2))` count, the bisection, `OPT` |

Two generated indexes sit next to the Lean files: `CLAIMS.md` (paper item → declarations, for
readers who do not know Lean) and `MODULES.md` (module → declarations).

## Modules

| module | role |
|---|---|
| `Interface.lean` | the interface: `IsFeasible`, the pair encoding, `t` |
| `Sandwich.lean` | `W₀`, `T`, `W`, the sandwich, the real-compression lemma |
| `Monotone.lean`, `Saturate.lean` | monotonicity and saturation of the decision predicate |
| `MinOrder.lean` | `tMin`, `tMinSet`, `t_min ≤ r ↔ DEC (r₀+r)`, `t_min ≤ 2ℓ` |
| `LowerBound.lean` | the spectral lower bound |
| `Tightness.lean` | Proposition 3 for complex designs, both directions and the packaging |
| `GraphExtension.lean`, `GraphExtract.lean` | `W(G,b)`, its pencil and its feasibility; the converse |
| `Converse.lean` | the converse sandwich for complex designs |
| `Realification.lean` | `DECℂ`, `UC`, `tMinC`, the real-compression step |
| `RealGraph.lean` | the real↔complex bridges, the real sandwich converse, Proposition 3 for real designs |
| `Complexity.lean` | the call count, the bisection algorithm and its correctness, `OPT` |
| `Appendix.lean` | the appendix instance at `λ = 0` |
| `Claims.lean`, `ClaimsCheck.lean` | the narrative claim table and its `#check`s |
| `Audit.lean` | the generated axiom audit |

## Coverage

Formalised, with declarations named in `docs/PAPER_II_PROOF_MAP.md`: the standing results,
Claims 1–5, Propositions 1–3 (complex designs *and* the paper's real designs, both packaged as a
single `↔`), the interface theorem (ordering half, call count, and the bisection algorithm with
its termination, correctness and the `OPT` corollary, in both the complex and the real form), and
the mathematical kernel of `FIND` (the sandwich and pencil conditions equivalent to feasibility).

Not formalised, with reasons:

* the chart parametrisation of `Ψ_{t,ω}` (`W = row[XB GB]`, the matrix `B` read off `X` on the
  pivot set), the sampling-point algorithm and its bit cost — the paper states all three as
  citations to the companion paper (`Remark rem:find-bit`), not as results of this paper;
* the appendix instance's full certificate — exact rational arithmetic over 64 minors, done by
  `scripts/verify_paperII_example.py`; `Appendix.lean` re-checks in Lean the `λ = 0` slice.

The paper-level map, including which item is proved where, is `docs/PAPER_II_PROOF_MAP.md`.
