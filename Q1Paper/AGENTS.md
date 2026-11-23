# AGENTS.md — Paper I Lean handoff for subagents

Read this file FIRST. It removes the need to rediscover the environment.

## 1. Environment (do not search for it)

- The Lean project lives **only** in WSL: `/home/zsj/WorkSpace/lean4/Q1Paper/`.
- Toolchain `leanprover/lean4:v4.35.0` + Mathlib (path dep). Run everything as:

```
wsl -e bash -lc 'cd /home/zsj/WorkSpace/lean4/Q1Paper && export PATH="$HOME/.elan/bin:$PATH" && lake env lean Q1Paper/<file>.lean'
```

- The Windows git repo (`C:\Users\26074\Desktop\工作 学习（待办）\q1-functional-observer`)
  is the **artifact** copy; **never** edit it from a subagent. The main agent promotes files.
- Work in a single new file `Q1Paper/Scratch<Name>.lean`. Do not modify existing files.
- Overwriting files under `\\wsl$\...` from Windows tools can fail with `GetFileSecurityW EIO`;
  copy to `/mnt/c/Windows/Temp/` and `cp` back inside WSL instead.

## 2. Deliverable rules (non-negotiable)

- No `sorry`, no `admit`, no `axiom`, no `native_decide` unless explicitly agreed.
- Every declaration must compile; if a statement cannot be proved, **delete it** and report
  precisely what failed — never axiomatize.
- Report format (always):
  1. exact statements proved (verbatim, with hypotheses);
  2. the compile command and its exit status;
  3. the proof route and the exact lemmas used;
  4. what remains, with the precise missing ingredient;
  5. the file path and its size.
- State restrictions honestly: a true restricted theorem is worth far more than a general axiom.

## 3. Conventions and pitfalls already paid for

- Use `omit [IsAlgClosed K] in` when a lemma does not need an instance that a `variable` block supplies.
- `Ext`/`rw` on matrices of polynomials: prefer `funext i j` over `ext i j` (`ext` recurses into
  `Polynomial.ext` and produces coefficient-level goals).
- `(∏ x in s, f x).size` may fail to parse; write `(s.prod f).size`.
- `Matrix.mulVec`/`smul` lemmas are named `smul_mulVec`, `mulVec_smul` (no `Matrix.` prefix in `rw`).
- Proof terms from `Set.powersetCard`/`Finset` coercions cause `whnf` blowups: bridge with
  `funext i; apply Fin.ext; simp` (see `rowEmb_imageFin` in `PaperI/MinorFamilyBridge.lean`).
- `det_submatrix_perm` requires `[CommRing R]` (a field-only version diverges on `K[X]`).
- Name clashes are real: before declaring, grep the tree for the name
  (`grep -rn "theorem <name>" Q1Paper/`); rename with a suffix if taken.
- `#print axioms` on a `def` works; on a theorem it prints the axiom list.

## 4. API index (start here instead of searching)

| Topic | File |
|---|---|
| DEC / DECℂ definitions | `PaperI/Interface.lean` |
| compression, `DEC_iff_compressed`, `exists_factor_of_rawAlgebraic` | `PaperI/CompressionMatrix.lean` |
| Gram certificate, `gram_certificate` | `PaperI/Gram.lean` |
| Bézout / window (Claim 9/10) | `PaperI/Claim11.lean`, `Window.lean` |
| rank = largest nonzero minor, `exists_det_submatrix_ne_zero_of_rank` | `PaperI/MinorRank.lean` |
| spectral ⇔ minors (Claim 11) | `PaperI/SpectralMinor.lean` |
| real ⇔ complex rank (`rank_map_ofReal`) | `PaperI/Complexify.lean` |
| Claim 11 final, `minorFamily`, `natDegree_maximalMinor_le` | `PaperI/Claim11Final.lean` |
| Claim 12 | `PaperI/Claim12.lean` |
| square Cauchy–Binet (ported, Apache-2.0) | `PaperI/CauchyBinet.lean` |
| Gram kernel / coefficients / window Gram | `PaperI/GramKernel.lean`, `GramCoefficients.lean`, `GramCompression.lean` |
| D1 bridge (sign, coefficient, window row, Gram `(ω!)²`, certificate, row space) | `MinorFamilyBridge.lean`, `WindowSign.lean`, `GramInj.lean`, `GramCert.lean`, `RowSpanBridge.lean` |
| bit length (`bitLenInt`, `bitLenRat`, `bitLenMat`), Leibniz | `BitLen.lean`, `BitLenAdd.lean`, `InputLen.lean` |
| Bareiss (D–J, tableau, bit bounds) | `DesnanotJacobi.lean`, `BareissTableau.lean`, `BareissAssemble.lean`, `BareissBase.lean` |
| Claim 13 rational bases (`tauM`) | `RationalBasis.lean` |
| Claim 14 intersection | `Claim14.lean` |
| Claim 15(iv) arithmetic skeleton | `Claim15iv.lean` |
| Claim 16 (five conditions, gcd) | `Claim16.lean`, `C16Gcd.lean` |
| Claims 3–8 bridges | `Claims38.lean` |
| rank factorization (left/right inverses) | `RankFactorization.lean` |
| Theorem 5 (encodes, DECℂ, D-form, ω=0) | `Theorem5.lean`, `T5Complete.lean`, `T5DecC.lean` |
| fibre sums/cardinalities | `FibreSum.lean`, `FibreCard.lean` |

## 5. Integration checklist (main agent only)

Use `python scripts/promote_paperI.py --scratch ScratchFoo.lean --name Foo --axioms "<names>"`,
which copies, fixes the header, strips `#print`, checks name clashes, wires `MainTheorems`,
adds the audit lines, builds, runs the axiom check and prints the count. Then commit and push.

## 6. Interaction with ChatGPT

Subagents must not drive the browser (one tab, shared with the main agent). If a design question
is unclear, put the precise question in the report; the main agent relays it to ChatGPT and
relaunches with the answer embedded. Do not block on the browser.
