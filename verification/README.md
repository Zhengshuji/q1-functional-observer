# Exact verification scripts

These scripts perform **finite exact checks** (rational arithmetic via `fractions` and
`sympy`) of the identities used in the paper. They are *not* proofs and do not replace
the paper arguments or the Lean kernel; each one prints the instance it checks and
asserts the basic invariants before drawing conclusions.

Run each script from this directory (`python cXXX_*.py`); the shared dependencies
(`spectral_gcd.py`, `audit_independent.py`) are bundled here.

| Script | What it checks | Paper location |
|---|---|---|
| `c311_rank_consistency.py` | rank-consistency identity on random systems | Lemma 3 |
| `c312_fixed_q_factor.py` | $H=XB$, $B_{:,J}=I_\omega$, $H_A=FH$ on random instances | Section VI |
| `c313_gram_indexing.py` | shifted-index formula and $e_0\in\operatorname{row}Z$ | Lemma 5 |
| `c314_G_form.py` | $G=FX$, $H_A=GB$, rank identity | Section V |
| `c315_r0_left_inverse.py` | rectangular adjugate: $SZ=I_\omega$ and $\deg S\le2\omega-2$ | Appendix A |
| `c316_gram_certificate_random.py` | Gram certificate, with common-root negative controls | Lemma 5 |
| `c317_cauchy_binet_random.py` | $K(\lambda,\mu)=\sum_{I,J}f_{IJ}(\lambda)f_{IJ}(\mu)$ and the coefficient identity | Section V |
| `c318_r0_linear_system.py` | linear system (R0) $\iff$ gcd test; counts and degree bound | Proposition 1, Appendix A |
| `c319_encoding_and_rowspace.py` | coefficient-vector row space; encoding witness; necessity of the data constraints | Theorem 3, Appendix A |

Note: `c319`'s fourth check (a negative control on an external example) needs data that
is not bundled in this repository; it is skipped here and runs in the paper's research
repository.

Script/statement names in the table refer to the paper's numbering; if the paper is
renumbered, the table is updated in the same commit.
