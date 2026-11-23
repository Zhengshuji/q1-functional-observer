# Exact verification scripts

These scripts perform **finite exact checks** (rational arithmetic via `fractions`,
`sympy` where noted) of the identities used in the papers. They are *not* proofs and do
not replace the paper arguments or the Lean kernel; each one prints the instance it
checks and asserts the basic invariants before drawing a conclusion.

Run a script from this directory: `python cNNN_<topic>.py`.

**Naming.** `cNNN_<topic>.py` where `NNN` is the attempt number in the research log.
Shared helpers carry no number.

## CI gates (run by `.github/workflows/build.yml`)

| Script | What it checks |
|---|---|
| `c317_cauchy_binet_random.py` | $K(\lambda,\mu)=\sum_{I,J}f_{IJ}(\lambda)f_{IJ}(\mu)$ and the coefficient identity (Paper I, Section V) |
| `c318_r0_linear_system.py` | the linear system (R0) $\iff$ the gcd test, with counts and the degree bound (Proposition 1, Appendix A) |
| `c319_encoding_and_rowspace.py` | the coefficient-vector row space, the encoding witness, necessity of the data constraints (Theorem 3, Appendix A) |

## Evidence (not run by CI; kept as the exact-arithmetic record)

| Script | What it checks |
|---|---|
| `c311_rank_consistency.py` | the rank-consistency elimination identity on random systems (Lemma 3) |
| `c312_fixed_q_factor.py` | $H=XB$, $B_{:,J}=I_\omega$, $H_A=FH$ on a feasible instance (Section VI) |
| `c313_gram_indexing.py` | the shifted-index formula and $e_0\in\operatorname{row}Z$ for the 2-4-4 pencil (Lemma 5) |
| `c314_G_form.py` | $G=FX$, $H_A=GB$ and the rank identity (Section V) |
| `c315_r0_left_inverse.py` | the rectangular adjugate: $SZ=I_\omega$ and $\deg S\le2\omega-2$ (Appendix A) |
| `c316_gram_certificate_random.py` | the Gram certificate on random polynomial families, with common-root negative controls (Lemma 5) |
| `c320_subspace_reduction.py` | the subspace (quotient) reduction of DEC |
| `c321_dimensional_test.py` | whether feasibility is determined by the dimensions alone under the reduction |
| `c322_opt_find.py` | OPT and FIND under the subspace reduction |
| `c323_common_projection_core.py` | the iterated common-projection core $S_*$ of the reduction |
| `c324_boundary_cases.py` | the boundary cases of the reduction listed in the expert reply |
| `c325_fer26b_example_audit.py` | audit of the illustrative example of the referenced paper |
| `c326_fer26b_order4_observer.py` | the explicit order-4 functional observer for that example |
| `c328_example_direct_dec.py` | the criteria applied directly to that order-4 observer |
| `c329_bounds_comparison.py` | comparison of the spectral lower bound with the quotient-space bound |

## Shared helpers

| Script | Role |
|---|---|
| `spectral_gcd.py` | exact maximal-minor gcd machinery (with direction assertions) |
| `audit_independent.py` | the independent audit driver |

## Known limitation

`c319`'s fourth check (a negative control on an external example) needs data that is not
bundled in this repository; it is skipped here and runs in the paper's research
repository.
