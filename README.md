# Parameterized algorithms for functional observer feasibility — artifact

This repository contains the Lean formalization, the exact verification scripts and the
LaTeX source of the paper

> **Parameterized algorithms for functional observer feasibility**
> (anonymous submission; the author block is empty by design).

The paper studies the decision complexity of minimum-order functional observer design:
given $(A,C,L_0)$ and a prescribed order $q$, decide whether an observer $L=[L_0;R]$ of
order $q$ exists. It proves two parameterized upper bounds (fixed $q$; fixed effective
dimension $\kappa_{\rm obs}=r\,\mathrm{rank}[N\ AN]$), closes the zero-free-row case with
a finite rational linear system, and records membership in $\exists\mathbb R$.

## Layout

```
lean-toolchain, lakefile.toml, Q1Paper.lean   # Lean project (Mathlib pinned to v4.35.0)
Q1Paper/                                      # the Lean sources
  Basic.lean  Compression.lean  FreeRows.lean  RankConsistency.lean
  SpectralCertificate.lean  FixedOrder.lean  FPT.lean  Audit.lean  Legacy/
scripts/check.sh                              # lake build + Audit.lean + axiom audit
verification/                                 # exact rational checks (Python + sympy)
paper/                                        # LaTeX source and compiled PDF
  paper_I_dec.tex                 # decision complexity (Paper I)
  paper_II_minorder.tex           # minimum order (Paper II)
  hyperplane_layer.tex            # the hyperplane layer (Paper III)
```

## Build

Lean (requires `elan`; Mathlib is fetched on the first build):

```text
lake exe cache get
lake build
lake env lean Q1Paper/Audit.lean     # axiom audit: only propext, Classical.choice, Quot.sound
bash scripts/check.sh
```

Paper (requires TeX Live):

```text
cd paper && pdflatex paper_I_dec.tex && pdflatex paper_I_dec.tex
cd paper && pdflatex paper_II_minorder.tex && pdflatex paper_II_minorder.tex
cd paper && pdflatex hyperplane_layer.tex && pdflatex hyperplane_layer.tex
```

## What is verified, and how

| Component | Evidence |
|---|---|
| Compression criterion `ker_compressed_iff` | Lean (`Compression.lean`) |
| Free-pair space, $k\le d_0\le\kappa_{\rm obs}$ | Lean (`FreeRows.lean`) |
| Rank-consistency (subspace form) | Lean (`RankConsistency.lean`) |
| Bézout for two polynomials, left inverse $\Rightarrow$ injective | Lean (`SpectralCertificate.lean`, `FPT.lean`) |
| Bézout degree bound for $s$ polynomials | paper proof (Appendix A) |
| Cauchy–Binet Gram-compression | paper proof + exact checks (`c317`) |
| $r=0$ linear system (R0) | paper proof + exact checks (`c318`) |
| Coefficient bit-size bounds | paper proof |
| $\exists\mathbb R$ encoding | paper proof + witness check (`c319`) |
| Hyperplane layer: direction theorem (admissible kernel direction $=$ eigenvector of the compression) | Lean (`HyperplaneDirection.lean`) |
| Hyperplane layer: prescribed-row orthogonality and independence of $\delta$ | Lean (`HyperplanePrescribed.lean`) |

The Python scripts are **finite exact checks, not proofs**; each prints the instance data
it checks and asserts the basic invariants first. Run them from `verification/`:

```text
python c312_fixed_q_factor.py
python c317_cauchy_binet_random.py
python c318_r0_linear_system.py
python c319_encoding_and_rowspace.py
```

## License

Code (Lean sources, scripts): MIT — see `LICENSE`.
Paper (LaTeX source and PDF): CC BY 4.0.

## Status

Work in progress: the Mathlib pin is fixed by `lean-toolchain`; a `lake-manifest.json`
will be committed once the project is built with the public dependency graph. The paper
is under revision; see the repository history.
