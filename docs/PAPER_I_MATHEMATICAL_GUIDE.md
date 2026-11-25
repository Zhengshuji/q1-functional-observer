# Paper I: a mathematical guide

This is the guide for a reader who knows the mathematics but not Lean.  It says what the paper
proves, why each step is needed for the next, and — in one line per step — which Lean module carries
it.  It deliberately does **not** explain Lean syntax; for "which declaration, which file, which
line", use `docs/PAPER_I_PROOF_MAP.md`.

The paper itself is `paper/paper_I_dec.tex`; this file is a reading companion, not a replacement.

## The problem

Given a plant $(A, C)$ and a prescribed row block $L_0$, one asks for a *functional observer*: a
matrix $\mathcal L = [L_0; R]$ whose rows, together with $C$ and $CA$, reproduce the behaviour of
$L_0$ on the reachable dynamics, without reconstructing the whole state.  Writing $LA$ for
$\mathcal L A$, the requirement is the pair of rank conditions

$$(5a)\quad \operatorname{rank}[LA;\,\mathcal L;\,CA;\,C] = \operatorname{rank}[\mathcal L;\,CA;\,C],$$

$$(5b)\quad \operatorname{rank}[\lambda\mathcal L - LA;\,CA;\,C] = \operatorname{rank}[\mathcal L;\,CA;\,C]
\quad\text{for every }\lambda .$$

$(5a)$ says the extra block $LA$ adds nothing beyond what $\mathcal L$, $CA$ and $C$ already span;
$(5b)$ says the same for the whole *pencil* $\lambda\mathcal L - LA$ at every frequency.  $(5b)$ is
the content: it is what makes the observer work at every eigenvalue, and it is quantified over the
**complex** numbers — a pencil can keep full rank at every real $\lambda$ and drop at a complex one.

**Decision problem.**  Fix the order $q$ (the number of rows of $\mathcal L$).  *Is there an $R$ such
that $(5a)$ and $(5b)$ hold?*  The paper's subject is the complexity of this question, not the
construction of a particular observer.

## Why the problem is hard, and the shape of the answer

The unknowns in $(5b)$ are the entries of $R$, and the condition is a rank condition on a pencil
whose coefficients depend on those entries.  "Rank $= k$ at every $\lambda$" is not a polynomial
condition — it is a *quantifier over $\lambda$* followed by a rank test.  There are two classical ways
to make such a condition finite:

* replace "rank drops everywhere" by "all maximal minors vanish identically", which is finitely many
  polynomial equations (this is where Bézout and the gcd enter);
* replace the unknown subspace by coordinates on a Grassmannian chart, so that the remaining
  unknowns enter polynomially (this is where the charts enter).

The paper does both, and the whole formalisation is organised around making those two reductions
exact.  Everything else is accounting: how many variables, how large the integer coefficients, how
much precision is needed.

## The steps, in the order the paper needs them

### Step 1 — compress to the invisible subspace

Everything can be pushed onto $K_0 = \ker[C; CA]$, the part of the state the measurements never see.
Choose a basis matrix $N$ of $K_0$ and put $H = \mathcal L N$, $H_A = LA\,N$.  Then $(5a)$ and $(5b)$ on
$(\mathcal L, LA)$ are **equivalent** to their compressed forms on $(H, H_A)$:

$$(5a)'\quad \operatorname{rank}[H_A; H] = \operatorname{rank} H, \qquad
(5b)'\quad \operatorname{rank}(\lambda H - H_A) = \operatorname{rank} H \ \ \forall\lambda .$$

This is Claim 1 (the rank identity $\operatorname{rank}[P;M] = \operatorname{rank}P + \operatorname{rank}(M N_P)$
that makes the dimension bookkeeping exact) and Claim 2 (the equivalence).  Its point: the free block
$R$ has now been replaced by a *pair of small matrices* $(H, H_A)$ with $H \in \mathbb C^{q \times d_0}$.

*Lean:* `Q1Paper/G4RankIdentity.lean`, `Q1Paper/PaperI/CompressionMatrix.lean`.

### Step 2 — describe which pairs $(H, H_A)$ are attainable

Not every pair comes from some $R$.  Write $W$ for the row space of the reachable part.  Then

* the attainable $W$ are exactly those with $\operatorname{row}(L_0 M) \subseteq W \subseteq \operatorname{row} M$,
  where $M$ is the reachable data (Claim 4, both directions);
* the count of degrees of freedom is $\kappa_{\text{obs}} = r\,d_0$ (Claim 3);
* for a *fixed* $W$, conditions $(5a)'$ and $(5b)'$ depend only on $W$ — never on which $R$ produced it
  (Claim 5).  **This is what makes a search over subspaces legitimate**: one test per subspace,
  not one per matrix;
* a feasible $W$ satisfies $\omega + 1 \le \dim W \le 2\omega$ (Claim 6) and the problem is monotone in
  $q$ (Claim 7).

*Lean:* `Q1Paper/PaperI/Claims38.lean`, `Q1Paper/PaperI/Claim4Converse.lean`.

### Step 3 — turn the pencil condition into linear algebra

The spectral condition $(5b)'$ says $\lambda H - H_A$ has rank $\omega$ for all $\lambda$, i.e. its
$\omega \times \omega$ minors have no common root.  Two facts close the gap:

* **Claim 8.** $\operatorname{rank}[H_A; H] = \operatorname{rank} H$ (i.e. $(5a)'$) is *equivalent* to the
  solvability of an explicit linear system $\mathcal M b = c$ in the entries of $b$; the system's
  consistency is decided by ranks of Gram-type matrices.  This is how the intermediate matrix $B$ is
  eliminated instead of being treated as a free variable.
* **Claim 11.** $(5b)'$ is equivalent to the solvability of the **Gram system** $Z^{\mathsf T} Z x = e_0$,
  where $Z$ is the *window matrix*: its columns index the $\omega \times \omega$ maximal minors of
  $\lambda H - H_A$, and its rows are their coefficient vectors.  "$e_0$ lies in the row space of $Z$"
  is the same as "the minors have no common complex root" — that is the Bézout content
  (Claims 9, 10), and Cauchy–Binet is what makes the Gram matrix computable from $Z$.

Claim 12 is the same statement for a full-column-rank pencil $\lambda X - G$, which is the form the
chart coordinates take.

*Lean:* `Q1Paper/PaperI/Claim8_ElemSymm.lean`, `Claim8_SumSquares.lean`, `Claim8_Disjunction.lean`,
`Claim11.lean`, `Claim11Final.lean`, `Claim12.lean`, `Window.lean`.

### Step 4 — make the certificate finite and rational

Charts.  A $\omega$-dimensional subspace of a $d_0$-dimensional space is described by a
$d_0 \times \omega$ matrix of full column rank, and one fixes $\omega$ pivot rows to the identity.
Enumerating those pivot sets (and the two degenerate cases $r = 0$ and $\omega = 0$ separately) turns
"there exists a subspace" into a finite disjunction of systems of polynomial equations.  Claim 14
supplies the chart data — bases of $K_0$, $T$, $S$, $W_0$ — with explicit size bounds.

Rationality.  Claim 13 gives rational bases of $\ker M$ and $\operatorname{row} M$; Claims 15–16 bound
every coefficient of every maximal minor and of the Gram entries in terms of the input bit length.
The point of this layer is not elegance: it is that a *real* algebraic feasibility question can be
decided with exact rational arithmetic at a known cost, with no numerical tolerance anywhere.

*Lean:* `Q1Paper/PaperI/Claim14Basis.lean`, `RationalBasis.lean`, `MinorCoeff.lean`,
`CompressedGram.lean`, `C16Gcd.lean`, `BezoutBounded.lean`.

### Step 5 — decide, and count

Putting Steps 3–4 together: for each chart, feasibility is a real-algebraic feasibility question in
$O(q^2)$ variables whose polynomials have explicitly bounded degree and bit length.  Feeding that to a
Renegar-type decision procedure gives the paper's bounds:

* **Theorem 1** (fixed order): time $\mathcal L^{O(q^2)}$ — the exponent depends only on the order;
* **Theorem 2** (fixed parameter): the parameter is $\ell = \operatorname{rank}(AN)$, and the bound is
  $(\ell+2)^{O(k_0 \ell^2)}(\beta+1)^{k_0}$, i.e. FPT in $\ell$;
* **Claim 16** (the zero-free-row case) and **Proposition 4** ($r = 0$) handle the two degenerate
  branches, where the general chart machinery would be vacuous;
* **Claim 19 / 21** are the bit-cost accounting for the exact-arithmetic layer.

**Theorem 5** closes the circle: the decision problem is equivalent to the existence of an encoding
witness, with no abstract hypothesis left — i.e. it is an $\exists\mathbb R$ problem.

*Lean:* `Q1Paper/PaperI/RenegarParams.lean`, `FptSpec.lean`, `Prop4.lean`, `T5Auto.lean`,
`ComplexityCounts.lean`, `ExactDiv.lean`.

## The one place where the formalisation says more than the paper

The paper states $(5b)$ over $\mathbb C$.  The Lean development originally stated it over the base
field (the reals) — call that `DEC` — and that is *strictly weaker*: complex implies real, but not
conversely.  So the chart equivalence was proved at the compressed level (`PhiPoint`, both
directions), and the paper's own specification was then stated separately as `complexDEC`, again with
both directions:

| direction | meaning | declaration |
|---|---|---|
| `PhiPoint` ⇒ `complexDEC` | a chart point is a witness | `ComplexSoundness.decComplex_of_phiPoint` |
| `complexDEC` ⇒ `PhiPoint` (for $\omega \ge 1$) | no witness is missed | `ComplexCompleteness.phiPoint_of_complexDEC` |

`DEC` is retained only as an auxiliary definition, linked by `complexDEC → DEC`.
The $\omega = 0$ branch is *not* covered by the completeness theorem and is a separate case in the
paper; see `docs/ALGORITHM_CORRECTNESS_MAP.md`.

## What is and is not machine-checked

| layer | status |
|---|---|
| Claims 1–16, Theorem 5, Proposition 4 ($r=0$), Claims 19/21 | kernel-checked in Lean |
| Theorems 1 and 2 | kernel-checked **conditionally**, relative to a declared backend cost model |
| The real-algebraic backend itself (Renegar) | **cited, not formalised** — no correctness field exists |
| An executable solver | **absent**; `verification/` holds a Python model used for differential testing only |

**One place where the coverage is finer than "Claim 11 is done".**  Claim 11 comes in two shapes.  The
Lean development proves the Gram certificate for the **injective** index family — an ordered choice of
$\omega$ rows and $\omega$ columns — and that is the form the statement is proved in.  The paper's
running text often indexes the same certificate by **subsets**, and the aggregation identity that
converts a sum over subsets into a sum over injective tuples (with the $(\omega!)^2$ multiplicity) is
*not* a single Lean theorem: what exists are its components — the fibre count
`sum_comp_eq_card_smul_sum` in `FibreSum.lean`, and the sign relation between the two families.  So
"Claim 11 is formalised" is true of the statement as written in the paper's displayed equivalence, and
the passage between the two index families is argued rather than compiled.  This is the same caveat the
README records; it is repeated here because a reader tracing the certificate will meet it.

"439 declarations pass the axiom audit" therefore means: 439 statements depend only on `propext`,
`Classical.choice` and `Quot.sound`.  It does **not** mean that every claim of the paper, every
algorithm, and its implementation are verified.
