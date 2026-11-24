#!/usr/bin/env python3
r"""decide.py -- Algorithm 1 of Paper I ("Deciding DEC(q) for a fixed order q"), end to end,
in exact rational arithmetic.

WHAT IS IMPLEMENTED
===================
    decide(A, C, L0, q)

executes Algorithm 1 of ``paper/paper_I_dec.tex`` (lines 940-969) literally:

  1. r0 = rows(L0), r = q - r0;   q < r0                       -> infeasible
  2. N  = basis of ker[C; CA];  h0 = L0 N;  g0 = L0 A N;
     D  = basis of (row[N AN])^perp
  3. r == 0                                                    -> the exact test of
                                                                  Section sec:zero (prop:zero),
                                                                  delegated to decide_r0
  4. h0 == 0 and g0 == 0                                       -> feasible   (W = 0 works)
  5. for omega = 1 .. min(q,k), for every J in C([k], omega):
        if Phi_{omega,J} of eq:phi has a real solution        -> feasible
     if every chart is refuted                                 -> infeasible
     otherwise                                                 -> unknown

Everything is ``fractions.Fraction``; no float takes part in any decision.

Step 5 is the only non-elementary step.  This module does **not** use a real-algebraic
oracle.  It decides each chart by an exact reduction (Claim A/B below, proved in the
comments) plus a *sound finite search*, and it distinguishes three outcomes per chart:

  * ``sat``      -- an explicit rational point of the chart system is found, converted into
                    (X, G, B, x), Phi is evaluated at it item by item, the induced free
                    block R is reconstructed and the resulting L is re-verified against
                    (5a)/(5b) by the *independent* implementation
                    ``audit_independent.cond_5a_orig`` / ``cond_5b_orig``.  ``sat`` is a
                    proof, not a guess.
  * ``unsat``    -- one of the exact refutations (R1)-(R6), or the exact decision (D1), below holds for the whole chart.
                    Again a proof, never "the solver found nothing".
  * ``unknown``  -- neither happened inside the search budget.  The chart is then *not*
                    refuted, and the failure to find a witness is not evidence of anything.

The top-level verdict is ``feasible`` / ``infeasible`` / ``unknown``; ``unknown`` carries
the list of undecided charts.  A wrong binary answer is never returned for a chart.

THE REDUCTION  (why the thing searched below is exactly Phi_{omega,J})
=====================================================================
Fix (omega, J), |J| = omega.  Phi_{omega,J} of eq:phi is

    exists X in R^{q x omega}, G in R^{q x omega}, B in R^{omega x k}, x in R^{2 omega}:

      (i)   rank X = omega                               [e_omega(X^T X) > 0]
      (ii)  M(X,G) b = c(X,G) is consistent              [b = non-pivot entries of B]
      (iii) X_i B = h0_i and G_i B = g0_i     (i <= r0)
      (iv)  D [(X_i B)^T; (G_i B)^T] = 0      (i > r0)    [the row pair lies in T]
      (v)   Z_Q^T Z_Q x = e0,  Q(lambda) = lambda X - G   [Claim 11, clm:gramQ]

with B_{:,J} = I_omega part of the pivot chart of Section sec:pivot.  Items (ii)-(iv) are
exactly "there is B with B_{:,J} = I_omega satisfying (iii) and (iv)": the pivot entries of
B are fixed to I_omega, the other entries are the vector b, and (ii) is the consistency of
the resulting linear system (this is the "rank consistency" of Claim 8, lem:rankcons).

Claim A (pair form).  Phi_{omega,J} is satisfiable iff there exist H, H_A in R^{q x k} with

    (L1) H_i = h0_i and (H_A)_i = g0_i for i <= r0                (prescribed rows)
    (L2) (H_i, (H_A)_i) in T for i > r0                           (attainable pairs)
    (L3) rank H = omega and rank H_{:,J} = omega                  (the chart: J is a basis of
                                                                   the column space of H)
    (L4) row H_A contained in row H                               (= (5a), Claim 2(i))
    (L5) rank(lambda H - H_A) = omega for every lambda in C       (= (5b), Claim 2(iii))

Proof.  (=>)  Given X, G, B, x put H = X B, H_A = G B.  (iii) is (L1) and (iv) is (L2).
Since B_{:,J} = I_omega, H_{:,J} = X, so rank H_{:,J} = rank X = omega; and rank H =
rank(X B) = rank X = omega because B has full row rank omega.  (L4): X has a left inverse
X_L (rank X = omega), so H_A = G B = (G X_L) X B = (G X_L) H.  (L5): B has a right inverse,
so rank(lambda H - H_A) = rank((lambda X - G) B) = rank(lambda X - G) = omega by (v) and
clm:gramQ.
(<=)  Given H, H_A put X = H_{:,J} (full column rank omega) and pick X_L with X_L X =
I_omega; set B = X_L H.  Then B_{:,J} = X_L H_{:,J} = I_omega, and X B = H_{:,J} X_L H = H
because rank H = rank H_{:,J} means every column of H is a linear combination of the columns
in J.  Hence X_i B = H_i = h0_i, and for G: by (L4) each row g_i of H_A lies in
row H = row B, and G_i -> G_i B is injective on row vectors of length omega (B has full row
rank), so a unique G_i with G_i B = g_i exists for every i.  (ii) holds with the
corresponding b, (iii)/(iv) hold by construction, and (v) follows from (L5) by clm:gramQ
(the window matrix depends on X and G only).  QED.

Claim B (chart coordinates).  Let U = row H (dimension omega).  Then (L1)-(L5) are
equivalent to

    (C1) U is an omega-dimensional subspace of R^k with U_pres subset U, where
         U_pres = span{h0_i, g0_i : i <= r0};
    (C2) the coordinate projection pi_J : U -> R^omega is injective;
    (C3) the free row pairs p_i = (H_i, (H_A)_i) (i > r0) lie in  T ∩ (U x U);
    (C4) rank(lambda H - H_A) = omega for every lambda, where H, H_A are the prescribed
         rows followed by the pairs p_i;
    plus rank H = omega (which with (C1),(C2) and (C4) is automatic).

Proof.  (L1) says h0_i ∩row H = U; (L4) and (5b) at lambda = 0 give rank H_A = omega =
dim U, so row H_A = U, hence g0_i ∩U: that is U_pres subset U.  (L3) is exactly the
injectivity of pi_J on U (the rank of H_{:,J} is the rank of the coordinate restriction
U -> R^omega).  (L2) plus H_i, (H_A)_i ∩U is (C3).  Conversely (C1),(C2) determine a
unique B -- the omega x k matrix with row space U and B_{:,J} = I_omega -- and X = H_{:,J},
so the construction above inverts Claim A.  QED.

Claims A and B are the reason the search below runs over (U, free pairs) instead of over
(X, G, B, x) directly: in these coordinates the constraints (L1)-(L4) are *linear* (or open
rank conditions), only (L5) is genuinely nonlinear, and the two conditions that make the
problem hard -- (5a) as an inclusion and "rank H <= omega" -- hold by construction.

WHAT THE SEARCH DOES
====================
For each omega, the module enumerates candidate subspaces U = U_pres + span(v_1,...,v_d)
with d = omega - dim U_pres, the v_i ranging over a fixed deterministic list of small
integer vectors (in lexicographic order), and for each U

  * checks (C1),(C2) exactly and computes the unique B of Claim B for each admissible J;
  * computes a basis of T ∩ (U x U) exactly (via the annihilator of U) and enumerates the
    free row pairs over a deterministic list of small combinations of that basis;
  * tests (L5) exactly on the resulting pencil through the (R0) linear system of
    Claim lem:zero (``decide_r0.build_system`` / ``solve_exact``), cross-checked against the
    gcd of the maximal minors (``decide_r0.gcd_minor_test``) whenever that is affordable;
  * on success, re-derives (X, G, B), evaluates Phi of eq:phi *literally* (all five items,
    including the Gram/window certificate (v) of Claim 11 built from the maximal minors of
    lambda X - G), reconstructs the free block R from the pairs and verifies L=[L0;R]
    against ``cond_5a_orig``/``cond_5b_orig``.

If a point passes, every admissible J of its U is a satisfiable chart, because the point
satisfies (L1)-(L5) and Claim A turns it into a Phi-solution chart by chart.

REFUTATIONS (what ``unsat`` means)
==================================
  (R1) omega < dim U_pres.  By (C1) every chart point has dim U = omega >= dim U_pres.
  (R2) omega > ell := rank(AN).  At a chart point row H_A = U (proof of Claim B), and
       row H_A = row(L A N) is contained in row(A N), so omega <= ell.
  (R3) a rational lambda_0 such that every maximal omega-minor of
       lambda_0 H - H_A vanishes identically on the whole linear family
           F = {(H,H_A) : (L1) and (L2)}.
       Then every point of F -- hence every chart point -- has
       rank(lambda_0 H - H_A) < omega and violates (L5).
       The identity test is exact: H and H_A are affine functions of the parameters t of F,
       every omega-minor is a polynomial of degree <= omega in t, and it is expanded
       symbolically (``_MPoly``) and compared with zero as a polynomial, not sampled.
  (R4) the same fixed-lambda_0 test as (R3), but on the *chart's own* affine family, used
       when the chart's U is forced: this happens exactly when omega = dim U_pres (then
       U = U_pres) or omega = k (then U = R^k).  The free pairs then range over the linear
       space T ∩ (U x U), and H, H_A are affine in those coordinates.
  (R5) omega = q.  Then X is a square omega x omega matrix, so
       rank(lambda X - G) = rank(lambda I - G X^{-1}) and the square matrix G X^{-1} has a
       complex eigenvalue, where the rank drops.  Equivalently dim W <= q = omega, while a
       feasible W with omega > 0 satisfies dim W >= omega + 1 (Claim 6, lem:struct).
  (R6) omega + 1 > dim T, or omega + 1 > dim W0 + r.  A feasible W has dim W >= omega + 1
       (Claim 6), while W <= T and dim(W/W0) <= r give dim W <= dim T and
       dim W <= dim W0 + r.
  (D1) not a refutation but a *complete* decision of a whole family of charts: if
       dim T = omega + 1 then W <= T and dim W >= omega + 1 force W = T (when it is
       reachable, dim T - dim W0 <= r).  Conditions (5a) and (5b) depend on W alone
       (Claim lem:W-conditions), so the chart is decided exactly by testing them on T:
       satisfiable with an explicit pair list if they hold and some pi_J is injective on
       U = pi_1(T), and unsatisfiable otherwise.

(R1)-(R6) and (D1) cover what this module decides; they are not complete.  In particular a
chart can be unsatisfiable because the pencil of *every* chart point drops rank at a lambda
that depends on the point (think of the family (x,g) = (1,t) for q = omega = 1: the drop is
at lambda = t).  Such a chart is reported ``unknown`` -- never ``infeasible``.

BOUNDARY / HONESTY NOTES
========================
* ``feasible`` for r > 0 is always accompanied by the matrix L and re-verified; for r = 0
  the verdict is decide_r0's (itself certified by an S-family or a Farkas vector).  One
  degenerate r = 0 case is handled here instead of in decide_r0: when h0 = g0 = 0
  (omega = 0) prop:zero Step 2 accepts, while decide_r0.compress_r0 returns None and
  decide_r0 therefore answers False.  Step 3 below answers ``feasible`` there and says so;
  L = L0 is still re-verified against cond_5a_orig/cond_5b_orig.
* The search is bounded (number of candidate U's, pairs, and (L5) tests).  When the budget
  is exhausted the chart is ``unknown``; ``_search_omega`` reports the number of points
  examined so the report can state the budget.
* This file does not modify decide_r0.py or audit_independent.py; it only imports them.

USAGE
=====
    python decide.py                 # built-in demo: one r > 0 feasible, one r > 0 infeasible
    python decide.py instance.json   # {"A": .., "C": .., "L0": .., "q": ..}
Exit status 0 on the demo when both verdicts are as expected, 2 on malformed input.
"""

from __future__ import annotations

import itertools
import json
import sys
from fractions import Fraction as Fr

import audit_independent as ai
import decide_r0 as dec0

FR0 = Fr(0)
FR1 = Fr(1)


# ====================================================================== exact helpers

def zeros(m, n):
    return [[FR0] * n for _ in range(m)]


def dim_rows(M):
    return len(M)


def dim_cols(M):
    return len(M[0]) if M else 0


def is_zero_mat(M):
    return all(v == 0 for row in M for v in row)


def basis_of_rows(vectors):
    """A row basis (rref, exact) of the span of ``vectors``; [] for the zero space."""
    rows = [list(v) for v in vectors if any(x != 0 for x in v)]
    if not rows:
        return []
    return ai.row_basis(rows)


def submatrix(M, rows, cols):
    return [[M[i][j] for j in cols] for i in rows]


def solve_row_combination(B, target):
    """Row vector y with y B = target, or None if there is none.  B is a x k."""
    a = len(B)
    k = dim_cols(B)
    if k == 0:
        return [FR0] * a
    M = [[B[j][c] for j in range(a)] for c in range(k)]
    kind, payload = dec0.solve_exact(M, [Fr(v) for v in target])
    return payload if kind == "yes" else None


def cond5b_pencil(X, G, omega, cross_check=True):
    """(5b) for Q(lambda) = lambda X - G: rank omega at every complex lambda.

    Uses the (R0) linear system of Claim lem:zero (decide_r0.build_system), i.e. the
    paper's own polynomial-size test, and cross-checks it against the gcd of the maximal
    minors whenever the number of minors is small enough.  A disagreement is an assertion
    failure (a bug), never a verdict.
    """
    if omega == 0:
        return all(v == 0 for row in X for v in row) and all(v == 0 for row in G for v in row)
    M, b = dec0.build_system(X, G, omega)
    kind, payload = dec0.solve_exact(M, b)
    if kind == "yes":
        assert dec0.check_solution(M, b, payload), "(R0) solver returned a non-solution"
        verdict = True
    else:
        assert dec0.check_farkas(M, b, payload), "returned vector is not a Farkas certificate"
        verdict = False
    q = len(X)
    if cross_check and omega <= 3 and q <= 8:
        ref = dec0.gcd_minor_test(X, G)
        assert ref == verdict, ("(R0) linear system and gcd-of-minors test disagree "
                                f"(system={verdict}, gcd={ref})")
    return verdict


def pencil_constant_rank(H, H_A, omega):
    """Direct test of (L5): gcd of the maximal omega-minors of lambda H - H_A is constant.

    This is the definition used in the paper (Claim compression(iii)); it works for the
    rectangular q x k pencil.  Only used on witnesses (cross-check of cond5b_pencil).
    """
    if omega == 0:
        return is_zero_mat(H) and is_zero_mat(H_A)
    q, k = len(H), dim_cols(H)
    if omega > q or omega > k:
        return False
    rows = [[ai.psub([FR0, H[i][j]], [H_A[i][j]]) for j in range(k)] for i in range(q)]
    g = None
    for rs in itertools.combinations(range(q), omega):
        for cs in itertools.combinations(range(k), omega):
            minor = ai._det_poly([[rows[i][j] for j in cs] for i in rs])
            if ai.pzero(minor):
                continue
            g = minor if g is None else ai.pgcd(g, minor)
            if g is not None and ai.pconst_nonzero(g):
                return True
    if g is None:
        return False
    return ai.pconst_nonzero(g)


def gram_window(X, G):
    r"""The window matrix Z_Q of Claim 11 (clm:gramQ / prop:gram) for Q = lambda X - G.

    Row (I, j) (I an omega-subset of the rows of Q, 0 <= j < omega) is
    coef(lambda^j f_I) in the basis 1, lambda, ..., lambda^(2 omega - 1), i.e.
    Z[(I,j), t] = c_{I, t-j}, where f_I = sum_a c_{I,a} lambda^a = det(lambda X_I - G_I).
    """
    q, om = len(X), dim_cols(X)
    cols_t = 2 * om
    rows = [[ai.psub([FR0, X[i][j]], [G[i][j]]) for j in range(om)] for i in range(q)]
    Z = []
    for I in itertools.combinations(range(q), om):
        f = ai._det_poly([[rows[i][j] for j in range(om)] for i in I])
        for j in range(om):
            row = [FR0] * cols_t
            for t in range(cols_t):
                a = t - j
                if 0 <= a < len(f):
                    row[t] = f[a]
            Z.append(row)
    return Z


def gram_certificate(X, G):
    """The x of Phi item (v): Z^T Z x = e0, or None.  Exact, over Q (hence over R)."""
    om = dim_cols(X)
    if om == 0:
        return [FR0]
    Z = gram_window(X, G)
    ZtZ = ai.mul(ai.tr(Z), Z)
    e0 = [FR1] + [FR0] * (2 * om - 1)
    kind, payload = dec0.solve_exact(ZtZ, e0)
    return payload if kind == "yes" else None


# ====================================================================== sparse polynomials

class _MPoly:
    """Sparse multivariate polynomial over Q: {exponent tuple: Fraction}."""

    __slots__ = ("c",)

    def __init__(self, coeffs=None):
        self.c = {e: Fr(v) for e, v in (coeffs or {}).items() if v != 0}

    @staticmethod
    def const(value, m):
        value = Fr(value)
        return _MPoly({(0,) * m: value} if value != 0 else {})

    @staticmethod
    def affine(const, coefs):
        m = len(coefs)
        d = {}
        if const != 0:
            d[(0,) * m] = Fr(const)
        for i, a in enumerate(coefs):
            if a != 0:
                e = [0] * m
                e[i] = 1
                d[tuple(e)] = Fr(a)
        return _MPoly(d)

    def is_zero(self):
        return not self.c

    def scale(self, a):
        a = Fr(a)
        return _MPoly({e: v * a for e, v in self.c.items()} if a != 0 else {})

    def __add__(self, other):
        d = dict(self.c)
        for e, v in other.c.items():
            d[e] = d.get(e, FR0) + v
        return _MPoly(d)

    def __neg__(self):
        return _MPoly({e: -v for e, v in self.c.items()})

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        d = {}
        for e1, v1 in self.c.items():
            for e2, v2 in other.c.items():
                e = tuple(a + b for a, b in zip(e1, e2))
                d[e] = d.get(e, FR0) + v1 * v2
        return _MPoly(d)


def _det_mpoly(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    acc = _MPoly()
    for j in range(n):
        if M[0][j].is_zero():
            continue
        minor = [[M[i][c] for c in range(n) if c != j] for i in range(1, n)]
        term = M[0][j] * _det_mpoly(minor)
        acc = acc + term if j % 2 == 0 else acc - term
    return acc


# ====================================================================== the instance context

class Context:
    """The instance after step 2 of Algorithm 1, with all invariants asserted."""

    def __init__(self, A, C, L0, q):
        n = len(A)
        assert n > 0 and all(len(row) == n for row in A), "A must be square"
        p, r0 = len(C), len(L0)
        assert p >= 1, "C must have at least one row"
        assert all(len(row) == n for row in C), "C must have n columns"
        assert all(len(row) == n for row in L0), "L0 must have n columns"
        assert q >= 0, "q must be a nonnegative order"
        self.A, self.C, self.L0, self.q = A, C, L0, q
        self.n, self.p, self.r0, self.r = n, p, r0, q - r0

        self.CA = ai.mul(C, A)                                   # p x n
        self.P0 = ai.vstack([C, self.CA])                        # 2p x n
        rk_P0 = ai.rank(self.P0)
        Ncols = ai.nullspace(self.P0)                            # exact, residual asserted
        self.k = len(Ncols)
        assert rk_P0 + self.k == n, "rank-nullity failed for [C; CA]"
        self.N = [[Ncols[j][i] for j in range(self.k)] for i in range(n)]   # n x k
        if self.k:
            assert all(v == 0 for row in ai.mul(self.P0, self.N) for v in row)
        self.AN = ai.mul(A, self.N)                              # n x k
        self.ell = ai.rank(self.AN)                              # dim row(A N)

        self.h0 = ai.mul(L0, self.N)                             # r0 x k
        self.g0 = ai.mul(L0, self.AN)                            # r0 x k
        assert len(self.h0) == r0 and dim_cols(self.h0) == self.k
        assert len(self.g0) == r0 and dim_cols(self.g0) == self.k

        M2 = [[self.N[i][j] for j in range(self.k)]
              + [self.AN[i][j] for j in range(self.k)] for i in range(n)]     # n x 2k
        self.Tbasis = ai.row_basis(M2) if self.k else []         # rows of T = row[N AN]
        self.d0 = len(self.Tbasis)
        if self.d0:
            assert all(len(r) == 2 * self.k for r in self.Tbasis)
        self.D = ai.nullspace(self.Tbasis) if self.d0 else \
            [[FR1 if i == j else FR0 for j in range(2 * self.k)] for i in range(2 * self.k)]
        assert len(self.D) == 2 * self.k - self.d0, "dim (row[N AN])^perp != 2k - d0"
        # the prescribed pairs really are attainable: D[(h0_i)^T; (g0_i)^T] = 0
        for i in range(r0):
            pair = [self.h0[i][c] for c in range(self.k)] + [self.g0[i][c] for c in range(self.k)]
            for drow in self.D:
                assert sum(drow[c] * pair[c] for c in range(2 * self.k)) == 0, \
                    "a prescribed row pair is not in T = row[N AN]"

        self.Upres = basis_of_rows(
            [[self.h0[i][c] for c in range(self.k)] for i in range(r0)]
            + [[self.g0[i][c] for c in range(self.k)] for i in range(r0)])
        # W_0 = row(L0 M) = row of the prescribed row pairs (h0_i, g0_i), dim W_0 = s_0
        self.W0mat = [[self.h0[i][c] for c in range(self.k)]
                      + [self.g0[i][c] for c in range(self.k)] for i in range(r0)]
        self.W0dim = ai.rank(self.W0mat) if r0 else 0
        assert self.W0dim <= min(self.d0, r0), "dim W0 must be <= dim T and <= r0"
        self.F = _Family(self)                                   # affine family (L1)+(L2)

    # ---- printing discipline: shapes / ranks / dimensions before any verdict
    def describe(self):
        print(f"[decide] n={self.n} p={self.p} r0={self.r0} q={self.q} r={self.r}")
        print(f"[decide] rank[C;CA]={self.n - self.k} (= n-k), k=dim ker[C;CA]={self.k}")
        print(f"[decide] h0: {self.r0}x{self.k} rank={ai.rank(self.h0) if self.k else 0};  "
              f"g0: {self.r0}x{self.k} rank={ai.rank(self.g0) if self.k else 0}")
        print(f"[decide] T=row[N AN]: d0={self.d0}; dim (row[N AN])^perp={len(self.D)} "
              f"(= 2k-d0 = {2 * self.k - self.d0})")
        print(f"[decide] ell=rank(AN)={self.ell}; dim U_pres=span{{h0_i,g0_i}}={len(self.Upres)}")
        print(f"[decide] family F=(L1)+(L2): {2 * self.q * self.k} unknowns, "
              f"{len(self.F.gens)} parameters")


class _Family:
    r"""The affine family F = {(H,H_A) : (L1) prescribed rows and (L2) free pairs in T}.

    Parametrised as base + sum_l t_l gen_l, so every entry of H and H_A is an affine
    function of t; ``entry`` returns it as an _MPoly.
    """

    def __init__(self, ctx):
        q, k, r0 = ctx.q, ctx.k, ctx.r0
        nvar = 2 * q * k
        eqs, rhs = [], []
        for i in range(r0):
            for c in range(k):
                e = [FR0] * nvar
                e[i * k + c] = FR1
                eqs.append(e)
                rhs.append(Fr(ctx.h0[i][c]))
                e = [FR0] * nvar
                e[q * k + i * k + c] = FR1
                eqs.append(e)
                rhs.append(Fr(ctx.g0[i][c]))
        for i in range(r0, q):
            for drow in ctx.D:
                e = [FR0] * nvar
                for c in range(k):
                    e[i * k + c] = drow[c]
                    e[q * k + i * k + c] = drow[k + c]
                eqs.append(e)
                rhs.append(FR0)
        if eqs:
            aug = [list(eqs[i]) + [rhs[i]] for i in range(len(eqs))]
            R, piv = ai.rref(aug)
            for i in range(len(R)):
                if all(v == 0 for v in R[i][:nvar]) and R[i][nvar] != 0:
                    raise AssertionError("the chart family F is empty (should not happen)")
            base = [FR0] * nvar
            for i, c in enumerate(piv):
                base[c] = R[i][nvar]
            gens = ai.nullspace(eqs)
        else:                                    # no equations: the whole space
            base = [FR0] * nvar
            gens = [[FR1 if t == j else FR0 for t in range(nvar)] for j in range(nvar)]
        self.base, self.gens, self.m = base, gens, len(gens)
        self.q, self.k = q, k

    def entry(self, index):
        return _MPoly.affine(self.base[index], [g[index] for g in self.gens])

    def H(self, i, j):
        return self.entry(i * self.k + j)

    def HA(self, i, j):
        return self.entry(self.q * self.k + i * self.k + j)


# ====================================================================== results

class ChartOutcome:
    """Step-5 outcome for one chart (omega, J)."""

    __slots__ = ("omega", "J", "verdict", "certificate", "witness", "n_points", "budget_hit")

    def __init__(self, omega, J, verdict, certificate="", witness=None,
                 n_points=0, budget_hit=False):
        self.omega, self.J, self.verdict = omega, tuple(J), verdict
        self.certificate, self.witness = certificate, witness
        self.n_points, self.budget_hit = n_points, budget_hit

    def __repr__(self):
        return (f"ChartOutcome(omega={self.omega}, J={list(self.J)}, {self.verdict}"
                f"{', ' + self.certificate if self.certificate else ''})")


class Decision:
    """The three-valued answer of Algorithm 1, with everything that backs it."""

    __slots__ = ("verdict", "L", "charts", "reason", "undecided", "context")

    def __init__(self, verdict, L=None, charts=None, reason="", undecided=None, context=None):
        self.verdict = verdict
        self.L = L
        self.charts = charts or []
        self.reason = reason
        self.undecided = undecided or []
        self.context = context

    def __repr__(self):
        tag = self.verdict.upper()
        extra = ""
        if self.L is not None:
            extra = f", L {len(self.L)}x{dim_cols(self.L)}"
        if self.undecided:
            extra += f", {len(self.undecided)} undecided chart(s)"
        return f"Decision({tag}{extra}: {self.reason})"


# ====================================================================== step 5: one chart

def _chart_B(Ub, J):
    r"""The unique B with row space U and B_{:,J} = I_omega (Claim B): B = U_J^{-1} U."""
    om = len(Ub)
    UJ = [[Ub[i][j] for j in J] for i in range(om)]
    UJinv = ai.inv(UJ)                       # asserts nonsingularity: pi_J injective
    B = ai.mul(UJinv, Ub)                    # omega x k
    assert dim_cols(B) == dim_cols(Ub)
    assert [[B[i][J[t]] for t in range(om)] for i in range(om)] == \
           [[FR1 if i == t else FR0 for t in range(om)] for i in range(om)], \
           "B_{:,J} != I_omega"
    return B


def _T_box_basis(ctx, Ub):
    """Basis (length-2k vectors) of T ∩ (U x U), exactly.

    v = c . Tbasis is in U x U iff both its blocks are annihilated by a basis of U^perp;
    that gives linear equations on c in R^{d0}, and the nullspace of those equations is
    the coordinate space of T ∩ (U x U).
    """
    k = ctx.k
    if ctx.d0 == 0:
        return []
    if Ub:
        Uperp = ai.nullspace([list(r) for r in Ub])
    else:
        Uperp = [[FR1 if i == j else FR0 for j in range(k)] for i in range(k)]
    eqs = []
    for pv in Uperp:
        row1 = [sum(pv[j] * ctx.Tbasis[t][j] for j in range(k)) for t in range(ctx.d0)]
        row2 = [sum(pv[j] * ctx.Tbasis[t][k + j] for j in range(k)) for t in range(ctx.d0)]
        eqs.append(row1)
        eqs.append(row2)
    if eqs:
        cbasis = ai.nullspace(eqs)
    else:
        cbasis = [[FR1 if t == j else FR0 for t in range(ctx.d0)] for j in range(ctx.d0)]
    out = []
    for c in cbasis:
        v = [sum(c[t] * ctx.Tbasis[t][col] for t in range(ctx.d0)) for col in range(2 * k)]
        out.append(v)
    return out


def _pair_candidates(Vb, limit=7):
    """Deterministic list of small elements of T ∩ (U x U), zero first."""
    k = len(Vb[0]) // 2 if Vb else 0
    out = [(tuple([FR0] * k), tuple([FR0] * k))]
    if not Vb:
        return out

    def mk(v):
        return (tuple(v[:k]), tuple(v[k:]))

    for v in Vb:
        out.append(mk(v))
        out.append(mk([-x for x in v]))
    for a, b in itertools.combinations(Vb, 2):
        out.append(mk([x + y for x, y in zip(a, b)]))
        out.append(mk([x - y for x, y in zip(a, b)]))
    return out[:limit]


def _assignments(cands, r, cap):
    """All r-tuples of pair candidates, ordered by the number of nonzero rows."""
    zero = cands[0]
    nz = cands[1:]
    out = []
    for w in range(0, r + 1):
        for pos in itertools.combinations(range(r), w):
            for combo in itertools.product(nz, repeat=w):
                assign = [zero] * r
                for p, c in zip(pos, combo):
                    assign[p] = c
                out.append(tuple(assign))
                if len(out) >= cap:
                    return out
    return out


def _small_vectors(k, limit):
    """Deterministic list of small integer vectors in Q^k (first nonzero entry = 1)."""
    out = []
    for w in range(1, k + 1):
        for pos in itertools.combinations(range(k), w):
            for rest in itertools.product((-1, 0, 1), repeat=w - 1):
                v = [FR0] * k
                v[pos[0]] = FR1
                for p, val in zip(pos[1:], rest):
                    v[p] = Fr(val)
                out.append(v)
                if len(out) >= limit:
                    return out
    return out


class Obstruction:
    __slots__ = ("kind", "detail")

    def __init__(self, kind, detail):
        self.kind, self.detail = kind, detail

    def __repr__(self):
        return f"Obstruction({self.kind}: {self.detail})"


def _forced_U(ctx, omega):
    """The unique U of the chart when it is forced, else None.

    The chart's U ranges over the (omega - dim U_pres)-dimensional Grassmannian of
    extensions of U_pres, so it is a single point exactly when omega = dim U_pres (U =
    U_pres) or omega = k (U = R^k).
    """
    s = len(ctx.Upres)
    if omega == s:
        return [list(r) for r in ctx.Upres]
    if omega == ctx.k:
        return [[FR1 if i == j else FR0 for j in range(ctx.k)] for i in range(ctx.k)]
    return None


def _chart_family_obstruction(ctx, omega, lam_candidates):
    """(R4): refute a chart whose U is forced, at a fixed lambda_0, on its own family.

    With U forced to U*, the chart points are (H,H_A) built from the prescribed rows and
    free pairs in V = T ∩(U* x U*).  H and H_A are affine in the coordinates of the r free
    pairs, so "rank(lambda_0 H - H_A) < omega identically" is again an exact polynomial
    identity test.  Refuting the larger affine family is sound for the chart.
    """
    U = _forced_U(ctx, omega)
    if U is None or len(basis_of_rows(U)) != omega:
        return None
    Vb = _T_box_basis(ctx, U)
    if omega > 4 or ctx.r * len(Vb) > 24 or \
            _binom(ctx.q, omega) * _binom(ctx.k, omega) > 2000:
        return None
    npar = ctx.r * len(Vb)
    nfree = len(Vb)
    Hforms, HAforms = [], []
    for i in range(ctx.q):
        if i < ctx.r0:
            Hforms.append([_MPoly.const(ctx.h0[i][c], npar) for c in range(ctx.k)])
            HAforms.append([_MPoly.const(ctx.g0[i][c], npar) for c in range(ctx.k)])
        else:
            j = i - ctx.r0
            hrow, harow = [], []
            for c in range(ctx.k):
                coefs = [FR0] * npar
                for l in range(nfree):
                    coefs[j * nfree + l] = Vb[l][c]
                hrow.append(_MPoly.affine(FR0, coefs))
                coefs = [FR0] * npar
                for l in range(nfree):
                    coefs[j * nfree + l] = Vb[l][ctx.k + c]
                harow.append(_MPoly.affine(FR0, coefs))
            Hforms.append(hrow)
            HAforms.append(harow)
    for lam0 in lam_candidates:
        lam0 = Fr(lam0)
        Mat = [[Hforms[i][j].scale(lam0) - HAforms[i][j] for j in range(ctx.k)]
               for i in range(ctx.q)]
        all_zero = True
        for rs in itertools.combinations(range(ctx.q), omega):
            for cs in itertools.combinations(range(ctx.k), omega):
                if not _det_mpoly([[Mat[i][j] for j in cs] for i in rs]).is_zero():
                    all_zero = False
                    break
            if not all_zero:
                break
        if all_zero:
            return Obstruction(
                "R4", f"U is forced and rank(lambda0 H - H_A) < {omega} on the whole chart "
                      f"family at lambda0={lam0}")
    return None


def _projection(Tbasis, k, first):
    return basis_of_rows([list(b[:k]) if first else list(b[k:]) for b in Tbasis])


class ForcedW:
    """Complete analysis of the charts with dim T = omega + 1, where W = T is forced.

    A feasible W has dim W >= omega + 1 (Claim 6).  If dim T = omega + 1 then W <= T
    forces W = T, so (5a) and (5b) -- which by Claim lem:W-conditions depend on W alone --
    are fixed, and the chart is decided exactly (no search, no unknown).
    """

    __slots__ = ("omega", "reachable", "U", "admissible_J", "ok5a", "ok5b", "sat", "pairs")

    def __init__(self, ctx, omega):
        self.omega = omega
        t = ctx.d0 - ctx.W0dim
        self.reachable = t <= ctx.r          # dim(W/W0) = dim T - dim W0 <= r
        self.U = _projection(ctx.Tbasis, ctx.k, True)          # pi_1(T) = row H
        U2 = _projection(ctx.Tbasis, ctx.k, False)             # pi_2(T)
        self.admissible_J = [
            J for J in itertools.combinations(range(ctx.k), omega)
            if ai.rank([[self.U[i][j] for j in J] for i in range(len(self.U))]) == omega]
        self.ok5a = ai.rank([list(r) for r in self.U] + [list(r) for r in U2]) == len(self.U)
        H_T = [list(b[:ctx.k]) for b in ctx.Tbasis]
        HA_T = [list(b[ctx.k:]) for b in ctx.Tbasis]
        self.ok5b = (len(self.U) == omega) and pencil_constant_rank(H_T, HA_T, omega)
        # the pairs that extend W0 to T (t of them, t <= r), the rest of the free rows 0
        chosen = []
        cur = [list(r) for r in ctx.W0mat]
        cur_rank = ai.rank(cur) if cur else 0
        for b in ctx.Tbasis:
            if cur_rank == ctx.d0:
                break
            trial = cur + [list(b)]
            rk = ai.rank(trial)
            if rk > cur_rank:
                chosen.append(list(b))
                cur, cur_rank = trial, rk
        assert cur_rank == ctx.d0, "failed to extend W0 to T"
        assert len(chosen) == t
        self.pairs = tuple((tuple(b[:ctx.k]), tuple(b[ctx.k:])) for b in chosen) + \
            tuple((tuple([FR0] * ctx.k), tuple([FR0] * ctx.k)) for _ in range(ctx.r - t))
        self.sat = (self.reachable and len(self.U) == omega and self.ok5a and self.ok5b
                    and bool(self.admissible_J))

    def why_unsat(self, ctx):
        if not self.reachable:
            return (f"dim T - dim W0 = {ctx.d0 - ctx.W0dim} > r = {ctx.r}: "
                    f"W = T is out of reach")
        if len(self.U) != self.omega:
            return f"dim pi_1(T) = {len(self.U)} != omega = {self.omega}"
        if not self.ok5a:
            return "pi_2(T) is not contained in pi_1(T), so (L4)/(5a) fails on W = T"
        if not self.ok5b:
            return "the pencil of W = T loses rank at some lambda, so (L5)/(5b) fails"
        return "no admissible J"


def _forced_W_analysis(ctx, omega):
    if omega + 1 != ctx.d0 or ctx.d0 == 0:
        return None
    return ForcedW(ctx, omega)


def _rank_deficient_at(Hforms, HAforms, omega, lam0, q, k):
    """True iff every maximal omega-minor of lambda_0 H - H_A vanishes identically."""
    Mat = [[Hforms[i][j].scale(lam0) - HAforms[i][j] for j in range(k)] for i in range(q)]
    for rs in itertools.combinations(range(q), omega):
        for cs in itertools.combinations(range(k), omega):
            if not _det_mpoly([[Mat[i][j] for j in cs] for i in rs]).is_zero():
                return False
    return True


def chart_obstruction(ctx, omega, lam_candidates):
    """(R1)-(R4): an exact refutation of every chart with this omega, or None."""
    if omega < len(ctx.Upres):
        return Obstruction("R1", f"omega={omega} < dim U_pres={len(ctx.Upres)} "
                                 f"(U must contain span{{h0_i,g0_i}})")
    if omega > ctx.ell:
        return Obstruction("R2", f"omega={omega} > ell=rank(AN)={ctx.ell} "
                                 f"(row H_A = U is contained in row(AN))")
    if omega > ctx.q or omega > ctx.k:
        return Obstruction("bounds", f"omega={omega} > min(q,k)")
    if omega + 1 > ctx.d0 or omega + 1 > ctx.W0dim + ctx.r:
        # (R6): a feasible W with omega > 0 has dim W >= omega+1 (Claim 6, lem:struct),
        # while W <= T and dim(W/W0) <= r give dim W <= dim T and dim W <= dim W0 + r.
        return Obstruction("R6", f"omega+1={omega + 1} exceeds dim T={ctx.d0} or "
                                 f"dim W0+r={ctx.W0dim + ctx.r} (Claim 6: omega+1 <= dim W)")
    if omega == ctx.q:
        # (R5): dim W <= q = omega, but a feasible W with omega > 0 has dim W >= omega+1
        # (Claim 6, lem:struct).  Equivalently: X is q x omega = omega x omega and
        # invertible, so rank(lambda X - G) = rank(lambda I - G X^{-1}) and the square
        # matrix G X^{-1} has a complex eigenvalue lambda_0, where the rank drops.
        return Obstruction("R5", f"omega={omega}=q: a square pencil "
                                 f"lambda I - G X^-1 always loses rank at an eigenvalue "
                                 f"(equivalently dim W <= q = omega contradicts "
                                 f"omega+1 <= dim W, Claim 6)")
    # (R3): (L5) fails at a fixed lambda_0 on the whole family F
    F = ctx.F
    if not (omega > 4 or F.m > 24 or _binom(ctx.q, omega) * _binom(ctx.k, omega) > 2000):
        Hf = [[F.H(i, j) for j in range(ctx.k)] for i in range(ctx.q)]
        HAf = [[F.HA(i, j) for j in range(ctx.k)] for i in range(ctx.q)]
        for lam0 in lam_candidates:
            if _rank_deficient_at(Hf, HAf, omega, Fr(lam0), ctx.q, ctx.k):
                return Obstruction(
                    "R3", f"rank(lambda0 H - H_A) < {omega} for every (H,H_A) in F at "
                          f"lambda0={lam0}; hence (L5) fails on all of F")
    # (R4): same test on the chart's own family when its U is forced
    obs4 = _chart_family_obstruction(ctx, omega, lam_candidates)
    if obs4 is not None:
        return obs4
    return None


def _binom(n, r):
    if r < 0 or r > n:
        return 0
    out = 1
    for i in range(r):
        out = out * (n - i) // (i + 1)
    return out


class _SatPoint:
    """A point of the chart system, in the (H,H_A) coordinates of Claim A."""

    __slots__ = ("omega", "U", "pairs", "H", "H_A", "admissible_J")

    def __init__(self, omega, U, pairs, H, H_A, admissible_J):
        self.omega, self.U, self.pairs = omega, U, pairs
        self.H, self.H_A = H, H_A
        self.admissible_J = admissible_J


def _search_omega(ctx, omega, opts):
    """Sound finite search for a point of the chart system with this omega.

    Returns (points, budget_hit): the satisfying points found (with their admissible J
    sets) and whether the search budget was exhausted.  Finding a point is a proof that
    the corresponding charts are satisfiable; finding nothing proves nothing.
    """
    points = []
    s = len(ctx.Upres)
    if omega < s or omega > ctx.ell or omega > ctx.q or omega > ctx.k:
        return points, False
    d = omega - s
    vecs = _small_vectors(ctx.k, opts["u_vector_limit"])
    if d == 0:
        combos = [()]
    else:
        combos = itertools.combinations(vecs, d)
    budget = opts["search_budget"]
    used = 0
    budget_hit = False
    for combo in combos:
        U = basis_of_rows(ctx.Upres + [list(v) for v in combo])
        if len(U) != omega:
            continue
        adm = []
        for J in itertools.combinations(range(ctx.k), omega):
            if ai.rank([[U[i][j] for j in J] for i in range(omega)]) == omega:
                adm.append(J)
        if not adm:
            continue
        Vb = _T_box_basis(ctx, U)
        cands = _pair_candidates(Vb, opts["pair_candidates"])
        for assign in _assignments(cands, ctx.r, opts["assignment_cap"]):
            used += 1
            if used > budget:
                budget_hit = True
                break
            H = [[ctx.h0[i][c] for c in range(ctx.k)] for i in range(ctx.r0)] + \
                [[assign[i][0][c] for c in range(ctx.k)] for i in range(ctx.r)]
            H_A = [[ctx.g0[i][c] for c in range(ctx.k)] for i in range(ctx.r0)] + \
                  [[assign[i][1][c] for c in range(ctx.k)] for i in range(ctx.r)]
            if ai.rank(H) != omega:
                continue
            # cheap necessary conditions: (5b) at lambda = 0 and lambda = 1 gives
            # rank(H_A) = rank(H - H_A) = omega.  A candidate failing them cannot work,
            # so this is a sound pre-filter for the (R0) test below.
            if ai.rank(H_A) != omega:
                continue
            if ai.rank([[H[i][c] - H_A[i][c] for c in range(ctx.k)] for i in range(ctx.q)]) != omega:
                continue
            J0 = adm[0]
            B = _chart_B(U, J0)
            X = [[H[i][j] for j in J0] for i in range(ctx.q)]
            if ai.rank(X) != omega:
                continue
            G = [solve_row_combination(B, H_A[i]) for i in range(ctx.q)]
            if any(g is None for g in G):        # row H_A not inside row H: not a point
                continue
            if not cond5b_pencil(X, G, omega, cross_check=opts["cross_check"]):
                continue
            points.append(_SatPoint(omega, U, assign, H, H_A, adm))
            if len(points) >= opts["collect_points"]:
                return points, budget_hit
        if budget_hit:
            break
    return points, budget_hit


# ====================================================================== literal Phi check

def evaluate_phi(ctx, omega, J, point):
    """Evaluate Phi_{omega,J} of eq:phi at ``point``, item by item, and return the data.

    Builds B from (U, J) and X, G from the point; checks (i) rank X = omega,
    (ii) the rank-consistency system M b = c of Claim 8 is consistent (and that its
    solution really is the B of the chart), (iii)/(iv) row by row, and (v) the Gram
    certificate Z_Q^T Z_Q x = e0 of Claim 11 built from the maximal minors of
    lambda X - G.  Every item is asserted; the returned dict is a certificate.
    """
    H, H_A = point.H, point.H_A
    k, q = ctx.k, ctx.q
    B = _chart_B(point.U, J)
    X = [[H[i][j] for j in J] for i in range(q)]
    assert ai.rank(X) == omega, "(i) rank X != omega"                      # (i) e_omega(X^T X)
    # (iii) for the X rows; G is recovered below from G_i B = g_i
    for i in range(ctx.r0):
        assert [sum(X[i][t] * B[t][c] for t in range(omega)) for c in range(k)] == \
               [ctx.h0[i][c] for c in range(k)], "(iii) X_i B != h0_i"
    G = []
    for i in range(q):
        gi = solve_row_combination(B, H_A[i])
        assert gi is not None, "(iii)/(iv): row H_A not in row H"
        G.append(gi)
    for i in range(ctx.r0):
        assert [sum(G[i][t] * B[t][c] for t in range(omega)) for c in range(k)] == \
               [ctx.g0[i][c] for c in range(k)], "(iii) G_i B != g0_i"
    for i in range(ctx.r0, q):
        pair = [sum(X[i][t] * B[t][c] for t in range(omega)) for c in range(k)] + \
               [sum(G[i][t] * B[t][c] for t in range(omega)) for c in range(k)]
        for drow in ctx.D:
            assert sum(drow[c] * pair[c] for c in range(2 * k)) == 0, "(iv) pair not in T"
    # (ii) the rank-consistency system of the chart, in the non-pivot entries of B
    M, cc = chart_linear_system(ctx, X, G, J)
    kind, payload = dec0.solve_exact(M, cc) if M else ("yes", [])
    if kind == "yes":
        assert dec0.check_solution(M, cc, payload), "(ii) solver returned a non-solution"
        b_solution = payload
    else:
        assert dec0.check_farkas(M, cc, payload), "(ii) not a Farkas certificate"
        raise AssertionError("(ii) the chart linear system is inconsistent at a chart point")
    # Claim 8: rank(MM^T) = rank(MM^T + cc^T), over Q (same ranks over R)
    nvar = len(M[0]) if M else 0
    if nvar > 0:
        MMt = ai.mul(M, ai.tr(M))
        cct = [[cc[i] * cc[j] for j in range(len(cc))] for i in range(len(cc))]
        MMt_plus = [[MMt[i][j] + cct[i][j] for j in range(len(cc))] for i in range(len(cc))]
        assert ai.rank(MMt) == ai.rank(MMt_plus), "Claim 8 rank-consistency criterion violated"
    elif M:
        # no unknowns: MM^T is the zero matrix, so the criterion reads rank(cc^T) = 0,
        # i.e. cc = 0, which is exactly consistency of the empty system
        assert all(v == 0 for v in cc), "(ii) inconsistent empty chart system"
    # rebuild B from the solution and compare with the chart B (both must be the same b)
    B2 = [list(Bt) for Bt in B]
    free_cols = [c for c in range(k) if c not in J]
    nfree = len(free_cols)
    for t in range(omega):
        for p, c in enumerate(free_cols):
            B2[t][c] = b_solution[t * nfree + p]
    for i in range(q):
        for c in range(k):
            lhs = sum(X[i][t] * B2[t][c] for t in range(omega))
            rhs = (ctx.h0[i][c] if i < ctx.r0 else H[i][c])
            assert lhs == rhs, "(ii) the reconstructed B does not generate H"
    # (v) the Gram/window certificate
    x = gram_certificate(X, G)
    assert x is not None, "(v) Z^T Z x = e0 is inconsistent at a chart point"
    assert cond5b_pencil(X, G, omega), "(v) the pencil drops rank although (v) was solvable"
    assert pencil_constant_rank(H, H_A, omega), "(L5) fails at the chart point"
    return {"B": B, "X": X, "G": G, "x": x, "b": b_solution, "J": tuple(J)}


def chart_linear_system(ctx, X, G, J):
    r"""M, c of the chart system M(X,G) b = c(X,G) (Section sec:param, Claim 8).

    Unknowns: the entries B[t][c] with c not in J (t = 0..omega-1, c = 0..k-1); the pivot
    entries are B[t][J[t]] = 1 and B[t][J[t']] = 0, so they contribute a known part.
    Equations: for i <= r0, X_i B = h0_i and G_i B = g0_i (2k per row); for i > r0, the
    (2k - d0) equations D[(X_i B)^T; (G_i B)^T] = 0.
    """
    q, k, r0 = ctx.q, ctx.k, ctx.r0
    om = len(J)
    Jset = set(J)
    free_cols = [c for c in range(k) if c not in Jset]
    pos = {c: p for p, c in enumerate(free_cols)}
    nvar = om * len(free_cols)

    def expr(a, c):
        """(coefficients of the unknown part, known part) of (a B)[c]."""
        co = [FR0] * nvar
        known = FR0
        for t in range(om):
            if J[t] == c:
                known += a[t]
        if c in pos:
            for t in range(om):
                co[t * len(free_cols) + pos[c]] = a[t]
        return co, known

    rows, rhs = [], []
    for i in range(r0):
        for c in range(k):
            cx, kx = expr(X[i], c)
            cg, kg = expr(G[i], c)
            rows.append(cx)
            rhs.append(Fr(ctx.h0[i][c]) - kx)
            rows.append(cg)
            rhs.append(Fr(ctx.g0[i][c]) - kg)
    for i in range(r0, q):
        for drow in ctx.D:
            row = [FR0] * nvar
            known = FR0
            for c in range(k):
                cx, kx = expr(X[i], c)
                cg, kg = expr(G[i], c)
                if drow[c] != 0:
                    row = [a + drow[c] * b for a, b in zip(row, cx)]
                    known += drow[c] * kx
                if drow[k + c] != 0:
                    row = [a + drow[k + c] * b for a, b in zip(row, cg)]
                    known += drow[k + c] * kg
            rows.append(row)
            rhs.append(-known)
    # NOTE: when nvar = 0 (omega = k, so B = I_omega is fully fixed) the rows are empty
    # and the system is consistent iff every rhs is 0; solve_exact handles that correctly.
    return rows, rhs


# ====================================================================== witness -> L

def reconstruct_L(ctx, point, J):
    """The free block R with r_i [N AN] = p_i, and L = [L0; R]."""
    M = [[ctx.N[i][j] for j in range(ctx.k)] + [ctx.AN[i][j] for j in range(ctx.k)]
         for i in range(ctx.n)]                       # n x 2k
    Mt = [[M[i][c] for i in range(ctx.n)] for c in range(2 * ctx.k)]   # 2k x n
    R = []
    for i in range(ctx.r):
        h, g = point.pairs[i]
        target = [Fr(v) for v in list(h) + list(g)]
        kind, payload = dec0.solve_exact(Mt, target)
        assert kind == "yes", "a free pair is not in T = row[N AN]"
        assert dec0.check_solution(Mt, target, payload), "preimage check failed"
        R.append(payload)
    L = [[Fr(v) for v in row] for row in ctx.L0] + R
    assert len(L) == ctx.q and all(len(row) == ctx.n for row in L)
    return L


def verify_feasible(ctx, L, tag):
    """Re-verify L against (5a)/(5b) with the *independent* implementation."""
    ok5a = ai.cond_5a_orig(ctx.A, ctx.C, L)
    ok5b = ai.cond_5b_orig(ctx.A, ctx.C, L)
    assert ok5a, f"{tag}: the returned L fails (5a) -- implementation bug"
    assert ok5b, f"{tag}: the returned L fails (5b) -- implementation bug"
    return ok5a and ok5b


# ====================================================================== Algorithm 1

DEFAULT_OPTS = dict(
    lam_candidates=(Fr(0), Fr(1), Fr(-1), Fr(2), Fr(-2), Fr(1, 2)),
    u_vector_limit=30,
    search_budget=4000,
    pair_candidates=7,
    assignment_cap=400,
    collect_points=3,
    cross_check=True,
    verbose=True,
)


def decide(A, C, L0, q, **overrides):
    """Algorithm 1: decide DEC(q) for the instance (A, C, L0).

    Returns a Decision with verdict 'feasible' | 'infeasible' | 'unknown'.  'feasible'
    always carries a matrix L re-verified against (5a)/(5b); 'infeasible' is returned only
    when every chart has an exact refutation; otherwise 'unknown' lists the open charts.
    """
    opts = dict(DEFAULT_OPTS)
    opts.update(overrides)
    ctx = Context(A, C, L0, q)
    if opts["verbose"]:
        ctx.describe()

    # ---- step 1
    if q < ctx.r0:
        return Decision("infeasible", reason=f"q={q} < r0={ctx.r0}: L=[L0;R] has >= r0 rows",
                        context=ctx)

    # ---- step 3: r = 0 -> the exact test of Section sec:zero (prop:zero)
    if ctx.r == 0:
        if is_zero_mat(ctx.h0) and is_zero_mat(ctx.g0):
            # prop:zero Step 2: H = 0 and H_A = 0, accepted; decide_r0.compress_r0 returns
            # None here and decide_r0 answers False, so the acceptance is done here.
            L = [list(row) for row in ctx.L0]
            verify_feasible(ctx, L, "r=0, h0=g0=0")
            return Decision("feasible", L=L,
                            reason="r=0, H=0 and H_A=0 (prop:zero Step 2); L=L0 verified",
                            context=ctx)
        dec = dec0.decide_r0(A, C, L0)
        if dec.feasible:
            L = [list(row) for row in ctx.L0]
            verify_feasible(ctx, L, "r=0 delegation")
            return Decision("feasible", L=L,
                            reason="r=0: decide_r0 (prop:zero Steps 1,3,4) accepted; "
                                   "L=L0 verified", context=ctx)
        return Decision("infeasible",
                        reason=f"r=0: decide_r0 (prop:zero) rejected: (5a)={dec.cond5a}, "
                               f"(5b)={dec.cond5b}", context=ctx)

    # ---- step 4: h0 = g0 = 0 -> feasible (W = 0)
    if is_zero_mat(ctx.h0) and is_zero_mat(ctx.g0):
        L = [[Fr(v) for v in row] for row in ctx.L0] + zeros(ctx.r, ctx.n)
        verify_feasible(ctx, L, "step 4 (h0=g0=0)")
        return Decision("feasible", L=L,
                        reason="h0=0 and g0=0: zero free block works (W=0); L=[L0;0] verified",
                        context=ctx)

    # ---- step 5: chart enumeration
    charts = []
    searched = {}
    limit = min(q, ctx.k)
    if limit < 1:
        return Decision("unknown", reason="no chart to enumerate (min(q,k) = 0)",
                        context=ctx)
    for omega in range(1, limit + 1):
        obs = chart_obstruction(ctx, omega, opts["lam_candidates"])
        if obs is None:
            pts, budget_hit = _search_omega(ctx, omega, opts)
            searched[omega] = (pts, budget_hit)
        else:
            pts, budget_hit = [], False
        forced = _forced_W_analysis(ctx, omega) if obs is None else None
        if forced is not None and forced.sat:
            # W = T is forced: the chart is decided exactly and the pair list is explicit
            pts = [_SatPoint(omega, forced.U, forced.pairs,
                             [[ctx.h0[i][c] for c in range(ctx.k)] for i in range(ctx.r0)]
                             + [[forced.pairs[i][0][c] for c in range(ctx.k)]
                                for i in range(ctx.r)],
                             [[ctx.g0[i][c] for c in range(ctx.k)] for i in range(ctx.r0)]
                             + [[forced.pairs[i][1][c] for c in range(ctx.k)]
                                for i in range(ctx.r)],
                             forced.admissible_J)]
            budget_hit = False
        for J in itertools.combinations(range(ctx.k), omega):
            if obs is not None:
                outcome = ChartOutcome(omega, J, "unsat", certificate=f"{obs.kind}: {obs.detail}")
                charts.append(outcome)
                if opts["verbose"]:
                    print(f"[chart omega={omega} J={list(J)}] unsat ({obs.kind})")
                continue
            if forced is not None and not forced.sat:
                # dim T = omega + 1 forces W = T; the tests above are complete for it
                why = forced.why_unsat(ctx)
                outcome = ChartOutcome(omega, J, "unsat",
                                       certificate=f"forced W=T: {why}")
                charts.append(outcome)
                if opts["verbose"]:
                    print(f"[chart omega={omega} J={list(J)}] unsat (forced W=T: {why})")
                continue
            if forced is not None and tuple(J) not in forced.admissible_J:
                outcome = ChartOutcome(omega, J, "unsat",
                                       certificate="forced W=T: pi_J is not injective on "
                                                   "U = pi_1(T)")
                charts.append(outcome)
                if opts["verbose"]:
                    print(f"[chart omega={omega} J={list(J)}] unsat (pi_J not injective on T)")
                continue
            hit = next((p for p in pts if tuple(J) in p.admissible_J), None)
            if hit is not None:
                data = evaluate_phi(ctx, omega, J, hit)
                L = reconstruct_L(ctx, hit, J)
                verify_feasible(ctx, L, f"chart omega={omega} J={list(J)}")
                outcome = ChartOutcome(omega, J, "sat", certificate="explicit chart point",
                                       witness={"U": hit.U, "pairs": hit.pairs, **data, "L": L})
                charts.append(outcome)
                if opts["verbose"]:
                    print(f"[chart omega={omega} J={list(J)}] SAT -> feasible (L verified)")
                return Decision("feasible", L=L, charts=charts,
                                reason=f"chart (omega={omega}, J={list(J)}) has the explicit "
                                       f"rational point (U, free pairs); Phi evaluated and "
                                       f"L=[L0;R] re-verified against (5a)/(5b)",
                                context=ctx)
            outcome = ChartOutcome(omega, J, "unknown",
                                   certificate=(f"search budget hit after {opts['search_budget']} "
                                                f"points" if budget_hit
                                                else "no witness, no refutation"),
                                   n_points=len(pts), budget_hit=budget_hit)
            charts.append(outcome)
            if opts["verbose"]:
                print(f"[chart omega={omega} J={list(J)}] unknown "
                      f"({outcome.certificate})")

    undecided = [c for c in charts if c.verdict == "unknown"]
    if not undecided:
        return Decision("infeasible", charts=charts,
                        reason="every chart (omega,J) has an exact refutation (R1)-(R6) or is decided exactly by (D1)",
                        context=ctx)
    return Decision("unknown", charts=charts, undecided=undecided,
                    reason=(f"{len(undecided)} of {len(charts)} charts are neither refuted "
                            f"nor witnessed; a complete implementation needs an exact "
                            f"real-feasibility oracle for Phi for those charts"),
                    context=ctx)


# ====================================================================== CLI / demo

def _parse(M):
    return [[Fr(x) for x in row] for row in M]


def main(argv):
    if len(argv) > 1 and argv[1] != "--demo":
        try:
            with open(argv[1], encoding="utf-8") as handle:
                data = json.load(handle)
            A, C, L0 = _parse(data["A"]), _parse(data["C"]), _parse(data["L0"])
            q = int(data["q"])
        except (OSError, KeyError, ValueError) as exc:
            print(f"malformed instance {argv[1]!r}: {exc}", file=sys.stderr)
            return 2
        print(decide(A, C, L0, q))
        return 0

    ok = True
    # A = 0, C = e1^T, L0 = e2^T, q = 2: H_A = 0 for every L (A N = 0), so (5b) fails at
    # lambda = 0 whenever omega >= 1: genuinely infeasible for r = 1.
    A = _parse([[0, 0, 0], [0, 0, 0], [0, 0, 0]])
    C = _parse([[1, 0, 0]])
    L0 = _parse([[0, 1, 0]])
    d = decide(A, C, L0, 2)
    print("infeasible r>0 instance :", d)
    ok &= d.verdict == "infeasible" and all(c.verdict == "unsat" for c in d.charts)
    print()
    # a genuinely feasible r > 0 instance (found by exhaustive search over small data)
    A = _parse([[0, 1, 0], [0, 0, 1], [0, 0, 0]])
    C = _parse([[1, 0, 0]])
    L0 = _parse([[-1, -1, -1]])
    d = decide(A, C, L0, 2)
    print("feasible r>0 instance   :", d)
    ok &= d.verdict == "feasible" and d.L is not None
    print("RESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
