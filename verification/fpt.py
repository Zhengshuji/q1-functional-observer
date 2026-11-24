#!/usr/bin/env python3
"""fpt.py -- the front end of Algorithm 2 (``alg:fpt``), the FPT decision procedure.

SCOPE.  This module builds the *objects* of Algorithm 2 in exact rational arithmetic and
checks their invariants.  It does **not** decide ``DEC``: the inner test of Algorithm 2 is
real feasibility of ``Psi_{t,omega}``, which needs a real-algebraic oracle and is deliberately
absent (see ``docs/ALGORITHM_REVIEW.md`` and the boundary note at the end of this docstring).

What is here, and what each piece corresponds to in ``paper/paper_I_dec.tex`` (Algorithm 2,
lines 1135-1185):

  * ``N = ker[C; CA]``, ``M = [N  AN]``, ``S = row(AN)``, ``ell = rank(AN)``   (step 4)
  * ``T = row[N  AN]``                                                         (step 4)
  * ``W0 = row(L0 M)``                                                         (step 5)
  * ``V = T cap (S x S)``, and the necessary condition ``W0 <= V``             (step 5/6)
  * ``s0 = dim W0``, ``m' = dim V - s0``                                       (step 7)
  * the Grassmann charts ``J <= [m']`` with ``|J| = t`` and coordinates
    ``Y in R^{t x (m'-t)}``, whose union covers the ``t``-dimensional subspaces of
    ``R^{m'}``; their number over all ``t`` is ``2^{m'}``                      (step 8)

A second, independent check ties this module to the Lean development: the elementary symmetric
function of the Gram matrix ``M M^T``, written as the sum of its principal minors, is positive
in degree ``omega`` exactly when ``rank M >= omega`` -- the theorem
``elemSymm_pos_iff_rank_ge`` of ``Q1Paper/PaperI/Claim8Ej.lean``.  Algorithm 2's condition (i)
is stated in exactly this form (``e_omega(H H^T) > 0``), so checking it here on random
instances is a cross-check between the paper's phrasing, this implementation, and Lean.

All arithmetic is ``fractions.Fraction``.  No floats, no sympy.

Usage:
    python fpt.py --demo
"""

from __future__ import annotations

import itertools
import sys
from fractions import Fraction as Fr

import audit_independent as ai


# ---------------------------------------------------------------- subspace algebra

def intersect_rowspaces(A, B, n):
    """A basis (as column vectors of length n) of row(A) cap row(B).

    ``row(A) cap row(B) = (ker A + ker B)^perp``, so it is the nullspace of the matrix whose
    rows span ``ker A + ker B``.
    """
    spanning = ai.nullspace(A) + ai.nullspace(B)
    if not spanning:
        # both kernels are trivial, so the intersection is everything
        return [list(v) for v in ai.nullspace([])] if False else \
               [[Fr(int(i == j)) for i in range(n)] for j in range(n)]
    return ai.nullspace(ai.tr(spanning))


def _rowbasis(M):
    """Rows of a matrix whose rows form a basis of row(M)."""
    if not M or not M[0]:
        return []
    R = [list(r) for r in M]
    piv = []
    nr, nc = len(R), len(R[0])
    row = 0
    for col in range(nc):
        p = next((r for r in range(row, nr) if R[r][col] != 0), None)
        if p is None:
            continue
        R[row], R[p] = R[p], R[row]
        pv = R[row][col]
        R[row] = [v / pv for v in R[row]]
        for r in range(nr):
            if r != row and R[r][col] != 0:
                f = R[r][col]
                R[r] = [u - f * v for u, v in zip(R[r], R[row])]
        piv.append(col)
        row += 1
        if row == nr:
            break
    return [R[i] for i in range(len(piv))]


def in_rowspace(vec, basis) -> bool:
    """Is the vector in the span of the given rows?"""
    if not basis:
        return all(v == 0 for v in vec)
    return ai.rank([list(b) for b in basis] + [list(vec)]) == ai.rank([list(b) for b in basis])


def pair_space_basis(Sbasis, k):
    """Basis of S x S inside the 2k-dimensional pair space: {(s, 0)} u {(0, s)}."""
    rows = []
    for s in Sbasis:
        rows.append(list(s) + [Fr(0)] * k)
    for s in Sbasis:
        rows.append([Fr(0)] * k + list(s))
    return rows


# ---------------------------------------------------------------- Algorithm 2 data

class FptData:
    def __init__(self, A, C, L0, q):
        self.A, self.C, self.L0, self.q = A, C, L0, q
        self.n = len(A)
        self.r0 = len(L0)
        self.r = q - self.r0

        CA = ai.mul(C, A)
        self.CA = CA
        Ncol = ai.nullspace([list(r) for r in C] + [list(r) for r in CA])
        self.k = len(Ncol)
        self.N = [[Ncol[j][i] for j in range(self.k)] for i in range(self.n)] if self.k else []
        # AN and M = [N AN]
        self.AN = ai.mul(A, self.N) if self.k else []
        self.ell = ai.rank(self.AN) if self.k else 0
        if self.k:
            self.M = [list(self.N[i]) + list(self.AN[i]) for i in range(self.n)]   # n x 2k
            self.T = _rowbasis([[self.M[i][j] for j in range(2 * self.k)] for i in range(self.n)])
            self.S = _rowbasis([[self.AN[i][j] for j in range(self.k)] for i in range(self.n)])
            self.W0 = _rowbasis(ai.mul(L0, self.M))
            self.SxS = pair_space_basis(self.S, self.k)
            self.V = intersect_rowspaces(self.T, self.SxS, 2 * self.k)
            self.s0 = len(self.W0)
            self.mprime = len(self.V) - self.s0
        else:
            self.M = self.T = self.S = self.W0 = self.SxS = self.V = []
            self.s0 = self.mprime = 0

    # --- invariants, asserted before any verdict is drawn
    def check(self):
        if self.k:
            assert ai.rank(self.M) == self.k + self.ell, "rank[N AN] != k + ell"
            assert len(self.T) == ai.rank(self.M), "T is not a basis of row[N AN]"
            assert len(self.S) == self.ell, "S is not a basis of row(AN)"
            assert all(in_rowspace(w, self.V) for w in self.W0), "W0 is not inside V = T cap (S x S)"
            assert self.mprime >= 0, "m' = dim V - s0 is negative"
        return True

    def describe(self):
        print(f"[fpt] n={self.n} r0={self.r0} q={self.q} r={self.r} "
              f"k={self.k} ell={self.ell} d0={len(self.T)} s0={self.s0} m'={self.mprime}")


# ---------------------------------------------------------------- Grassmann charts

def grassmann_charts(mprime, t):
    """All charts of the t-dimensional subspaces of R^{m'}: J <= [m'], |J| = t.

    Each chart parameterises the subspace by a t x m' matrix [I_t | Y] read in the J
    coordinates, so it has t*(m'-t) free parameters.  Over all t the charts number 2^{m'}.
    """
    return [tuple(J) for J in itertools.combinations(range(mprime), t)]


def chart_count(mprime):
    """Number of Grassmann charts over every t: must be 2^{m'}."""
    total = sum(len(grassmann_charts(mprime, t)) for t in range(mprime + 1))
    assert total == 2 ** mprime, f"chart count {total} != 2^{mprime}"
    return total


def chart_matrix(J, Y, mprime):
    """The t x m' matrix [I_t | Y] placed in the J columns (a chart point)."""
    t = len(J)
    cols = [Fr(0)] * mprime
    rows = []
    free = [c for c in range(mprime) if c not in J]
    for a in range(t):
        r = [Fr(0)] * mprime
        r[J[a]] = Fr(1)
        for b, c in enumerate(free):
            r[c] = Y[a][b]
        rows.append(r)
    return rows


# ---------------------------------------------------------------- the e_omega cross-check

def principal_minors_sum(H, omega):
    """e_omega(H H^T) as the sum of the omega x omega principal minors of the Gram matrix."""
    from itertools import combinations

    q = len(H)
    if omega > q:
        return Fr(0)
    gram = [[sum(H[i][t] * H[j][t] for t in range(len(H[0]))) for j in range(q)] for i in range(q)]
    total = Fr(0)
    for S in combinations(range(q), omega):
        sub = [[gram[i][j] for j in S] for i in S]
        total += _det_int(sub)
    return total


def _det_int(M):
    k = len(M)
    if k == 0:
        return Fr(1)
    if k == 1:
        return M[0][0]
    if k == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    acc = Fr(0)
    for j in range(k):
        if M[0][j] == 0:
            continue
        minor = [[M[i][c] for c in range(k) if c != j] for i in range(1, k)]
        term = M[0][j] * _det_int(minor)
        acc = acc + term if j % 2 == 0 else acc - term
    return acc


def check_elem_symm(n_instances=25, seed=7):
    """e_omega(M M^T) > 0  <=>  rank M >= omega, on random small integer matrices.

    This is the theorem `elemSymm_pos_iff_rank_ge` of Q1Paper/PaperI/Claim8Ej.lean; the paper's
    Algorithm 2 states its condition (i) in exactly this form.
    """
    import random

    rng = random.Random(seed)
    checked = 0
    for _ in range(n_instances):
        rows, cols = rng.randint(1, 4), rng.randint(1, 3)
        M = [[Fr(rng.randint(-2, 2)) for _ in range(cols)] for _ in range(rows)]
        rank = ai.rank(M)
        for omega in range(0, rows + 2):
            e = principal_minors_sum(M, omega)
            assert (e > 0) == (rank >= omega), (
                f"e_{omega} > 0 != (rank {rank} >= {omega}) for M = {M}")
            checked += 1
    return checked


def demo():
    ok = True
    # A = the shift, C = e1^T, L0 = e1^T, q = 2  (an r = 1 instance)
    A = [[Fr(0), Fr(1), Fr(0)], [Fr(0), Fr(0), Fr(1)], [Fr(0), Fr(0), Fr(0)]]
    C = [[Fr(1), Fr(0), Fr(0)]]
    L0 = [[Fr(1), Fr(0), Fr(0)]]
    ctx = FptData(A, C, L0, 2)
    ctx.describe()
    assert ctx.check(), "the Algorithm 2 invariants failed"
    print(f"[fpt] W0 <= V: ok;  m' = {ctx.mprime}")
    total = chart_count(ctx.mprime)
    print(f"[fpt] Grassmann charts over all t: {total} = 2^{ctx.mprime}")
    # a chart point really is a t x m' matrix of rank t
    for t in range(0, ctx.mprime + 1):
        for J in grassmann_charts(ctx.mprime, t)[:1]:
            Y = [[Fr(a + b + 1) for b in range(ctx.mprime - t)] for a in range(t)]
            Z = chart_matrix(J, Y, ctx.mprime)
            assert len(Z) == t and (t == 0 or ai.rank(Z) == t), "the chart point is not rank t"
    print("[fpt] chart points verified: rank [I_t | Y] = t for every t")
    n = check_elem_symm()
    print(f"[fpt] e_omega(M M^T) > 0 <=> rank M >= omega: {n} (M, omega) pairs agree")
    print("RESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


def main(argv):
    return demo()


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
