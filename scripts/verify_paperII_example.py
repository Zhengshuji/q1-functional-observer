"""verify_paperII_example.py -- exact rational certificate for the appendix instance.

Paper II, Appendix (`app:example`): the instance of Fernando's Section VII with n = 8, p = 2,
the published claim of infeasibility at order 4, and the four-row witness `L = [L0; R]`.

This script checks, with exact rational arithmetic (no floating point anywhere):

  1. the basic invariants of the instance: shapes, k = dim ker[C; CA] = 4,
     d_0 = rank[N AN] = 6, s_0 = dim row(L0 M) = 2, ell = 4;
  2. condition (5a) for the witness:  rank[L; CA; C] = rank[LA; L; CA; C];
  3. condition (5b) for the witness:  the 8 x 8 pencil [lam L - LA; CA; C] has vanishing
     determinant and the gcd of all its 7 x 7 minors is a nonzero constant, so its rank is 7
     for every lam in C (over Q, hence over C).

Verification is not proof, but here it checks the *statement* the paper prints (an explicit
rational witness), not a special case of it.

    python scripts/verify_paperII_example.py
"""

from __future__ import annotations

import itertools
import sys

import sympy as sp


def rank(M: sp.Matrix) -> int:
    assert M.rows > 0 and M.cols > 0, "rank of an empty matrix"
    return int(M.rank())


def main() -> int:
    C = sp.Matrix([[-2, -2, 2, -2, -1, 0, 1, -3], [0, 0, 1, 2, 2, 3, -1, -2]])
    L0 = sp.Matrix([[-2, -1, -2, -3, -1, 3, 2, 0], [1, -1, -2, 1, 0, 2, 0, 1]])
    A = sp.Matrix(
        [
            [0, 1, 0, 1, 0, 0, 0, 0],
            [0, -1, 1, 0, 0, 0, 0, -1],
            [1, 0, -1, 1, 0, 0, 1, -1],
            [-1, -1, 0, -2, 0, 0, 0, 0],
            [0, 0, 0, 0, -2, 0, 0, 1],
            [0, 0, 0, 0, 0, -2, 1, 0],
            [0, 0, 0, 0, 0, -1, -2, 1],
            [0, 0, 0, 0, 0, 0, 1, -2],
        ]
    )
    R = sp.Matrix(
        [
            [sp.Rational(-42919, 32067), sp.Rational(-55096, 10689), 1, 0, 0, 0, 0, 0],
            [sp.Rational(3283, 4581), sp.Rational(118, 1527), 0, 1, 0, 0, 0, 0],
        ]
    )

    # ---- basic invariants (assert before concluding anything) ----
    assert (C.rows, C.cols) == (2, 8), C.shape
    assert (L0.rows, L0.cols) == (2, 8), L0.shape
    assert (A.rows, A.cols) == (8, 8), A.shape
    assert (R.rows, R.cols) == (2, 8), R.shape
    L = sp.Matrix.vstack(L0, R)
    assert (L.rows, L.cols) == (4, 8), L.shape

    CA = C * A
    ker_stack = sp.Matrix.vstack(C, CA)
    N = ker_stack.nullspace()
    k = len(N)
    Nmat = sp.Matrix.hstack(*N) if k else sp.Matrix.zeros(8, 0)
    d0 = rank(sp.Matrix.hstack(Nmat, A * Nmat)) if k else 0
    print(f"k = dim ker[C; CA] = {k}")
    print(f"d_0 = rank[N AN]     = {d0}")
    assert k == 4, k
    assert d0 == 6, d0

    # s_0 = dim row(L0 M) with M = [N AN] (the paper's W_0 = row(L0 M))
    Mmat = sp.Matrix.hstack(Nmat, A * Nmat)
    s0 = rank(L0 * Mmat)
    print(f"s_0 = dim row(L0 M)  = {s0}   (M = [N AN])")
    print(f"      dim row(L0 N)  = {rank(L0 * Nmat)}")
    assert s0 == 2, s0
    ell_val = rank(A * Nmat)
    print(f"ell = rank(A N)      = {ell_val}")
    assert ell_val == 4, ell_val

    # ---- (5a) ----
    LA = L * A
    left = rank(sp.Matrix.vstack(L, CA, C))
    right = rank(sp.Matrix.vstack(LA, L, CA, C))
    print(f"rank[L; CA; C]      = {left}")
    print(f"rank[LA; L; CA; C]  = {right}")
    assert left == right == 7, (left, right)

    # ---- (5b) ----
    lam = sp.Symbol("lam")
    P = sp.Matrix.vstack(lam * L - LA, CA, C)
    assert (P.rows, P.cols) == (8, 8), P.shape
    det = sp.expand(P.det())
    print(f"det of the pencil   = {det}")
    assert det == 0, det

    minors = []
    for i, j in itertools.product(range(8), range(8)):
        m = sp.expand(sp.factor(P.minor_submatrix(i, j).det()))
        if m != 0:
            minors.append(m)
    assert minors, "all 7x7 minors vanish: rank would drop below 7"
    g = minors[0]
    for m in minors[1:]:
        g = sp.gcd(g, m)
    g = sp.factor(sp.simplify(g))
    print(f"nonzero 7x7 minors  = {len(minors)} / 64")
    print(f"gcd of the minors   = {g}")
    assert g.is_number and sp.simplify(g) != 0, g

    print("OK: (5a) and (5b) hold for this four-row witness; q_min <= 4 for the instance.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
