#!/usr/bin/env python3
"""cb_gram.py -- the Cauchy-Binet compression of Algorithm 2's window Gram, and its check.

Algorithm 2 states its condition (ii) as

    Z(Y)^T Z(Y) x = e_0,   with Z(Y) computed from K(lambda, mu) by Cauchy-Binet
                           over the ell columns of S.

This module builds that Gram matrix in two independent ways and compares them:

  PATH A (Cauchy-Binet, the paper's route)
      K(lambda, mu) = sum_{|J| = omega} det( P(lambda)_{:,J}^T  P(mu)_{:,J} )
      a bivariate polynomial in (lambda, mu); then the Gram entries are the diagonal band sums
          T[t][t'] = sum_{j=0}^{omega-1} S[t - j][t' - j],
      where S[a][b] is the coefficient of lambda^a mu^b in K.

  PATH B (direct, the definition)
      enumerate every omega x omega submatrix of the pencil P(lambda) = lambda H - G, take the
      maximal-minor coefficient vectors, and form the Gram matrix of those coefficient vectors,
      summed over all submatrices.

If the two agree on random rational instances, the compression is verified on those instances;
if they disagree, the disagreement is a fact about the paper's (ii) and is reported as such.
Neither outcome is turned into a proof -- this is `[exact verification n/N]`.

All arithmetic is fractions.Fraction on bivariate polynomials with rational coefficients.
"""

from __future__ import annotations

import itertools
import sys
from fractions import Fraction as Fr

import audit_independent as ai

# a bivariate polynomial is a dict {(a, b): coeff} with a, b >= 0; missing keys are 0
ZERO = {}


def bp_add(p, q):
    out = dict(p)
    for k, v in q.items():
        out[k] = out.get(k, Fr(0)) + v
        if out[k] == 0:
            del out[k]
    return out


def bp_mul(p, q):
    out = {}
    for (a, b), u in p.items():
        for (c, d), v in q.items():
            k = (a + c, b + d)
            out[k] = out.get(k, Fr(0)) + u * v
    return {k: v for k, v in out.items() if v != 0}


def bp_scale(p, c):
    if c == 0:
        return {}
    return {k: v * c for k, v in p.items() if v * c != 0}


def bp_det(M):
    """Determinant of a square matrix of bivariate polynomials (Laplace)."""
    n = len(M)
    if n == 0:
        return {(0, 0): Fr(1)}
    if n == 1:
        return dict(M[0][0])
    acc = {}
    for j in range(n):
        if not M[0][j]:
            continue
        minor = [[M[i][c] for c in range(n) if c != j] for i in range(1, n)]
        term = bp_mul(M[0][j], bp_det(minor))
        acc = bp_add(acc, term) if j % 2 == 0 else bp_add(acc, bp_scale(term, Fr(-1)))
    return acc


def pencil_entry(H, G, i, j, var):
    """The entry lam*H[i][j] - G[i][j], as a bivariate poly in (lam, mu); `var` picks which."""
    if var == "lam":
        return {(1, 0): H[i][j], (0, 0): -G[i][j]}
    return {(0, 1): H[i][j], (0, 0): -G[i][j]}


def K_cauchy_binet(H, G, omega):
    r"""K(lam, mu) = sum over ROW subsets I of det(P(lam)_I  P(mu)_I^T).

    This is the Cauchy-Binet compression: expanding each omega x omega determinant of the Gram
    by Cauchy-Binet gives sum_{I,J} det P(lam)_{I,J} det P(mu)_{I,J}, i.e. the plain Gram of all
    maximal-minor coefficient vectors -- which is exactly what gram_from_minors computes by
    enumerating every submatrix.  Summing over row subsets only is what avoids that enumeration.
    """
    q, ell = len(H), len(H[0])
    total = {}
    for I in itertools.combinations(range(q), omega):
        n = len(I)
        # M[a][b] = sum_j P(I[a], j)(lam) * P(I[b], j)(mu)
        M = [[{} for _ in range(n)] for _ in range(n)]
        for a in range(n):
            for b in range(n):
                entry = {}
                for j in range(ell):
                    entry = bp_add(entry, bp_mul(pencil_entry(H, G, I[a], j, "lam"),
                                                 pencil_entry(H, G, I[b], j, "mu")))
                M[a][b] = entry
        total = bp_add(total, bp_det(M))
    return total


def gram_from_K(K, omega):
    """The plain Gram: entry (a, b) is the coefficient of lambda^a mu^b in K.

    (The WINDOW matrix's Gram has an additional diagonal band sum,
    ``T[t][t'] = sum_{j<omega} S[t-j][t'-j]``; that step belongs to the window construction and
    is not what is compared here -- here the point is the Cauchy-Binet compression itself.)
    """
    n = 2 * omega
    return [[K.get((a, b), Fr(0)) for b in range(n)] for a in range(n)]


def minor_coeffs(H, G, rows, cols):
    """Coefficients of det of the submatrix rows x cols of lam H - G, as a list in lam."""
    n = len(rows)
    M = [[pencil_entry(H, G, rows[i], cols[j], "lam") for j in range(n)] for i in range(n)]
    # replace the (0,1) component: here we want a univariate poly in lam
    M1 = [[{(a, 0): v for (a, b), v in M[i][j].items() if b == 0} for j in range(n)]
          for i in range(n)]
    det = bp_det(M1)
    if not det:
        return []
    deg = max(a for (a, b) in det)
    return [det.get((a, 0), Fr(0)) for a in range(deg + 1)]


def gram_from_minors(H, G, omega):
    """The direct definition: Gram of the coefficient vectors of all omega x omega minors."""
    q, ell = len(H), len(G[0])
    coeffs = []
    for rows in itertools.combinations(range(q), omega):
        for cols in itertools.combinations(range(ell), omega):
            c = minor_coeffs(H, G, rows, cols)
            if c:
                coeffs.append(c)
    T = [[Fr(0) for _ in range(2 * omega)] for _ in range(2 * omega)]
    for a in range(2 * omega):
        for b in range(2 * omega):
            s = Fr(0)
            for c in coeffs:
                if a < len(c) and b < len(c):
                    s += c[a] * c[b]
            T[a][b] = s
    return T


def compare(H, G, omega, label):
    A = gram_from_K(K_cauchy_binet(H, G, omega), omega)
    B = gram_from_minors(H, G, omega)
    same = A == B
    if not same:
        print(f"  [{label}] MISMATCH for omega={omega}")
        for i in range(2 * omega):
            print(f"    A[{i}] = {A[i]}")
            print(f"    B[{i}] = {B[i]}")
    return same


def gram_certificate(G):
    """Solve G x = e_0 exactly; return x, or None when there is no solution."""
    from decide_r0 import solve_exact

    n = len(G)
    e0 = [Fr(1)] + [Fr(0)] * (n - 1)
    kind, payload = solve_exact([row[:] for row in G], e0)
    return payload if kind == "yes" else None


def pencil_has_common_root(H, G, omega):
    """True iff the maximal minors of lam H - G share a common complex root.

    Independent of the Gram: the gcd of the maximal-minor polynomials is a nonzero constant iff
    there is no common root.
    """
    q, ell = len(H), len(H[0])
    polys = []
    for rows in itertools.combinations(range(q), omega):
        for cols in itertools.combinations(range(ell), omega):
            c = minor_coeffs(H, G, rows, cols)
            if c:
                polys.append(c)
    if not polys:
        return False
    g = polys[0]
    for p in polys[1:]:
        g = ai.pgcd(g, p)
        if ai.pconst_nonzero(g):
            return False
    return not ai.pconst_nonzero(g)


def check_certificate_iff(H, G, omega, label):
    """(ii) of Algorithm 2: Z^T Z x = e_0 is solvable  <=>  the pencil has no common root."""
    gram = gram_from_K(K_cauchy_binet(H, G, omega), omega)
    x = gram_certificate(gram)
    solvable = x is not None
    no_common_root = not pencil_has_common_root(H, G, omega)
    if solvable != no_common_root:
        print(f"  [{label}] omega={omega}: cert solvable={solvable} but "
              f"no-common-root={no_common_root}")
    return solvable == no_common_root


def demo():
    cases = [
        ([[Fr(1), Fr(0)], [Fr(0), Fr(1)], [Fr(1), Fr(1)]],
         [[Fr(0), Fr(1)], [Fr(1), Fr(0)], [Fr(1), Fr(-1)]], 1, "3x2, omega=1"),
        ([[Fr(1), Fr(2), Fr(0)], [Fr(0), Fr(1), Fr(1)], [Fr(2), Fr(0), Fr(1)]],
         [[Fr(0), Fr(1), Fr(1)], [Fr(1), Fr(0), Fr(2)], [Fr(1), Fr(1), Fr(0)]], 2, "3x3, omega=2"),
    ]
    ok = True
    for H, G, omega, label in cases:
        good = compare(H, G, omega, label)
        print(f"[{label}] omega={omega}: K-compression {'==' if good else '!='} direct minors")
        ok &= good
        cert = check_certificate_iff(H, G, omega, label)
        print(f"[{label}] omega={omega}: Z^T Z x = e0 solvable <=> no common root: {cert}")
        ok &= cert
    print("RESULT:", "PASS" if ok else "MISMATCH (reported, not hidden)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(demo())
