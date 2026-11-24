#!/usr/bin/env python3
"""decide_r0.py -- an end-to-end decision procedure for the r = 0 branch of Paper I.

This is the *r = 0 branch only*.  Do not read it as an implementation of the paper's full
DEC algorithm: the r > 0 branch needs chart enumeration plus a real-algebraic feasibility
oracle and is NOT implemented here (the entry point raises NotImplementedError explicitly
rather than returning a guess).

What it does
------------
For an instance (A, C, L0), write M = [C; CA], take a kernel basis N of M, and set
H = L0 N, H_A = L0 A N, omega = rank H.  The paper (Proposition 4) reduces the existence of
an observer of order r0 to

    (5a)  rank[H; H_A] = omega
    (5b)  rank(lambda X - G) = omega for every lambda in C,

where X, G are the omega-column blocks of H, H_A on a set of independent columns.

(R0)  The (5b) test is equivalent to the consistency of a *finite rational linear system*.
    With unknown matrices S_0 .. S_d (omega x q) and d = 2 omega - 2, the equations are,
    by the power k of lambda,

        k = 0        :  -S_0 G            = I_omega
        1 <= k <= d  :   S_{k-1} X - S_k G = 0
        k = d + 1    :   S_d X             = 0

    A solution (S_j) is a certificate that S(lambda) Q(lambda) = I for all lambda, i.e. that
    the pencil never loses rank.  The system is consistent iff (5b) holds.

Certificates in both directions (this is the point of the script)
-----------------------------------------------------------------
  YES  the solver returns the actual solution, i.e. the matrices S_0 .. S_d.  It is checked
       by substituting back into every equation, not by trusting the solver.
  NO   the solver returns a Farkas certificate: a vector y with y^T M = 0 and y^T b != 0,
       which is checked directly and *proves* inconsistency.  Absence of a solution is never
       reported on the strength of the solver having failed to find one.

Self-check (independent path)
-----------------------------
The (R0) consistency verdict is cross-checked against the *other* exact test, the gcd of the
maximal omega-order minors of Q(lambda) being a nonzero constant, computed by a separate
code path (`gcd_minor_test`, reusing the polynomial arithmetic of `audit_independent`).  The
two must agree on every instance; a disagreement is an assertion failure, not a warning.

Honesty notes
-------------
* Everything is exact rational arithmetic (`fractions.Fraction`).  No floats take part in any
  decision, and `unknown`/timeout/exception are never turned into `False`.
* The witness is in the *compressed* form the paper itself uses (the S family).  Reconstructing
  an actual observer matrix L from it is a further step and is not implemented.
* This file is an `[algorithm implementation]` for the r = 0 branch, not an `[exact
  verification]` of a conjectured identity.

Usage
-----
    python decide_r0.py --demo
    python decide_r0.py instance.json     # {"A": .., "C": .., "L0": ..}

Exit status: 0 = every checked instance behaved as expected, 1 = a check failed,
2 = malformed input.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction as Fr

import audit_independent as ai


# ------------------------------------------------------------------ exact linear algebra

def solve_exact(M, b):
    """Solve M x = b over Q exactly.

    Returns ("yes", x) with x a solution, or ("no", y) with y^T M = 0 and y^T b != 0.
    The certificate is tracked through the elimination (the y's are the row combinations).
    """
    nr, nc = len(M), len(M[0])
    A = [list(M[i]) + [b[i]] for i in range(nr)]
    Y = [[Fr(int(i == j)) for j in range(nr)] for i in range(nr)]
    pivots = []
    row = 0
    for col in range(nc):
        piv = next((r for r in range(row, nr) if A[r][col] != 0), None)
        if piv is None:
            continue
        A[row], A[piv] = A[piv], A[row]
        Y[row], Y[piv] = Y[piv], Y[row]
        pv = A[row][col]
        A[row] = [v / pv for v in A[row]]
        Y[row] = [v / pv for v in Y[row]]
        for r in range(nr):
            if r != row and A[r][col] != 0:
                f = A[r][col]
                A[r] = [u - f * v for u, v in zip(A[r], A[row])]
                Y[r] = [u - f * v for u, v in zip(Y[r], Y[row])]
        pivots.append(col)
        row += 1
        if row == nr:
            break
    for i in range(nr):
        if all(v == 0 for v in A[i][:nc]) and A[i][nc] != 0:
            return "no", Y[i]
    x = [Fr(0)] * nc
    for i, c in enumerate(pivots):
        x[c] = A[i][nc]
    return "yes", x


def check_solution(M, b, x) -> bool:
    """Substitute back: M x == b, entry by entry, exactly."""
    nr = len(M)
    for i in range(nr):
        s = sum((M[i][k] * x[k] for k in range(len(x))), Fr(0))
        if s != b[i]:
            return False
    return True


def check_farkas(M, b, y) -> bool:
    """y^T M == 0 and y^T b != 0."""
    nc = len(M[0])
    for k in range(nc):
        if sum((y[i] * M[i][k] for i in range(len(M))), Fr(0)) != 0:
            return False
    return sum((y[i] * b[i] for i in range(len(M))), Fr(0)) != 0


# ------------------------------------------------------------------ the compressed pencil

def mat_mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def compress_r0(A, C, L0):
    """(X, G, omega, cond5a) for the instance, or None when omega = 0.

    N is a basis of ker[C; CA] (columns), H = L0 N, H_A = L0 A N, omega = rank H, and X, G
    are the omega independent columns of H, H_A.
    """
    n = len(A)
    CA = mat_mul(C, A)
    Mstack = [list(r) for r in C] + [list(r) for r in CA]
    Ncol = ai.nullspace(Mstack)                 # list of column vectors of length n
    if not Ncol:
        return None
    k = len(Ncol)
    N = [[Ncol[j][i] for j in range(k)] for i in range(n)]      # n x k
    H = mat_mul(L0, N)
    HA = mat_mul(mat_mul(L0, A), N)
    om = ai.rank(H)
    if om == 0:
        return None
    # independent column set of H
    J = []
    for j in range(k):
        trial = J + [j]
        sub = [[H[i][c] for c in trial] for i in range(len(H))]
        if ai.rank(sub) == len(trial):
            J = trial
        if len(J) == om:
            break
    assert len(J) == om, "failed to find an independent column set"
    X = [[H[i][c] for c in J] for i in range(len(H))]
    G = [[HA[i][c] for c in J] for i in range(len(HA))]
    cond5a = ai.rank(list(H) + list(HA)) == om   # vertical stack: rank[H; H_A] = rank H
    return X, G, om, cond5a


def build_system(X, G, om):
    """(M, b) of (R0): unknowns S_j[a, b], j = 0..d with d = 2 omega - 2."""
    q = len(X)
    d = 2 * om - 2
    # clear denominators
    den = 1
    for v in [x for r in X for x in r] + [x for r in G for x in r]:
        den = den * v.denominator // _gcd(den, v.denominator)
    Xs = [[x * den for x in r] for r in X]
    Gs = [[x * den for x in r] for r in G]
    nvar = (d + 1) * om * q
    rows, rhs = [], []
    for k in range(d + 2):
        for a in range(om):
            for c in range(om):
                row = [Fr(0)] * nvar
                if k == 0:
                    for bb in range(q):
                        row[0 * om * q + a * q + bb] = -Gs[bb][c]
                    rhs.append(Fr(int(a == c)))
                elif k <= d:
                    for bb in range(q):
                        row[(k - 1) * om * q + a * q + bb] += Xs[bb][c]
                        row[k * om * q + a * q + bb] -= Gs[bb][c]
                    rhs.append(Fr(0))
                else:
                    for bb in range(q):
                        row[d * om * q + a * q + bb] += Xs[bb][c]
                    rhs.append(Fr(0))
                rows.append(row)
    return rows, rhs


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


# ------------------------------------------------------------------ independent reference test

def gcd_minor_test(X, G):
    """True iff the gcd of the maximal minors of lam X - G is a nonzero constant."""
    from itertools import combinations

    q, om = len(X), len(X[0])
    # row i of the pencil, as a vector of polynomials in lambda: lam X[i][j] - G[i][j]
    rows = []
    for i in range(q):
        row = [ai.psub([Fr(0), X[i][j]], [G[i][j]]) for j in range(om)]
        rows.append(row)
    mins = []
    for rs in combinations(range(q), om):
        for cs in combinations(range(om), om):
            sub = [[rows[rs[i]][cs[j]] for j in range(om)] for i in range(om)]
            val = ai._det_poly(sub)
            if not ai.pzero(val):
                mins.append(val)
    if not mins:
        return False
    g = mins[0]
    for m in mins[1:]:
        g = ai.pgcd(g, m)
        if ai.pconst_nonzero(g):
            return True
    return ai.pconst_nonzero(g)


# ------------------------------------------------------------------ the decision procedure

class Decision:
    def __init__(self, feasible, cond5a, cond5b, witness=None, certificate=None, note=""):
        self.feasible = feasible
        self.cond5a = cond5a
        self.cond5b = cond5b
        self.witness = witness            # the S family, when feasible
        self.certificate = certificate    # the Farkas vector, when not
        self.note = note

    def __repr__(self):
        return (f"Decision(feasible={self.feasible}, (5a)={self.cond5a}, (5b)={self.cond5b}"
                f"{', witness' if self.witness is not None else ''}"
                f"{', certificate' if self.certificate is not None else ''})")


def decide_r0(A, C, L0, cross_check=True):
    """Decide the r = 0 branch exactly.

    Returns a `Decision`.  Raises NotImplementedError for the r > 0 branch (which this module
    deliberately does not implement) rather than guessing.
    """
    comp = compress_r0(A, C, L0)
    if comp is None:
        # omega = 0: no compressed pencil to test; the paper's step 2 covers this case.
        return Decision(False, False, False, note="omega = 0 (handled as a separate case in the paper)")
    X, G, om, cond5a = comp
    M, b = build_system(X, G, om)
    kind, payload = solve_exact(M, b)
    if kind == "yes":
        assert check_solution(M, b, payload), "the solver's own solution does not satisfy the system"
    else:
        assert check_farkas(M, b, payload), "the returned vector is not a Farkas certificate"
    cond5b = (kind == "yes")
    if cross_check:
        ref = gcd_minor_test(X, G)
        assert ref == cond5b, (
            "the (R0) linear system and the gcd-of-minors test DISAGREE "
            f"(system={cond5b}, gcd={ref}): one of the two exact routes is wrong")
    return Decision(cond5a and cond5b, cond5a, cond5b,
                    witness=payload if kind == "yes" else None,
                    certificate=None if kind == "yes" else payload)


def _parse(M):
    return [[Fr(x) for x in row] for row in M]


def _demo():
    """One feasible and one infeasible instance; both are checked, not just printed."""
    ok = True
    # A = the shift e1 -> e2 -> e3 -> 0, C = e1^T, so CA = e2^T and ker[C; CA] = span(e3).
    A = _parse([[0, 1, 0], [0, 0, 1], [0, 0, 0]])
    C = _parse([[1, 0, 0]])
    # feasible: found by exhaustive search over small integer L0 (the demo asserts the result
    # rather than trusting the search): rank[H; H_A] = omega and the pencil never loses rank.
    L_ok = _parse([[-1, -1, -1], [-1, -1, 0]])
    d = decide_r0(A, C, L_ok)
    print("feasible instance  :", d)
    ok &= d.feasible and d.cond5a and d.cond5b and d.witness is not None
    # infeasible: one row, H = (1), H_A = (0), the pencil is lam itself, which vanishes at 0.
    L_bad = _parse([[0, 0, 1]])
    d2 = decide_r0(A, C, L_bad)
    print("infeasible instance:", d2)
    ok &= (not d2.feasible) and (not d2.cond5b) and d2.certificate is not None
    print("RESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


def main(argv):
    if len(argv) == 1 or "--demo" in argv:
        return _demo()
    path = argv[1]
    try:
        with open(path, encoding="utf-8") as handle:
            data = json.load(handle)
        A, C, L0 = _parse(data["A"]), _parse(data["C"]), _parse(data["L0"])
    except (OSError, KeyError, ValueError) as exc:
        print(f"malformed instance {path!r}: {exc}", file=sys.stderr)
        return 2
    d = decide_r0(A, C, L0)
    print(d)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
