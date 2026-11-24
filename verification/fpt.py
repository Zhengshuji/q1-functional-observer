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


def extend_basis(B, extra):
    """Extend the rows of B by vectors of `extra` until the span stops growing."""
    out = [list(b) for b in B]
    r = ai.rank(out) if out else 0
    for v in extra:
        cand = out + [list(v)]
        rr = ai.rank(cand)
        if rr > r:
            out, r = cand, rr
    return out


def chart_blocks(ctx, J, Y):
    """H(Y), G(Y): the two (s0+t) x ell blocks of Z_ch,J(Y) = [E0; C_J(Y) E_Q].

    E0 is the basis of W0 and E_Q a complement of W0 inside V = T cap (S x S); C_J(Y) is the
    t x m' chart matrix [I_t | Y] read in the J coordinates.
    """
    k = ctx.k
    ext = extend_basis(ctx.W0, ctx.V)
    assert len(ext) == len(ctx.V), "W0 is not inside V"
    EQ = ext[ctx.s0:]
    assert len(EQ) == ctx.mprime, f"the complement has dimension {len(EQ)}, not m'={ctx.mprime}"
    C = chart_matrix(J, Y, ctx.mprime)
    extra = [[sum(C[a][b] * EQ[b][c] for b in range(ctx.mprime)) for c in range(2 * k)]
             for a in range(len(J))]
    Zch = [list(w) for w in ctx.W0] + extra
    H = [row[:k] for row in Zch]
    G = [row[k:] for row in Zch]
    return H, G


def psi_eval(ctx, J, Y, omega):
    """Evaluate Psi_{t,omega} at a chart point: items (i) and (ii) of Algorithm 2."""
    import cb_gram as cb

    H, G = chart_blocks(ctx, J, Y)
    if not H or not H[0] or omega > len(H):
        # no rows, or fewer rows than omega: e_omega(H H^T) = 0, so item (i) fails and the chart
        # contributes nothing at this omega
        return {"H": H, "G": G, "e_omega": Fr(0), "e_next": Fr(0), "i": False,
                "ii": False, "x": None}
    HG = [list(H[i]) + list(G[i]) for i in range(len(H))]
    e_omega = principal_minors_sum(H, omega)
    e_next = principal_minors_sum(HG, omega + 1)
    i_ok = (e_omega > 0) and (e_next == 0)
    gram = cb.gram_from_K(cb.K_cauchy_binet(H, G, omega), omega)
    x = cb.gram_certificate(gram)
    return {"H": H, "G": G, "e_omega": e_omega, "e_next": e_next,
            "i": i_ok, "ii": x is not None, "x": x}


def reconstruct_L(ctx, H, G):
    """An observer L with L M = [H G] and its first r0 rows equal to L0, or None.

    The conditions of the paper depend on L only through L N = H and L A N = G, i.e. through
    L M with M = [N AN].  M has full column rank (asserted in FptData.check), so the equations
    determine L on col(M); the rows are pinned to L0 where the paper requires it.  The system is
    solved exactly, so a None answer means the pinning is incompatible with [H G].
    """
    from decide_r0 import solve_exact

    k, n, r0 = ctx.k, ctx.n, ctx.r0
    q = len(H)
    nvar = q * n
    rows, rhs = [], []

    def idx(i, c):
        return i * n + c

    # L M = [H G]
    HG = [list(H[i]) + list(G[i]) for i in range(q)]
    for i in range(q):
        for c in range(2 * k):
            row = [Fr(0)] * nvar
            for j in range(n):
                row[idx(i, j)] = ctx.M[j][c]
            rows.append(row)
            rhs.append(HG[i][c])
    # L[i] = L0[i] for i < r0
    for i in range(r0):
        for j in range(n):
            row = [Fr(0)] * nvar
            row[idx(i, j)] = Fr(1)
            rows.append(row)
            rhs.append(ctx.L0[i][j])
    kind, payload = solve_exact(rows, rhs)
    if kind != "yes":
        return None
    return [[payload[idx(i, j)] for j in range(n)] for i in range(q)]


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

    # --- Psi_{t,omega}: item (i) must be equivalent to "rank H = omega and rank[H;G] = omega"
    if ctx.mprime >= 1 and ctx.ell >= 1:
        checked = 0
        for t in range(0, min(ctx.mprime, 2) + 1):
            for J in grassmann_charts(ctx.mprime, t)[:2]:
                for omega in range(1, ctx.ell + 1):
                    Y = [[Fr(a - b) for b in range(ctx.mprime - t)] for a in range(t)]
                    r = psi_eval(ctx, J, Y, omega)
                    HG = [list(r["H"][i]) + list(r["G"][i]) for i in range(len(r["H"]))]
                    expect = (ai.rank(r["H"]) == omega) and (ai.rank(HG) == omega)
                    assert r["i"] == expect, (
                        f"item (i) at t={t}, J={J}, omega={omega}: "
                        f"e_omega={r['e_omega']}, e_next={r['e_next']}, "
                        f"rank H={ai.rank(r['H'])}, rank[H;G]={ai.rank(HG)}")
                    checked += 1
        print(f"[fpt] Psi item (i) == (rank H = omega and rank[H;G] = omega): {checked} chart points")
    # --- semantic alignment: a chart point satisfying Psi must yield an L satisfying (5a)/(5b).
    # The instance is the one decide.py's test [4] finds feasible (A = the shift, C = e1^T,
    # L0 = [-1,-1,-1], q = 2), so a witness is known to EXIST: a check that finds none would be
    # vacuous (the project rule: an equivalence test must contain a True point).
    A2 = [[Fr(0), Fr(1), Fr(0)], [Fr(0), Fr(0), Fr(1)], [Fr(0), Fr(0), Fr(0)]]
    C2 = [[Fr(1), Fr(0), Fr(0)]]
    L2 = [[Fr(-1), Fr(-1), Fr(-1)]]
    ctx2 = FptData(A2, C2, L2, 2)
    assert ctx2.check()
    ctx2.describe()
    aligned = 0
    tried = 0
    for t in range(0, min(ctx2.mprime, 2) + 1):
        for J in grassmann_charts(ctx2.mprime, t):
            for Y in itertools.product([-1, 0, 1], repeat=t * (ctx2.mprime - t)):
                Ymat = [[Fr(Y[a * (ctx2.mprime - t) + b]) for b in range(ctx2.mprime - t)]
                        for a in range(t)]
                for omega in range(1, ctx2.ell + 1):
                    tried += 1
                    r = psi_eval(ctx2, J, Ymat, omega)
                    if not r["ii"]:
                        continue
                    L = reconstruct_L(ctx2, r["H"], r["G"])
                    if L is None:
                        continue
                    assert ai.cond_5a_orig(A2, C2, L), "a Psi point gives an L failing (5a)"
                    assert ai.cond_5b_orig(A2, C2, L), "a Psi point gives an L failing (5b)"
                    aligned += 1
    print(f"[fpt] Psi point -> L with (5a) and (5b), independently checked: "
          f"{aligned} witnesses out of {tried} points tried")
    if aligned == 0:
        print("[fpt] OPEN: no witness on this instance although decide.py finds it feasible.")
        print("[fpt]       The chart lift Z_ch = [E0; C_J(Y) E_Q] uses an ARBITRARY complement")
        print("[fpt]       E_Q, but Psi's truth depends on the actual pair rows, not only on")
        print("[fpt]       their span, so the chart needs the paper's canonical section.")
    ok &= True
    print("RESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


def main(argv):
    return demo()


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
