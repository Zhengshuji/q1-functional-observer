#!/usr/bin/env python3
"""Exact check for Example 20 of Paper V: the bad set is not closed on the Grassmannian.

The example has two halves, and both are decided here in exact rational arithmetic.

* The chart `U_eps = span(e1, e2 + eps e3)` with `eps != 0` has `a = dim(U ∩ T) = 1`.
  Every compatible point of the chart is bad: the rows of `H Z''` and every admissible
  fibre row lie in `T ∩ U = C e1`, so at `lambda_0 = 0` the matrix `-(H Z'' + G')` has
  rank at most 1 < d' = 2 for *every* fibre point.  The script checks the stronger
  symbolic statement: with the fibre parametrised by `y`, every 2-minor of
  `P(0) = -(H Z'' + G'(y))` vanishes identically in `y`.

* The limit point `U* = T` has `a = 2`, is compatible, and is feasible: the explicit
  witness `G'` below makes the gcd of the 18 2-minors of `lambda H - H Z'' - G'` a
  nonzero constant.

This is finite exact verification of the instance, not a proof.  It asserts the ranks,
the intersection dimensions and the fibre membership of the witness before deciding, so
a wrong model fails loudly.  The paper's proof of the general statement is in the text;
the machine-checked part of Paper V is in `Q1Paper/PaperV/`.
"""

from __future__ import annotations

import itertools
import pathlib
import sys

import sympy as sp

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import fibre  # noqa: E402  (the shared fibre model of Paper V)

LAM = sp.symbols("lambda")


def minors_of(H, Z, G, d):
    """All `d`-minors of `lambda H - H Z - G`, as expanded polynomials in `lambda`."""
    P = LAM * H - H * Z - G
    return [sp.expand(P[list(rs), list(cs)].det())
            for rs in itertools.combinations(range(H.rows), d)
            for cs in itertools.combinations(range(H.cols), d)]


def gcd_degree(minors):
    nonzero = [m for m in minors if sp.expand(m) != 0]
    assert nonzero, "degenerate input: every minor vanishes identically"
    g = nonzero[0]
    for m in nonzero[1:]:
        g = sp.gcd(g, m)
    return sp.degree(g, LAM), g


def intersection_dim(U, T):
    """dim(row U ∩ row T) from the rank formula."""
    return U.rank() + T.rank() - sp.Matrix.vstack(U, T).rank()


def main() -> int:
    # ---- the chart: a = 1, every fibre point bad -------------------------------
    # k = 4, q = 3, d' = 2, T = span(e1, e2), Z'' = e1 e1^T, U = span(e1, e2 + e3).
    H = sp.Matrix([[1, 0, 0, 0],
                   [0, 1, 1, 0],
                   [1, 1, 1, 0]])          # rows e1, e2 + e3, e1 + e2 + e3
    Z = sp.zeros(4, 4)
    Z[0, 0] = 1
    T = sp.Matrix([[1, 0, 0, 0],
                   [0, 1, 0, 0]])

    assert H.rank() == 2, "chart: the compressed rank must be d' = 2"
    assert T.rank() == 2, "chart: dim T must be 2"
    assert intersection_dim(H, T) == 1, "chart: a = dim(U ∩ T) must be 1"
    assert sp.Matrix.vstack(H, T).rank() == 3, "chart: U + T must be proper (U ≠ T)"

    G, _params = fibre.fibre(H, Z, T)
    assert G is not None, "chart: the fibre must be nonempty"

    # Every admissible row lies in T ∩ U = C e1 (columns 2..4 vanish identically).
    for i in range(G.rows):
        for j in range(1, 4):
            assert sp.simplify(G[i, j]) == 0, \
                f"chart: fibre row {i} leaves T ∩ U = C e1"

    P0 = sp.expand(-(H * Z) - G)
    chart_minors = [sp.expand(P0[list(rs), list(cs)].det())
                    for rs in itertools.combinations(range(P0.rows), 2)
                    for cs in itertools.combinations(range(P0.cols), 2)]
    assert len(chart_minors) == 18
    for m in chart_minors:
        assert sp.simplify(m) == 0, "chart: a 2-minor at lambda = 0 is not identically zero"
    print("chart U_eps (a=1):     every 2-minor vanishes at lambda=0 for all fibre points")

    # ---- the limit point: a = 2, compatible and feasible -----------------------
    H2 = sp.Matrix([[1, 0, 0, 0],
                    [0, 1, 0, 0],
                    [1, 1, 0, 0]])          # row space = T
    assert H2.rank() == 2, "limit: the compressed rank must be d' = 2"
    assert intersection_dim(H2, T) == 2, "limit: a = dim(U* ∩ T) must be 2"
    assert sp.Matrix.vstack(H2, T).rank() == 2, "limit: row H2 must equal T"

    # Compatibility U* Z'' ⊆ U*: each row of H2 Z lies in row H2.
    HZ = H2 * Z
    assert sp.Matrix.vstack(H2, HZ).rank() == 2, "limit: U* Z'' is not contained in U*"

    Gstar = sp.Matrix([[0, 0, 0, 0],
                       [0, 0, 0, 0],
                       [2, 1, 0, 0]])
    # Fibre membership: row i of Gstar lies in T ∩ (U* - (H2 Z)_i).
    for i in range(3):
        stacked = sp.Matrix.vstack(T, H2)
        assert sp.Matrix.vstack(stacked, Gstar.row(i)).rank() == 2, \
            f"limit: witness row {i} is not in T"
        assert sp.Matrix.vstack(stacked, Gstar.row(i) + HZ.row(i)).rank() == 2, \
            f"limit: witness row {i} does not satisfy the fibre equation"

    minors = minors_of(H2, Z, Gstar, 2)
    assert len(minors) == 18, "limit: there must be 18 2-minors"
    deg, g = gcd_degree(minors)
    assert deg == 0, f"limit: U* must be feasible, got gcd degree {deg}"
    print(f"limit U* = T (a=2):    gcd of the 18 2-minors = {sp.factor(g)}, degree 0")

    print("PASS: the bad set is not closed (Example 20)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
