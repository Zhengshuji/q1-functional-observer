#!/usr/bin/env python3
"""test_fpt.py -- end-to-end agreement between the Algorithm 2 front end and Algorithm 1.

For each small instance this script searches every Grassmann chart of the front end over a small
grid of chart coordinates, and for every point where Psi holds it reconstructs an observer L and
re-verifies it against the ORIGINAL conditions with the independent checker
(`audit_independent.cond_5a_orig` / `cond_5b_orig`).

The hard direction asserted is SOUNDNESS of the front end:

    a Psi witness exists  =>  decide.py does not report the instance infeasible

The other direction (decide says feasible => a Psi witness is found) is reported but not asserted,
because the front end's search is a finite grid and can miss points; a miss there is a coverage
statement, not a contradiction.

Every arithmetic step is fractions.Fraction.
"""

from __future__ import annotations

import itertools
import sys

from fractions import Fraction as Fr

import audit_independent as ai
import decide
import fpt

A_SHIFT = [[Fr(0), Fr(1), Fr(0)], [Fr(0), Fr(0), Fr(1)], [Fr(0), Fr(0), Fr(0)]]
A_ZERO = [[Fr(0), Fr(0), Fr(0)], [Fr(0), Fr(0), Fr(0)], [Fr(0), Fr(0), Fr(0)]]

INSTANCES = [
    ("shift, C=e1, L0=[-1,-1,-1], q=2", A_SHIFT,
     [[Fr(1), Fr(0), Fr(0)]], [[Fr(-1), Fr(-1), Fr(-1)]], 2),
    ("shift, C=e1, L0=e1, q=2", A_SHIFT,
     [[Fr(1), Fr(0), Fr(0)]], [[Fr(1), Fr(0), Fr(0)]], 2),
    ("zero A, C=e1, L0=e2, q=2", A_ZERO,
     [[Fr(1), Fr(0), Fr(0)]], [[Fr(0), Fr(1), Fr(0)]], 2),
    ("shift, C=e3, L0=e1, q=2", A_SHIFT,
     [[Fr(0), Fr(0), Fr(1)]], [[Fr(1), Fr(0), Fr(0)]], 2),
]


def search_psi(ctx, grid=(-1, 0, 1)):
    """Yield (J, Y, omega, H, G) for every chart point where Psi holds."""
    hits = []
    for t in range(0, min(ctx.mprime, 2) + 1):
        for J in fpt.grassmann_charts(ctx.mprime, t):
            width = ctx.mprime - t
            for Yflat in itertools.product(grid, repeat=t * width):
                Y = [[Fr(Yflat[a * width + b]) for b in range(width)] for a in range(t)]
                for omega in range(1, ctx.ell + 1):
                    r = fpt.psi_eval(ctx, J, Y, omega)
                    if r["i"] and r["ii"]:
                        hits.append((J, Yflat, omega, r["H"], r["G"]))
    return hits


def main() -> int:
    ok = True
    print(f"instances: {len(INSTANCES)}")
    print("-" * 72)
    for label, A, C, L0, q in INSTANCES:
        d = decide.decide(A, C, L0, q, verbose=False)
        verdict = getattr(d, "verdict", "?")
        ctx = fpt.FptData(A, C, L0, q)
        ctx.check()
        if not ctx.w0_in_v:
            # Algorithm 2's step 5/6 test: W0 not inside V => infeasible, no chart to search
            print(f"[{label}]")
            print(f"    decide.py verdict : {verdict}")
            print("    W0 not inside V   : Algorithm 2 rejects at step 6 (infeasible)")
            if verdict == "feasible":
                print("    CONTRADICTION: the paper's step-6 test rejects a feasible instance")
                ok = False
            else:
                print("    AGREE (both reject)")
            continue
        hits = search_psi(ctx)
        verified = 0
        for (J, Yflat, omega, H, G) in hits:
            L = fpt.reconstruct_L(ctx, H, G)
            if L is None:
                continue
            assert ai.cond_5a_orig(A, C, L), f"{label}: Psi witness fails (5a)"
            assert ai.cond_5b_orig(A, C, L), f"{label}: Psi witness fails (5b)"
            verified += 1
        print(f"[{label}]")
        print(f"    decide.py verdict : {verdict}")
        print(f"    Psi witnesses     : {len(hits)}  (reconstruct+verify ok: {verified})")
        if hits and verdict == "infeasible":
            print("    CONTRADICTION: a Psi witness exists but decide.py says infeasible")
            ok = False
        if not hits and verdict == "feasible":
            print("    coverage miss: decide.py is feasible but the grid found no witness")
        if hits and verdict == "feasible":
            print("    AGREE (both feasible)")
    print("-" * 72)
    print("RESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
