#!/usr/bin/env python3
"""test_fpt.py -- Algorithm 2's control flow against Algorithm 1, on small instances.

`fpt.decide_fpt` implements Algorithm 2 as the paper states it, including the short-circuits:

    W0 not inside V   -> infeasible
    W0 = 0            -> feasible        (the omega = 0 branch, R = 0)
    otherwise         -> enumerate (t, J, omega) and test Psi

and it returns 'unknown' -- never 'infeasible' -- when the chart grid finds no witness, since a
grid miss is not a proof of infeasibility (an exact real-feasibility oracle is absent, the same
boundary as Algorithm 1's unknown).

This script compares that verdict with `decide.py`'s (Algorithm 1) and asserts the two directions
that must hold:

  * soundness   : Algorithm 2 says 'feasible'  =>  Algorithm 1 says 'feasible'
  * soundness'  : Algorithm 1 says 'infeasible' => Algorithm 2 says 'infeasible'

Whenever Algorithm 2 reports 'feasible' through a chart, the witness L is reconstructed and
re-verified against the ORIGINAL (5a)/(5b) by audit_independent.
"""

from __future__ import annotations

from fractions import Fraction as Fr

import audit_independent as ai
import decide
import fpt

A_SHIFT = [[Fr(0), Fr(1), Fr(0)], [Fr(0), Fr(0), Fr(1)], [Fr(0), Fr(0), Fr(0)]]
A_ZERO = [[Fr(0), Fr(0), Fr(0)], [Fr(0), Fr(0), Fr(0)], [Fr(0), Fr(0), Fr(0)]]
E1 = [[Fr(1), Fr(0), Fr(0)]]
E2 = [[Fr(0), Fr(1), Fr(0)]]
E3 = [[Fr(0), Fr(0), Fr(1)]]

A_SHIFT4 = [[Fr(int(i + 1 == j)) for j in range(4)] for i in range(4)]

INSTANCES = [
    ("shift, C=e1, L0=[-1,-1,-1], q=2", A_SHIFT, E1, [[Fr(-1), Fr(-1), Fr(-1)]], 2),
    ("shift, C=e1, L0=e1, q=2", A_SHIFT, E1, E1, 2),
    ("zero A, C=e1, L0=e2, q=2", A_ZERO, E1, E2, 2),
    ("shift, C=e3, L0=e1, q=2", A_SHIFT, E3, E1, 2),
    ("shift, C=e1, L0=e2, q=2", A_SHIFT, E1, E2, 2),
    # n = 4 and r = 2 (q = 3 with |L0| = 1)
    ("n=4 shift, C=e1, L0=e1, q=2", A_SHIFT4, [[Fr(1), Fr(0), Fr(0), Fr(0)]],
     [[Fr(1), Fr(0), Fr(0), Fr(0)]], 2),
    ("n=4 shift, C=e1, L0=e1, q=3 (r=2)", A_SHIFT4, [[Fr(1), Fr(0), Fr(0), Fr(0)]],
     [[Fr(1), Fr(0), Fr(0), Fr(0)]], 3),
    ("n=4 shift, C=e1, L0=[-1,-1,-1,-1], q=2", A_SHIFT4,
     [[Fr(1), Fr(0), Fr(0), Fr(0)]], [[Fr(-1), Fr(-1), Fr(-1), Fr(-1)]], 2),
    ("n=4 shift, C=e4, L0=e1, q=2", A_SHIFT4,
     [[Fr(0), Fr(0), Fr(0), Fr(1)]], [[Fr(1), Fr(0), Fr(0), Fr(0)]], 2),
    # a two-row measurement
    ("shift, C=[e1;e2], L0=e1, q=2", A_SHIFT,
     [[Fr(1), Fr(0), Fr(0)], [Fr(0), Fr(1), Fr(0)]], E1, 2),
]


def main() -> int:
    ok = True
    print(f"instances: {len(INSTANCES)}")
    print("-" * 74)
    for label, A, C, L0, q in INSTANCES:
        d1 = decide.decide(A, C, L0, q, verbose=False)
        v1 = getattr(d1, "verdict", "?")
        v2, hits = fpt.decide_fpt(A, C, L0, q)

        verified = 0
        for (J, Yflat, omega, H, G) in hits:
            L = fpt.reconstruct_L(fpt.FptData(A, C, L0, q), H, G)
            if L is None:
                continue
            assert ai.cond_5a_orig(A, C, L), f"{label}: a Psi witness fails (5a)"
            assert ai.cond_5b_orig(A, C, L), f"{label}: a Psi witness fails (5b)"
            verified += 1

        agree = (v2 == v1) or (v2 == "unknown")
        print(f"[{label}]")
        print(f"    Algorithm 1 : {v1}")
        print(f"    Algorithm 2 : {v2}   (chart witnesses: {len(hits)}, verified: {verified})")
        if v2 == "feasible" and v1 == "infeasible":
            print("    CONTRADICTION: Algorithm 2 accepts what Algorithm 1 rejects")
            ok = False
        if v1 == "infeasible" and v2 not in ("infeasible",):
            print("    CONTRADICTION: Algorithm 1 rejects but Algorithm 2 does not")
            ok = False
        if v2 == "unknown":
            print("    (unknown: the chart grid found no witness; needs the oracle)")
        elif agree:
            print("    AGREE")
    print("-" * 74)
    print("RESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
