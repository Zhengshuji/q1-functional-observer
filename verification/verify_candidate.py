#!/usr/bin/env python3
"""verify_candidate.py -- check one candidate observer against the paper's two conditions.

Given `A` (n x n), `C` (p x n) and a candidate observer `L = [L0; R]` (q x n), decide with
exact rational arithmetic whether `L` satisfies

  (5a)  rank[LA; L; CA; C] = rank[L; CA; C]
  (5b)  the gcd of the r0-order minors of [lambda L - LA; CA; C] is a nonzero constant
        (r0 = rank[L; CA; C]); equivalently the pencil keeps full column rank at every
        complex lambda.

The verdict is `DEC` when both hold.  The point of this script is not to re-prove anything:
it packages the *independent* implementation in `audit_independent.py` (Fraction linear
algebra and exact polynomial gcd, no sympy, no project code) behind a documented entry
point that a reader can run on their own instance.

Following the project's rule for certificate scripts, the basic invariants are printed and
asserted BEFORE any verdict is drawn, so a malformed input trips an assertion instead of
producing a confident wrong answer.

Usage
-----
    python verify_candidate.py                 # two worked examples (one DEC, one not)
    python verify_candidate.py instance.json   # {"A": .., "C": .., "L0": .., "R": .., "expect": bool}

Exit status: 0 if every checked instance agrees with its expectation, 1 on a mismatch,
2 on malformed input.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction as Fr

import audit_independent as ai


def _parse(M):
    return [[Fr(x) for x in row] for row in M]


def verify(A, C, L, expect=None, label="instance"):
    """Check (5a) and (5b) for `L`; return True iff the verdict matches `expect` (or is True)."""
    n, p, q = ai.cols(A), ai.rows(C), ai.rows(L)

    # ---- invariants first: shapes, then the ranks the conditions refer to ----
    assert ai.rows(A) == n, f"A must be square, got {ai.rows(A)} x {n}"
    assert ai.cols(C) == n and ai.cols(L) == n, "C and L must have exactly n columns"
    base_rank = ai.rank(ai.vstack([L, ai.mul(C, A), C]))
    assert base_rank <= min(q + 2 * p, n), "rank cannot exceed the number of rows or columns"
    print(f"[{label}] n={n} p={p} q={q}  rank[L;CA;C]={base_rank}")

    ok5a = ai.cond_5a_orig(A, C, L)
    ok5b = ai.cond_5b_orig(A, C, L)
    print(f"  (5a) {'PASS' if ok5a else 'FAIL'}   (5b) {'PASS' if ok5b else 'FAIL'}")
    dec = ok5a and ok5b
    print(f"  -> DEC = {dec}")

    if expect is not None and dec != expect:
        print(f"  MISMATCH: expected DEC = {expect}")
        return False
    return True


# A_shift is the nilpotent Jordan block, so the reachable chain from e1 is e1, e2, e3.
_A_SHIFT = [[0, 1, 0], [0, 0, 1], [0, 0, 0]]


def demo():
    ok = True
    # feasible: L = e1^T observes the first coordinate; the reachable pair chain has full
    # rank on the observed part, and the pencil keeps column rank at every lambda.
    ok &= verify(_parse(_A_SHIFT), _parse([[1, 0, 0]]), _parse([[1, 0, 0]]),
                 expect=True, label="feasible example")
    # infeasible: L = e1^T but C = e3^T observes only the last coordinate, so LA = e2^T is
    # not in row[L; CA; C] (CA = e3^T A = 0) and (5a) fails.
    ok &= verify(_parse(_A_SHIFT), _parse([[0, 0, 1]]), _parse([[1, 0, 0]]),
                 expect=False, label="infeasible example")
    print("RESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


def main(argv):
    if len(argv) == 1:
        return demo()
    path = argv[1]
    try:
        with open(path, encoding="utf-8") as handle:
            data = json.load(handle)
        A = _parse(data["A"])
        C = _parse(data["C"])
        L0 = _parse(data["L0"])
        R = _parse(data.get("R", []))
    except (OSError, KeyError, ValueError) as exc:
        print(f"malformed instance {path!r}: {exc}", file=sys.stderr)
        return 2
    L = L0 + R
    return 0 if verify(A, C, L, data.get("expect"), label=path) else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
