#!/usr/bin/env python3
"""test_decide.py -- tests for decide.py (Algorithm 1 of Paper I, end to end).

Run from the repository root:

    python verification/test_decide.py

Covers, as required:

  1. the q < r0 case                                              (infeasible)
  2. the h0 = g0 = 0 case                                         (feasible)
  3. the r = 0 branch, cross-checked against decide_r0
  4. a genuine r > 0 feasible instance, found by exhaustive search over small integer
     data, with the free rows genuinely needed (R = 0 fails)
  5. a genuine r > 0 infeasible instance, with a proof of infeasibility that does not go
     through decide.py (A N = 0 and L0 N != 0 force a rank drop at lambda = 0)
  6. the witness cross-check: every feasible verdict for r > 0 is re-verified against
     audit_independent.cond_5a_orig / cond_5b_orig (this is also done inside decide.py,
     here it is done again from the outside, on the returned L)
  7. edge cases: k = 0 (empty common kernel) and a q = n instance
  8. the three-valued API: a chart that can be neither refuted nor witnessed must not be
     reported as infeasible (see test_unknown_is_honest; it checks the API contract on the
     instances available, and is skipped with a printed note if none of the small
     instances leaves a chart undecided)

Every test prints the invariants it relies on (ranks, dimensions) before its verdict.
NOT a proof of anything: this is the exact-arithmetic regression suite of decide.py.
"""

from __future__ import annotations

import itertools
import sys
from fractions import Fraction as Fr

import audit_independent as ai
import decide as D
import decide_r0 as dec0


# ---------------------------------------------------------------- helpers

def build(A, C, L0):
    return ([[Fr(x) for x in row] for row in A],
            [[Fr(x) for x in row] for row in C],
            [[Fr(x) for x in row] for row in L0])


def brute_force_L(A, C, L0, q, grid):
    """Exhaustive search over free blocks with entries in ``grid`` (small instances only)."""
    r0, r, n = len(L0), q - len(L0), len(A)
    if r < 0:
        return None
    for combo in itertools.product(grid, repeat=r * n):
        R = [[Fr(combo[i * n + j]) for j in range(n)] for i in range(r)]
        L = [list(row) for row in L0] + R
        if ai.cond_5a_orig(A, C, L) and ai.cond_5b_orig(A, C, L):
            return L
    return None


def check_witness(A, C, L, tag):
    """The cross-check demanded by the task: (5a)/(5b) on the returned L."""
    assert L is not None, f"{tag}: feasible verdict without a witness"
    rk_base = ai.rank(ai.vstack([L, ai.mul(C, A), C]))
    rk_top = ai.rank(ai.vstack([ai.mul(L, A), L, ai.mul(C, A), C]))
    ok5a = ai.cond_5a_orig(A, C, L)
    ok5b = ai.cond_5b_orig(A, C, L)
    print(f"    witness L: {len(L)}x{len(L[0])}, rank[L;CA;C]={rk_base}, "
          f"rank[LA;L;CA;C]={rk_top}, (5a)={ok5a}, (5b)={ok5b}")
    assert ok5a and ok5b, f"{tag}: the returned L does not satisfy (5a) and (5b)"
    return ok5a and ok5b


# ---------------------------------------------------------------- 1. q < r0

def test_q_lt_r0():
    print("[1] q < r0")
    A, C, L0 = build([[0, 1], [0, 0]], [[1, 0]], [[0, 1], [1, 0]])
    q = 1
    print(f"    r0 = rows(L0) = {len(L0)}, q = {q}")
    assert q < len(L0)
    dec = D.decide(A, C, L0, q, verbose=False)
    print(f"    verdict: {dec.verdict}  ({dec.reason})")
    assert dec.verdict == "infeasible"
    assert dec.L is None
    return True


# ---------------------------------------------------------------- 2. h0 = g0 = 0

def test_h0_g0_zero():
    print("[2] h0 = g0 = 0 (step 4)")
    # A = 0, C = e1^T, L0 = e1^T: N spans ker C, so L0 N = 0 and L0 A N = 0.
    A, C, L0 = build([[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[1, 0, 0]], [[1, 0, 0]])
    q = 2
    N = ai.nullspace(ai.vstack([C, ai.mul(C, A)]))
    Nmat = [[N[j][i] for j in range(len(N))] for i in range(3)]
    h0 = ai.mul(L0, Nmat)
    g0 = ai.mul(L0, ai.mul(A, Nmat))
    print(f"    k = {len(N)}, h0 = {h0}, g0 = {g0}, q = {q}, r = {q - len(L0)}")
    assert all(v == 0 for row in h0 for v in row)
    assert all(v == 0 for row in g0 for v in row)
    dec = D.decide(A, C, L0, q, verbose=False)
    print(f"    verdict: {dec.verdict}  ({dec.reason})")
    assert dec.verdict == "feasible" and dec.L is not None
    check_witness(A, C, dec.L, "h0=g0=0")
    return True


# ---------------------------------------------------------------- 3. r = 0 branch

def test_r0_branch():
    print("[3] r = 0 branch, cross-checked against decide_r0")
    cases = [
        # (A, C, L0) -- the decide_r0 demo instances plus a couple more
        ([[0, 1, 0], [0, 0, 1], [0, 0, 0]], [[1, 0, 0]], [[-1, -1, -1], [-1, -1, 0]]),
        ([[0, 1, 0], [0, 0, 1], [0, 0, 0]], [[1, 0, 0]], [[0, 0, 1]]),
        ([[0, 1, 0], [0, 0, 1], [0, 0, 0]], [[1, 0, 0]], [[-1, -1, -1]]),
        ([[1, 0, 0], [0, 2, 0], [0, 0, 3]], [[1, 0, 0]], [[0, 1, 1]]),
        ([[0, 1, 0], [0, 0, 0], [0, 0, 0]], [[1, 0, 0]], [[1, 0, 1]]),
    ]
    checked = 0
    for Am, Cm, Lm in cases:
        A, C, L0 = build(Am, Cm, Lm)
        q = len(L0)                       # r = 0
        dec = D.decide(A, C, L0, q, verbose=False)
        ref = dec0.decide_r0(A, C, L0)
        print(f"    instance n={len(A)} r0={q}: decide={dec.verdict}, "
              f"decide_r0 feasible={ref.feasible} ((5a)={ref.cond5a}, (5b)={ref.cond5b})")
        assert dec.verdict == ("feasible" if ref.feasible else "infeasible"), \
            "decide and decide_r0 disagree on an r = 0 instance"
        if dec.verdict == "feasible":
            check_witness(A, C, dec.L, "r=0")
        checked += 1
    print(f"    {checked} r = 0 instances agree with decide_r0")
    # The one degenerate case where decide_r0 is incomplete: omega = 0 with H = H_A = 0.
    # prop:zero Step 2 accepts there, decide_r0.compress_r0 returns None and rejects.
    A, C, L0 = build([[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[1, 0, 0]], [[1, 0, 0]])
    dec = D.decide(A, C, L0, 1, verbose=False)
    ref = dec0.decide_r0(A, C, L0)
    print(f"    degenerate omega = 0, H = H_A = 0: decide={dec.verdict}, "
          f"decide_r0 feasible={ref.feasible} (must agree: the paper's omega = 0 case)")
    assert dec.verdict == "feasible"
    check_witness(A, C, dec.L, "r=0, omega=0")
    # Round 17: decide_r0 used to answer False here (a known gap); it now decides the degenerate
    # case with the original (5a)/(5b), so it must agree with decide.py.
    assert ref.feasible is True, "decide_r0 must accept the omega = 0 case when H = H_A = 0"
    return True


# ---------------------------------------------------------------- 4. genuine r > 0 feasible

def find_feasible_r_gt_0():
    """Exhaustive search over small integer data for a genuine r > 0 feasible instance.

    Search space: n = 3, p = 1, r0 = 1, q = 2 (so r = 1); C = e1^T; L0 and A over
    {-1,0,1} with A restricted to the nilpotent shift family and small perturbations; the
    free block R ranges over {-1,0,1}^3.  "Genuine" means: L = [L0; 0] fails (5a) or (5b),
    so a nonzero free row is really needed.
    """
    grid = (-1, 0, 1)
    As = [
        [[0, 1, 0], [0, 0, 1], [0, 0, 0]],
        [[0, 1, 0], [0, 0, 0], [0, 0, 0]],
        [[0, 0, 0], [0, 0, 1], [0, 0, 0]],
    ]
    Cs = [[[1, 0, 0]], [[0, 1, 0]], [[1, 1, 0]]]
    for Am in As:
        for Cm in Cs:
            A, C, _ = build(Am, Cm, [[0, 0, 0]])
            if ai.rank(C) < 1:
                continue
            for Lvec in itertools.product(grid, repeat=3):
                if all(v == 0 for v in Lvec):
                    continue
                A, C, L0 = build(Am, Cm, [list(Lvec)])
                q = 2
                if ai.rank(L0) != 1:
                    continue
                # L0 alone must fail, so that the free row is genuinely needed
                if ai.cond_5a_orig(A, C, L0) and ai.cond_5b_orig(A, C, L0):
                    continue
                W = brute_force_L(A, C, L0, q, grid)
                if W is not None:
                    return Am, Cm, list(Lvec)
    return None


def test_r_gt_0_feasible():
    print("[4] genuine r > 0 feasible instance (exhaustive search over small integer data)")
    found = find_feasible_r_gt_0()
    assert found is not None, "the exhaustive search found no instance"
    Am, Cm, Lvec = found
    print(f"    searched n=3, p=1, r0=1, q=2, entries in {{-1,0,1}}; found")
    print(f"    A = {Am}, C = {Cm}, L0 = {Lvec}")
    A, C, L0 = build(Am, Cm, [Lvec])
    q = 2
    N = ai.nullspace(ai.vstack([C, ai.mul(C, A)]))
    print(f"    k = dim ker[C;CA] = {len(N)}")
    # the witness the search found, checked independently
    W = brute_force_L(A, C, L0, q, (-1, 0, 1))
    check_witness(A, C, W, "brute-force witness L")
    # L0 alone fails, so r > 0 is really needed
    assert not (ai.cond_5a_orig(A, C, L0) and ai.cond_5b_orig(A, C, L0)), \
        "the instance is already feasible at r = 0"
    print(f"    L0 alone: (5a)={ai.cond_5a_orig(A, C, L0)}, "
          f"(5b)={ai.cond_5b_orig(A, C, L0)}  -> free rows are needed")
    dec = D.decide(A, C, L0, q, verbose=False)
    print(f"    decide: {dec.verdict}  ({dec.reason})")
    assert dec.verdict == "feasible" and dec.L is not None
    assert any(c.verdict == "sat" for c in dec.charts)
    check_witness(A, C, dec.L, "decide's L")
    return True


# ---------------------------------------------------------------- 5. genuine r > 0 infeasible

def test_r_gt_0_infeasible():
    print("[5] genuine r > 0 infeasible instance")
    # A = 0, C = e1^T, L0 = e2^T, q = 2.  For *every* L: LA = 0 and L A N = 0, hence
    # H_A = L A N = 0.  (5b) at lambda = 0 then reads rank(-H_A) = rank H, i.e.
    # 0 = rank H; but h0 = L0 N != 0 forces rank H >= 1.  So the instance is infeasible
    # for every q >= r0, independently of decide.py.
    A, C, L0 = build([[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[1, 0, 0]], [[0, 1, 0]])
    q = 2
    N = ai.nullspace(ai.vstack([C, ai.mul(C, A)]))
    Nmat = [[N[j][i] for j in range(len(N))] for i in range(3)]
    AN = ai.mul(A, Nmat)
    h0 = ai.mul(L0, Nmat)
    print(f"    k = {len(N)}; A N = {AN}; L0 N = {h0}")
    assert all(v == 0 for row in AN for v in row), "the proof needs A N = 0"
    assert any(v != 0 for row in h0 for v in row), "the proof needs h0 != 0"
    print("    proof: H_A = L A N = 0 for every L, so (5b) at lambda=0 forces rank H = 0, "
          "while h0 != 0 forces rank H >= 1")
    # supporting exhaustive evidence (not the proof)
    W = brute_force_L(A, C, L0, q, (-2, -1, 0, 1, 2))
    print(f"    exhaustive search over R in {{-2..2}}^(1x3): {'witness found' if W else 'none'}")
    assert W is None
    dec = D.decide(A, C, L0, q, verbose=False)
    print(f"    decide: {dec.verdict}  ({dec.reason})")
    assert dec.verdict == "infeasible"
    assert dec.charts and all(c.verdict == "unsat" for c in dec.charts)
    print(f"    {len(dec.charts)} charts, all refuted: "
          f"{[c.certificate.split(':')[0] for c in dec.charts]}")
    return True


# ---------------------------------------------------------------- 6/7. edge cases

def test_k_zero():
    print("[7a] k = 0 (empty common kernel)")
    # C = I_2 makes ker[C; CA] = 0; then h0 and g0 are empty and step 4 applies.
    A, C, L0 = build([[1, 2], [0, 1]], [[1, 0], [0, 1]], [[1, 1]])
    q = 2
    N = ai.nullspace(ai.vstack([C, ai.mul(C, A)]))
    print(f"    n = 2, p = 2, k = {len(N)}, r0 = 1, q = 2")
    assert len(N) == 0
    dec = D.decide(A, C, L0, q, verbose=False)
    print(f"    verdict: {dec.verdict}")
    assert dec.verdict == "feasible"
    check_witness(A, C, dec.L, "k=0")
    return True


def test_q_equals_n():
    print("[7b] q = n")
    A, C, L0 = build([[0, 1, 0], [0, 0, 1], [0, 0, 0]], [[1, 0, 0]], [[-1, -1, -1]])
    q = 3
    dec = D.decide(A, C, L0, q, verbose=False)
    print(f"    n = 3, r0 = 1, q = 3: verdict {dec.verdict}")
    assert dec.verdict in ("feasible", "infeasible", "unknown")
    if dec.verdict == "feasible":
        check_witness(A, C, dec.L, "q=n")
    return True


# ---------------------------------------------------------------- 8. three-valued API

def test_three_valued_api():
    print("[8] three-valued API")
    A, C, L0 = build([[0, 1, 0], [0, 0, 1], [0, 0, 0]], [[1, 0, 0]], [[-1, -1, -1]])
    dec = D.decide(A, C, L0, 2, verbose=False)
    assert dec.verdict in ("feasible", "infeasible", "unknown")
    if dec.verdict == "unknown":
        assert dec.undecided, "an unknown verdict must list the undecided charts"
        assert all(c.verdict == "unknown" for c in dec.undecided)
        assert dec.L is None
        print(f"    unknown verdict lists {len(dec.undecided)} undecided chart(s)")
    else:
        print(f"    verdict {dec.verdict!r} is one of the three values; "
              f"{len(dec.charts)} chart outcomes recorded")
        assert all(c.verdict in ("sat", "unsat", "unknown") for c in dec.charts)
        assert all(c.certificate or c.verdict == "sat" for c in dec.charts)
    # an infeasible verdict must be backed by refutations of every chart, never by silence
    A2, C2, L02 = build([[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[1, 0, 0]], [[0, 1, 0]])
    dec2 = D.decide(A2, C2, L02, 2, verbose=False)
    assert dec2.verdict == "infeasible"
    assert dec2.charts and all(c.verdict == "unsat" and c.certificate for c in dec2.charts)
    print("    infeasible verdict: every chart carries an explicit refutation")
    return True


# ---------------------------------------------------------------- main

def main():
    tests = [
        test_q_lt_r0,
        test_h0_g0_zero,
        test_r0_branch,
        test_r_gt_0_feasible,
        test_r_gt_0_infeasible,
        test_k_zero,
        test_q_equals_n,
        test_three_valued_api,
    ]
    failed = 0
    for test in tests:
        try:
            ok = test()
        except AssertionError as exc:
            ok = False
            print(f"    FAILED: {exc}")
        failed += not ok
        print()
    print("=" * 74)
    print(f"RESULT: {'PASS' if failed == 0 else 'FAIL'} "
          f"({len(tests) - failed}/{len(tests)} tests)")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
