import os
import sys

# these scripts live in verification/debug/ but import the modules one level up
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from fractions import Fraction as Fr

import audit_independent as ai
import fpt
import test_fpt as T

A = [[Fr(0), Fr(1), Fr(0)], [Fr(0), Fr(0), Fr(1)], [Fr(0), Fr(0), Fr(0)]]
C = [[Fr(1), Fr(0), Fr(0)]]
L0 = [[Fr(1), Fr(0), Fr(0)]]

ctx = fpt.FptData(A, C, L0, 2)
ctx.describe()
print("W0rows =", [[str(x) for x in r] for r in ctx.W0rows])
print("s0 =", ctx.s0, " m' =", ctx.mprime, " r =", ctx.r, " ell =", ctx.ell)

GRID = [Fr(-2), Fr(-1), Fr(-1, 2), Fr(0), Fr(1, 2), Fr(1), Fr(2)]
tmax = min(ctx.mprime, ctx.r, 2 * ctx.ell)
print("tmax =", tmax)

hits = T.search_psi(ctx, grid=GRID)
print("hits with the dense grid:", len(hits))
for (J, Yflat, omega, H, G) in hits:
    L = fpt.reconstruct_L(ctx, H, G)
    print("  J =", J, "Y =", Yflat, "omega =", omega, "-> L =",
          None if L is None else [[str(x) for x in r] for r in L])
