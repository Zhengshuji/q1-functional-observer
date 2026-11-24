import os
import sys

# these scripts live in verification/debug/ but import the modules one level up
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from fractions import Fraction as Fr

import audit_independent as ai
import fpt

A = [[Fr(0), Fr(1), Fr(0)], [Fr(0), Fr(0), Fr(1)], [Fr(0), Fr(0), Fr(0)]]
C = [[Fr(1), Fr(0), Fr(0)]]
L0 = [[Fr(-1), Fr(-1), Fr(-1)]]

ctx = fpt.FptData(A, C, L0, 2)
ctx.describe()
print("M =", [[str(x) for x in r] for r in ctx.M])
print("W0 =", [[str(x) for x in r] for r in ctx.W0])
print("V =", [[str(x) for x in r] for r in ctx.V])

for t in range(0, min(ctx.mprime, 2) + 1):
    for J in fpt.grassmann_charts(ctx.mprime, t):
        for Yt in __import__("itertools").product([-1, 0, 1], repeat=t * (ctx.mprime - t)):
            Y = [[Fr(Yt[a * (ctx.mprime - t) + b]) for b in range(ctx.mprime - t)]
                 for a in range(t)]
            r = fpt.psi_eval(ctx, J, Y, 1)
            print(f"t={t} J={J} Y={Yt}: i={r['i']} (e_w={r['e_omega']}, e_next={r['e_next']}) "
                  f"ii={r['ii']}")
            if r["ii"]:
                L = fpt.reconstruct_L(ctx, r["H"], r["G"])
                print("   reconstruct_L ->", None if L is None else
                      [[str(x) for x in row] for row in L])
