import os
import sys

# these scripts live in verification/debug/ but import the modules one level up
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from fractions import Fraction as Fr

import audit_independent as ai
import decide

A = [[Fr(0), Fr(1), Fr(0)], [Fr(0), Fr(0), Fr(1)], [Fr(0), Fr(0), Fr(0)]]
C = [[Fr(1), Fr(0), Fr(0)]]
L0 = [[Fr(-1), Fr(-1), Fr(-1)]]

d = decide.decide(A, C, L0, 2, verbose=False)
print("verdict:", getattr(d, "verdict", d), " L is None:", d.L is None)
if d.L is None:
    raise SystemExit(0)
L = d.L
print("L =", [[str(x) for x in r] for r in L])

Ncol = ai.nullspace([list(r) for r in C] + [list(ai.mul(C, A))])
k = len(Ncol)
Nmat = [[Ncol[j][i] for j in range(k)] for i in range(3)]
H = ai.mul(L, Nmat)
HA = ai.mul(ai.mul(L, A), Nmat)
print("N (n x k) =", [[str(x) for x in r] for r in Nmat])
print("H  =", [[str(x) for x in r] for r in H], " rank", ai.rank(H))
print("HA =", [[str(x) for x in r] for r in HA], " rank", ai.rank(HA))
print("rank[H;HA] =", ai.rank([list(h) + list(ha) for h, ha in zip(H, HA)]))
