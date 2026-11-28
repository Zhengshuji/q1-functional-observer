#!/usr/bin/env python3
"""Exact checks for Paper V: the fibre criterion and the three examples of §V.

The script drives `verification/fibre.py` on the three instances the paper uses:

  * Example 1 (a feasible fibre at t = 2): the gcd of the 2-minors is 1, degree 0;
  * Example 2 (a bad point): the gcd is λ + 3, independent of the fibre parameters, so
    the whole fibre is bad and the point is bad while its neighbours are feasible;
  * Example 3 (the thin region): with Z'' = 0, U = U_0 = span(e₁) and d' = 1 < q = 2 the
    fibre is feasible although d' + t - k = 0 < s = 1.

Each instance is asserted before it is decided: the ranks, the dimension of `T ∩ U` and
the nonemptiness of the fibre are checked first, so a wrong model fails loudly.

This is finite exact verification, not a proof; the machine-checked part of the paper is
`Q1Paper/PaperV/Fibre.lean` (Theorem 1) and `Q1Paper/PaperV/Specialize.lean` (Lemma 2).
"""

from __future__ import annotations

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import fibre  # noqa: E402  (the shared checker of Paper V)


def main() -> int:
    return fibre.main()


if __name__ == "__main__":
    sys.exit(main())
