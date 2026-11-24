# Debug and evidence scripts

These are **not** part of the test suite and are not run by CI.  They are the scripts that
localised concrete bugs during development, kept because each one is the evidence for a claim in
`docs/ALGORITHM_REVIEW.md` or in a commit message.

| script | status | what it was for |
|---|---|---|
| `debug_recon.py` | **runs** | localised the `E_0` bug: `W0` held a *normalised* basis `[[1,1]]` while `L0 M = [[-1,-1]]`, so pinning `L[0..r0] = L0` contradicted `L M = [H G]` and `reconstruct_L` returned `None` for every chart point. With the fix it prints `reconstruct_L -> [['-1','-1','-1'],['0','0','1']]`, the witness `decide.py` finds. |
| `inspect_witness.py` | **historical, broken** | an earlier attempt to print the witness `L`, `H`, `H_A` and their ranks. It fails with a `Fraction` type error, which is itself the record of a mistake in how I passed matrices around. Its purpose is now served by `debug_recon.py`. |
| `debug_inst2.py` | **historical, broken** | searched instance 2 with a denser `Y` grid and found that the "coverage miss" was my own missing `W0 = 0` shortcut, not a gap in Algorithm 2. It calls `test_fpt.search_psi`, which was removed when that test was rewritten to use `fpt.decide_fpt`. |

Scripts here import the modules one directory up via a `sys.path` bootstrap, so they can be run
from this directory:

```
python verification/debug/debug_recon.py
```

Nothing here is evidence of correctness; the correctness evidence is `verification/test_decide.py`,
`verification/test_fpt.py`, `verification/fpt.py --demo`, `verification/decide_r0.py --demo`, and
the Lean axiom audit.
