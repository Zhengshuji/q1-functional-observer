import Q1Paper.PaperII.MainTheorems
import Q1Paper.PaperII.Complexity
/-
Q1Paper/PaperII/Read/S07_Algorithms.lean

§V  The algorithmic part of the interface theorem: the call count and OPT.

This file contains **no proofs**: a reading entry in proof order, one `#check` per step.

## What it consumes

The decision problem `DEC` of the paper and `tMin`/`tMinC` (`S03`), together with the a priori
bound `t_min <= 2 ell` and the spectral lower bound (`S04`).

## What it proves

1. **The count is logarithmic.**  `half_width` (one halving step keeps at most half the
   interval), `lt_two_pow_log2_succ`, `div_two_pow_log2_succ_eq_zero`, `bisect_steps_le` and
   `log2_mono_le` reduce the counting to arithmetic.
2. **The algorithm.**  `bisectGo` performs the bisection with an explicit fuel; `bisectGo_spec`
   bounds the interval by `(hi - lo) / 2 ^ k` and `bisectGo_collapses` shows that
   `log2 (hi - lo) + 1` halvings leave a single point.
3. **Correctness.**  `bisectGo_invariant` keeps the threshold invariant and `bisectGo_finds`
   returns the least point satisfying a monotone predicate.
4. **OPT.**  `tMin_eq_bisectGo` (complex designs) and `tMinC_eq_bisectGo` (real designs) identify
   the minimum order with the point returned by bisection on the decision predicate over
   `[0, 2 ell]`, so `t_min` is computed with `log2 (2 ell) + 1` calls.

## The result

- `Q1Paper.PaperII.half_width`, `lt_two_pow_log2_succ`, `div_two_pow_log2_succ_eq_zero`,
  `bisect_steps_le`, `log2_mono_le`
- `Q1Paper.PaperII.bisectGo`, `bisectGo_spec`, `bisectGo_collapses`
- `Q1Paper.PaperII.bisectGo_invariant`, `bisectGo_finds`
- `Q1Paper.PaperII.tMin_eq_bisectGo`, `tMinC_eq_bisectGo`
-/

#check @Q1Paper.PaperII.half_width
#check @Q1Paper.PaperII.lt_two_pow_log2_succ
#check @Q1Paper.PaperII.div_two_pow_log2_succ_eq_zero
#check @Q1Paper.PaperII.bisect_steps_le
#check @Q1Paper.PaperII.log2_mono_le
#check @Q1Paper.PaperII.bisectGo
#check @Q1Paper.PaperII.bisectGo_spec
#check @Q1Paper.PaperII.bisectGo_collapses
#check @Q1Paper.PaperII.bisectGo_invariant
#check @Q1Paper.PaperII.bisectGo_finds
#check @Q1Paper.PaperII.tMin_eq_bisectGo
#check @Q1Paper.PaperII.tMinC_eq_bisectGo
