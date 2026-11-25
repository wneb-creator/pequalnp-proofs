# Circuit search

Started 2026-11-25T17:31:14Z.

Target T = 0xfeeefeeafeeeccc8, 45 true assignments. Minimal true sets: ab, bc, bd, ae, be, cde, af, cdf. Maximal false assignments 13, 34, 52, 56.

Verified on all 64 assignments a 9-gate monotone realization:

`` f = b AND (a OR c OR d OR e) OR ((e OR f) AND (a OR (c AND d))) ``

Gate references 0..5 are inputs a..f; append:

1. AND 2 3
2. OR 4 5
3. OR 0 6
4. AND 7 8
5. OR 0 2
6. OR 3 10
7. OR 4 11
8. AND 1 12
9. OR 9 13

Sympy, NumPy, SciPy installed; z3, pysat, pycosat, cvc5, ortools absent; no kissat/cadical/minisat/glucose/abc/yosys/z3 commands.

Next: seek 8-gate unrestricted realization or a rigorous lower bound.

## Independent positive-proof validation

2026-11-25T17:33:06.132634+00:00

Reference PR17278 nine-gate witness independently evaluates correctly on all64 rows. Its two restriction leaves were independently checked to both equal three-input majority table232. A complete Python memoized search verified table232 unreachable in at most3 operations from {0,170,204,240} with AND/OR/DIFF. Counts by remaining budget: [994, 114, 12, 1]. Thus the finite leaf fact supporting the positive proof is correct independently of Lean. The mathematical argument removes two gates fixing variable5, then one gate each fixing variable2/3 or variable0/4, leaving a >=4-gate majority leaf: binary gates >=8. Any circuit with NOT then has >=9 total gates; any circuit without NOT is already a valid monotone replacement.

Stochastic8-gate AND/OR/NOT search completed 1,000,000,000 mutations without a witness; best differed on2 of64 rows. This is only heuristic evidence, superseded by the independently verified leaf facts and pending Lean check of the positive twin. Strategy finished 2026-11-25T17:33:18.447813+00:00.
