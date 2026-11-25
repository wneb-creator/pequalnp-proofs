Small-row CEGIS experiment, 2026-11-25 UTC

This is an incomplete counterexample search, not a circuit lower-bound proof.
The script uses the reviewed parent search/synth.py encoder and the same local
CaDiCaL shared wrapper as the previous SAT experiment. It begins with the fifteen
edge-positive rows, fifteen maximal-independent negative rows, and rows 0/1023.
Each candidate is checked independently on all 1024 assignments, and failing rows
are added incrementally while retaining learned clauses. The final two outputs
must also have nonempty exclusive witness sets before a candidate can refute the
posted gap.

Both runs fixed the first gate to OR(input0,input2), required a final OR of the
last two earlier outputs, and enabled the prior ordering heuristic. These
restrictions are search choices, not proved complete normal forms.

The 20-gate monotone control timed out after 90 seconds in round zero, returning
UNKNOWN. The 19-gate at-most-one-NOT run timed out after 240 seconds in round zero,
also UNKNOWN. Neither run produced a candidate, an exhaustive result, or a
certificate. The full stdout/stderr logs are preserved without truncation.

The review is results/orch/review-root-cegis.txt. Its minor final-status logging
caveat did not arise in these runs: both print an explicit UNKNOWN result.
