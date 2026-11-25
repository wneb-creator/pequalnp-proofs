Partial Lean strategy

2026-11-25: Drafted results/orch/lemmas/Partial.lean with finite Petersen invariants:
- 15 distinct edges.
- Triangle-free and square-free.
- Maximum independent set size 4, with witness {0,2,8,9}.
- Every vertex cover has at least 6 vertices.
- Every one of the ten input variables is essential, with explicit singleton/pair witnesses.

The finite propositions use Lean kernel decision only. No compilation yet: toolchain setup is in progress. These are supporting facts, not the posted circuit lower bound.

Added explicit 20-gate circuit (six stars followed by five OR joins). Python independently verifies its output on all 1024 assignments. Lean validation pending cache completion.

First complete checked partial: /tmp/oec/pequalnp-pilot-103/Graph.lean. `lake env lean` exited 0; graph-first.stdout and graph-first.stderr are empty. It contains 15-edge count and triangle/C4 freedom. These finite adjacency statements require synthInstance.maxSize 100000; no global instance is added.

Full finite invariant file /tmp/oec/pequalnp-pilot-103/Finite.lean compiled with exit 0 (finite-third logs empty). Explicit 20-gate baseline /tmp/oec/pequalnp-pilot-103/Circuit.lean compiled with exit 0 (circuit-third logs empty). The final circuit correctness proof uses direct kernel decision over all 1024 assignments.

Additional checked generic helper /tmp/oec/pequalnp-pilot-103/MassTwo.lean: two distinct original list elements with constant projections contribute mass at least 2, without needing Nodup or distinct projections. Shared with lower_bound and root.

Additional checked components:
- GeometryCheck.lean: exact Automorphisms.lean plus minimal Binary17 definitions, exit 0; geometry-first logs empty. No fixes needed.
- CountCheck.lean: exact count arithmetic wrapper from a supplied 17-binary-gate floor, exit 0; count-check-first logs empty. No fixes needed.
- NotElimination.lean: last-NOT semantic replacement by true under h→f, and by false under f→h, for a suffix monotone in the substituted bit. Exit 0; not-elimination-first logs empty.
- EdgeRobustness.lean: every selection of at least 5 vertices spans at least 2 edges; deleting one edge leaves independence number at most 4; each Petersen edge AND implies its edge function. Exit 0; edge-robust-second logs empty.

Partial.lean now includes the edge robustness lemmas. The combined rerun completed with exit 0; partial-final.stdout and partial-final.stderr are empty. Root requested stopping the rerun for memory, but it had already finished naturally before termination was sent. Boolean expressions before equality are explicitly parenthesized to avoid coercion precedence.
