# Structural route

2026-11-25: The target is an equality-case refinement of the expected C4-free graph bound |E| + vertex-cover-number - 1 = 52 + 13 - 1 = 64.

R_meta_2602_2 already formalizes reduction from a 56-gate lower bound on the face removing an incident point and line, plus an unresolved path savings hypothesis. R_meta_2602_926 extracts AND collisions from the derivative failures and reduces to four collision-type counting claims. Neither closes the global counting bridge.

Draft independent component: /tmp/oec/pequalnp-pilot-71/structural/CoverClass.lean proves every vertex cover with at most 13 vertices equals all points or all lines. Uses diagonal matching to force disjoint complementary sides, then cyclic +1 adjacency forces every nonempty point side to be all points. Awaiting Lean toolchain provision to check.

Important correction from counterexample agent: double derivative failure needs at least 3 gates locally, but only 2 AND gates: g1=p∧l; g2=g1∨z; g3=g1∧g2. Hence AND>=15 is not justified merely by double repetition.

05:53 UTC: Parent reported renewal HTTP410; stopped work immediately. CoverClass.lean remains UNVERIFIED (Lean toolchain unavailable), no proof claim.
