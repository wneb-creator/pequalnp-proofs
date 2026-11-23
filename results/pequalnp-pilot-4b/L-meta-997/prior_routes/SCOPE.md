# Checked partial results for L-meta-997

These files do not prove the posted statement. Every included Lean source compiled successfully with the pinned project toolchain; the paired log is complete stdout and stderr. Empty logs are successful silent compilations. No posted-statement checker acceptance is claimed.

| File | Proven scope |
| --- | --- |
| SparseCount.lean | Monotone fan-in-at-most-two circuits correct below weight k satisfy the light sum bound sum min(k, line size) <= circuit size + number of lines. Includes localized partial-support charging. |
| HeavyOrCount.lean | Full heavy-window line counting charges OR gates only; proves per-line charge bound, disjointness across linear families, and falsity on the common background. |
| PartialOverlap.lean | An actual nine-gate, one-NOT circuit satisfies the target hypotheses but refutes naive inclusion of coarse partial-support charge intersections in the exact-profile refund. This is not a counterexample to L-meta-997. |
| HeavyAndPruning.lean | A monotone AND function globally sound for a line has a globally sound child. |

HeavyOrCount inlines all helper dependencies, including fp3_strategy's WeightedFrontier theorem. Its original source and successful log are retained under dependencies/. All other dependencies are Mathlib and PEqualNP.Defs; copied evaluation/counting lemmas are already inlined.

SparseCount and the complete HeavyOrCount assembly were independently read by formal_audit, which found no issue. The remaining obligation is a compensation or charge-selection theorem restricting mixed light/heavy cost to the exact-profile refund. RESEARCH.md records the source reuse and this limitation.
