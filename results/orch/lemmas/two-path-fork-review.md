# Independent review: two-path fork

Reviewed by constructive on 2026-11-25 UTC. Source: `/tmp/oec/pequalnp-pilot-70/lower-bound/TwoPathFork.lean`, 39 lines. Read the complete source and empty `two-path-fork-lean.log`; the author reports Lean exit 0. This review did not rerun Lean.

Verdict: PASS. The common endpoint guarantees a shared vertex. Choosing the smallest first-path index with any match on the second path gives positive indices on both paths because each start is excluded from the other path. Their immediately preceding vertices must differ, or the first path would have an earlier shared index. The two preceding arcs therefore exhibit a shared child with distinct live parents.

The proof does not require simple paths or acyclicity, and does not implicitly use them. Length-zero cases make the cross-start exclusions inconsistent, so they cause no arithmetic gap. The conclusion matches the fork alternative in `LiveDagCredit.extra_arc_leaf_budget`.

The forbidden-format scan returned status 1 with no matches for `_root_`, string literals, attributes, `sorry`, axioms, `native_decide`, or options. The import is `PEqualNP.Defs`. Constructing these paths from selected clean consumers remains a separate circuit-model obligation.
