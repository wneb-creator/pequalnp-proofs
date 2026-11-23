Proves the exact posted L-meta-1020 incidence bound for a C4-free relation and sound products with line degrees at most 2 and 1. The proof constructs shared degree-one networks and counts their accepted pairs using source queries and near-star supports.

Validation: `lake build PEqualNP.Outside.L_meta_1020` passed. The local checker returned `ACCEPTED (check)` before and after cleanup, using only the three permitted standard axioms. Independent red-team and semantic reviews passed.

Cleanup reduced the file from 8,909 to 8,900 lines. Complete source, build output, checker output, and validation metadata are preserved in this branch's checkpoint history.

Ride-along refactor: removed one unused helper (nine lines) in a separate `refactor(ride-along):` commit.

Sub-agents: 13 unique agents for proof attempts, counterexample searches, Lean formalization, and independent audits.
TIMING total=187.52 subagents=13
