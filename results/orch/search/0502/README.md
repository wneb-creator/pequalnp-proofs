# Prepared disconnected-parent strengthening

The reviewed general-five-cost-disconnected runner adds29variables and482clauses to the already running general five-output reduced query. A color per parent wire and output edge forces selected-parent and edge colors equal, while two edge colors must differ. This is exactly parent-graph disconnection, necessary by checked ConnectedCircuit after the injective in-place constant/copy compilation. All500 fixed-graph tests passed, and count-only full regeneration reports129594variables/2680563clauses. No CNF or solver has been launched for this variant; the older live query is unchanged.

Its dependencies are preserved in../0457/general-five-reduced-cost/encoding-source, with hashes repeated in dependencies.json. The source covers the reduced five-output class, not the unrestricted thirteen-output gap.

The disconnected-core-analysis files only classify needed original clauses from the already independently replayed restricted2+3 certificate. They do not assert a new SAT/UNSAT result. The count-only reconstruction exactly matches the original clause/variable counts. Resource snapshot0502 was taken at05:01:03 UTC; all four queries were live with no new verdict.
