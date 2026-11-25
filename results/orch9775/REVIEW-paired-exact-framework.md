# Independent review: PairedExactFramework

UTC: 2026-11-25T17:40:22.342635+00:00

Verdict: PASS for the new paired exact-neighborhood soundness bridge. Source: 125 lines, 5,974 bytes, SHA-256 `3d7527bb8d4d7f158c741193428aeeedd67b2608dd0e6de87234ea8c963fa093`. The separate Compact/WeakCompact and resolution-checker audit records the imported dependency checks.

`Layout.exact_from_chain` correctly promotes a shared-empty semantic witness to a genuine exit slot for x. The witness gives x in the selected operand support. If x survived the AND output, it would also belong to the opposite operand; that operand is dominated by i along the explicit single-fanout chain, so its singleton support is contained in {i}. This would give x=i, contradicting the stated adjacency and graph irreflexivity. Layout.covers then supplies an actual live slot, and Layout.limit supplies the cap. The exact projection labels follow directly from the witness's equivalence on every member of the mask.

`Layout.paired_exact` applies the already checked upstream sem_shared_empty theorem with all premises preserved: strict-live exact graph computation, Bzero at most 1, independent projection set, both ineligible vertices, and a projected neighbor distinguishing j from i. The selected adjacent x/y ensures the corresponding semantic witness yields a valid slot. The result is an OR of two existential slot statements; it does not assert both or choose one globally.

The plain BudgetScheme branch explicitly requires weakScheme=true, excluding exactAt, whose stronger Bzero=0 requirement would otherwise be invalid here. The paired branch encodes the exact disjunction and checks all finite geometry assumptions. The expandBudget lists include every bounded slot. localCheckBudget allows only clause weakening by actual signed facts; the atLit defaults and truth defaults agree. inputsOKBudget requires paired list lengths and validates every clause; book_start_budget transfers this to exactly the first n clauses. No solver result is assumed by these theorems.

Both full compile streams are empty; author validation records successful check/export. The saved axiom audit reports only propext, Classical.choice, and Quot.sound. No new build was run. Source format/prohibited-marker scans pass. This helper alone does not establish exhaustive case coverage, kernel acceptance of any generated RUP certificate, or the final gap theorem. The WeakCompactFramework import still requires inlining in a final standalone file.
