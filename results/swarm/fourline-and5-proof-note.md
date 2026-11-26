# Four-line search constraint

This is a necessary constraint for the searched counterexample class, not a proof of L-meta-2583. The frozen encoder is unchanged.

The four-line core has 16 edges, 16 distinct maximal false inputs, and four vertex-disjoint private-leaf edges. Its graph has no four-cycle. Root and the independent auditor checked all these finite facts; each pair of distinct maximal false inputs has a target-true union. Any vertex cover therefore has at least 4 vertices.

For any exact circuit with at most 18 gates, the false-family signature bound forces at least 4 physical ANDs. If there were exactly 4, the checked saturation theorem would make every AND semantically below the circuit output. Exact graph semantics then give the all-clean hypothesis of CleanBudget.relative_clean_graph_budget. That checked theorem produces a cover T with `16 + T.card <= C.size + 1`, forcing size at least 19, contradiction. Thus any searched counterexample has at least 5 ANDs. This argument uses no minimum-circuit assumption.

Root independently rebuilt H8 portable saturation source `55ab4003` and H7 current clean-budget source, then printed the exact original-model theorem types and their standard-three-axiom closures. H7 also kernel-checked the combined generic implication; the concrete finite graph checks in this archive are Python checks, not a claimed standalone Lean specialization.

The added CNF counts active ANDs only. Each fresh variable is equivalent to active_j AND NOT op_j (op=false is AND). Requiring a true variable in every 14-element subset of 18 variables is exactly cardinality at least 5. The independent auditor checked all 18 equivalences, all 3060 subsets, unchanged baseline clauses, metadata, and geometry. Inactive suffix gates cannot satisfy the bound.

The script reads q3fourline18-all.cnf/json beside itself and writes q3fourline18-and5.cnf/json. To reproduce, generate the four-line base in the scratch directory using the frozen encoder, then copy this script into that same directory and run it. Complete source and independent audit are archived. An UNKNOWN result establishes neither unsatisfiability nor a full-gap lower bound.
