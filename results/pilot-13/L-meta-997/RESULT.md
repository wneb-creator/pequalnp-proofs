# L-meta-997: compiled partial results, no general proof

The exact posted statement is in statement.txt and posted-gap.json. The proof source is lean/PEqualNP/Outside/L_meta_997.lean. It contains helpers only: the named final theorem is absent. Build27 succeeded on6310 lines. The exact-statement checker rejected that snapshot with no-theorem, as expected. No proof PR was opened.

The compiled special cases include: no NOT gate; |Y|<=2; all outputs meeting Y; all outputs disjoint from Y; every disjoint output of size<=|Y|+1; at most one, two, or three larger disjoint outputs; total excess above |Y|+1 at most |Y|; NOT true on the union of disjoint outputs; n<=5*|Y|+1; and every input dimension<=16. Original hypotheses are retained and extra restrictions are explicit in each lemma.

Other compiled tools include physical light/heavy forests, active singleton paths, within-output Hall matchings, an empty-singleton-support prefix budget, two-color source counting, and a low-weight union bound for at most |Y| selected outputs. These do not establish a global capacity bound across all outputs.

The unresolved step is to combine the light truncated quotas and heavy full quotas while counting each physical gate once except the exact posted refunds. Proper intermediate gates can belong to both window arguments without being refundable. Low-weight correctness of the heavy outputs rules out the cheap abstract set/window countermodels, but no valid global charging argument was found.

No actual counterexample was found. STATUS_REVIEW_FINAL_README.md distinguishes bounded synthesis impossibility, timeouts, positive controls, and counterexamples only to proposed intermediate lemmas. The independently enumerated eight-input hybrid barrier verifies all256 original inputs and disproves only a local gatewise hybrid rewrite; it satisfies the posted inequality.

The results and complete diagnostics are preserved in branch history. The cleanup pass was not started because the exact-statement checker did not pass. None of the search timeouts or restricted-model UNSAT results is a refutation or proof of the posted theorem.
