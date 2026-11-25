# Frozen OR-count SAT extension

The generic `false_or_count` theorem compiled and passed independent review. For each maximal-negative Fano assignment S, every absent input is individually critical: switching it on makes the output true. Hence at least 13−|S| OR gates are false at S. The 37 rows give two thresholds of6, fourteen of8, and twenty-one of9.

The new encoder adds a literal for each row/gate expressing that the gate is OR and false on that row. A threshold dynamic program enforces the required count. Cell(i,j) means at least j of the first i literals are true; its recurrence is z iff a OR (b AND x), encoded by four clauses. Every auxiliary variable has a recorded meaning in metadata.

Exhaustive small-case tests covered all27,826 complete input/auxiliary assignments for n=0..4 and thresholds0..n+1, including impossible thresholds and the zero threshold. Each satisfying input has exactly one auxiliary assignment. The independent reviewer separately checked the recurrence truth table, reconstructed every new clause, verified all37 critical-input masks, and assigned every variable of the known28 control. That control satisfies all250,866 clauses across18,814 variables. This is an encoding validation, not a target27 satisfiability claim.

The final target has18,073 variables and236,262 clauses. The prior minimality-only run stopped UNKNOWN after1,024.184 seconds; complete logs are archived. The sole new solver launched at11:01:51 UTC with5,526 seconds and the unchanged12:34 UTC cutoff. Root renewed the lease at11:01:26, expiring11:21:25.822, with automatic renewals continuing. This encoder is frozen.

Restore the earlier `sat-preservation-manifest.json` bundle first, then the files in `sat-orcount-preservation-manifest.json`, decompressing each `.gz` to its restore basename. Run `python3 status-orcount-fano-sat-review.py ARTIFACT_DIRECTORY` for the complete independent final-control and exact-extension check. The small exhaustive test and author control check retain their fixed scratch root, as do the encoders. The new manifest excludes mutable active output; all earlier archived bytes and hashes remain unchanged.
