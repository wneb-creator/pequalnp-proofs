# Native SAT experiments

These searches are not proofs of the posted Lean statement. Sources, CNFs, solver versions and invocation hashes are recorded in search-run-manifest.jsonl.

The model bounds only the number of OR gates. Between OR gates, any AND-only network collapses to a conjunction of primary inputs, previous OR outputs and constants. Thus each OR operand and the final output can be represented by a subset selector. Empty conjunction is true; an explicit false atom handles zero constants. Unused OR gates are permitted, so the model means at most k OR gates with arbitrarily many AND gates. All finite conjunctions can be implemented with binary AND gates.

For exact graph semantics, output values on every graph edge and every maximal independent set suffice by monotonicity. Returned SAT models are independently checked against all CNF clauses and the complete Boolean cube. Pair-only runs additionally allow higher-order minterms and check every empty, singleton and pair input.

The CNF encoder and separate integer RUP certificate checker passed independent source review. The verifier proves CNF unsatisfiability by checked reverse unit propagation, rather than strictly validating every unused LRAT record. Assertions require unoptimized Python; runs use python3 without optimization. Neither the encoding-completeness argument nor certificate verifier has been checked in Lean.

C5 validation: k=4 is SAT, with every clause and all 32 inputs validated. k=3 is UNSAT in 0.01 seconds; the 108,281-byte text LRAT trace has 794 additions, all independently RUP-checked, ending with the empty clause. Small C5 artifacts are retained in native-c5/.

Sustained searches: theta(2,3,3) with at most 6 OR gates and Petersen with at most 13 OR gates, each allowing unbounded AND gates and exact graph semantics. Both started at 2026-11-25T01:46:15Z with 900-second limits. Their potentially large proof traces remain in scratch; sizes and outcomes will be recorded on completion.
