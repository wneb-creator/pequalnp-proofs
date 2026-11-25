# Fixed P5 OR-prefix computational boundary

The established result here is an exhaustive ordinary-Python census. There is no accepted Lean certificate for this boundary. It is a local circuit-replacement example, not a refutation of L-meta-1031 or a minimum-circuit claim.

The graph has edges 01, 12, 23, 34. Starting from inputs 0 through 4, the frozen seven-OR prefix has operand pairs (1,3), (1,2), (6,4), (0,4), (8,2), (0,3), (10,2). Its twelve input/prefix functions and both constant functions are free sources in the stronger finite model.

Each signal records its complete 32-bit Boolean truth table and the four-bit union of pair-input truth masks of all AND gates in its ancestry, including its own gate when applicable. An OR unions both ancestor masks. An AND owns its pair truth mask minus its operands' ancestor union. It is legal when that ownership mask is nonempty and contained in one of the maximal P5 star masks 3, 6 or 12. The resulting ancestor mask additionally includes that AND output's pair truth mask.

The Python enumeration finds no completion using at most three added legal gates. It starts with 14 free signals, reaches 44 states after one gate and 1,311 after two, and examines 367,362 operation transitions. It deduplicates whole available-signal sets, retaining ancestry masks, so it preserves distinct future ownership behavior. Complete output is `p5_frozen_or_boundary_free_true.log`; the source is `lemmas/CounterexampleP5BoundaryFreeTrue.py`. The original version omitting free true is also preserved.

Proof attempts failed and are not results:

- An initial tactic attempt was discarded after axiom audit found native reflection. That source is not retained for publication.
- `experiments/P5Boundary_UNVERIFIED.lean` uses ordinary `decide +kernel` over deduplicated signal lists. Its build exited 137 during memory pressure. Complete diagnostics are `p5boundary-lean-02.log`.
- `experiments/P5BoundarySplit_UNVERIFIED.lean` splits the same computation into 58 first-signal cases and validates an explicit first-signal table. A single-worker build under Lean's 2 GB memory cap exited 134 before a useful theorem completion was reported. Complete diagnostics are `p5boundary-split-lean-02.log`.

Both preserved Lean files are explicitly unverified research drafts. Neither uses native reflection, declares axioms, or contains placeholders, but neither has passed a complete build. No general correspondence with the repository's `Circuit` type has been proved. Further attempts were stopped to prioritize the exact total-gate searches on the assigned problem.
