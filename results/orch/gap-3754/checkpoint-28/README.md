# Partial checkpoint 28 — L-meta-3754

The 1930-line four-graph certificate compiles and was independently approved by and_lower_bound. It proves ordinary AO2 circuit gate lower bounds C8 >=11, C10 >=14, C6 plus one leaf >=9, and C6 plus a two-edge tail >=11. These are useful prerequisites, not the assigned universal theorem or a counterexample.

The 86-line matching control compiles and was independently approved by status_review and counterexample. It validates a dirty lift-fixed seven-gate circuit against all inputs and explicitly proves that it is not least using a three-gate competitor. It is not a refutation.

Complete successful Lean stdout/stderr are included. The original local target-checker attempt ended with CHECKER FAULT (exit3): the prebuilt Batteries root object was absent. This environment repair is in progress; no checker acceptance is claimed. The named partial file still lacks the target theorem. The two Cadical conversion-review runs include the failed initial probe and successful corrected validation; all complete logs are retained.

Independent reviews also approved the computational fourth search bundle and the AND-only audit. Solver UNSAT is not a Lean certificate; UNKNOWN is a timeout, not a lower bound. No complete proof, refutation, or PR is claimed.
