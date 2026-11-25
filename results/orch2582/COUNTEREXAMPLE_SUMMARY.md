# Counterexample investigation for L-meta-2582

No proof or refutation of the posted projective-plane normalization statement was found. The examples below concern P4 and a three-edge matching. They test local normalization ideas; neither is a plane instance or a globally minimum circuit.

## Lean-checked examples

- `lemmas/ReadTwoSanity.lean`: a five-gate P4 circuit is not READ-2, while an equivalent four-gate circuit is READ-2 and smaller. Thus a source circuit failing READ-2 does not refute the existence of a suitable replacement.
- `lemmas/ReadTwoLocalObstruction.lean`: a seven-gate P4 circuit is not READ-2 despite all eleven wire functions being distinct. An equivalent four-gate READ-2 circuit is checked. Eliminating duplicate wire functions alone is insufficient.

Both files compiled with exit 0 and empty stdout/stderr. Their diagnostics are archived alongside this summary.

## External finite searches

- C6, eight gates, requiring failure of READ-2: UNKNOWN after 120.048 seconds, timeout. No infeasibility or minimality conclusion.
- P4, seven gates, requiring failure of READ-2 and every single-gate bypass to either operand to change the final function: SAT in 2.842 seconds. The full truth table, all fourteen bypass witnesses, and literal capped-at-three joint count vectors were independently checked. This circuit has a duplicate wire function, so it does not combine semantic distinctness with the bypass property.
- Fixed five-gate P4 sanity: SAT without the bypass constraint; UNSAT with it, as expected from its known removable final gate.

These are external solver results, not Lean-certified optimality results. Times are driver-measured wall times. The READ-2 encoding preserves joint vectors, including zero coordinates, and the independent validator compares its truncated vectors against the literal capped-at-three recurrence at every wire.

## Matching CNF construction

The structural agent supplied a nineteen-gate circuit for the three-edge matching: four shared two-variable ORs, eight prime CNF clauses, and seven ANDs. Numerical checks establish its exact function on all 64 inputs, failure of READ-2 on each edge, all 25 wire functions distinct, and a changed output for all 285 replacements of one gate by any earlier wire. A direct five-gate READ-1 realization exists, so this is not a global minimum.

`lemmas/MatchingCNFValidation.py` reproduces these numerical checks and their explicit witnesses. `MatchingBypassCertificate.lean` formalizes the construction and all 285 earlier-wire bypass witnesses. Its inclusion in the final named file passed `lake build` at 18:54:28 UTC; the axiom audit uses only the three permitted axioms. The raw existential variant exited 137, while the standalone explicit-certificate exit status was lost; neither is used as evidence for the successful final build.

All searches have finished. Complete output files are archived with byte counts and SHA256 hashes in `read2-log-manifest.json`.
