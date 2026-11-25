# Counterexample strategy

Assigned gap: L-meta-2592. Checked the actual definitions: AND and OR have at most two operands; NOT reads its first operand; missing wires read false. No unintended gate basis or fan-in loophole was found.

The Petersen graph edge function is true on 948 of 1024 inputs. Its 76 independent inputs have cardinality distribution 1, 10, 30, 30, 5 for sizes zero through four.

No SAT/SMT solver or Python bindings were available at startup. CaDiCaL was subsequently built from its public GitHub source in `/tmp/oec/pequalnp-pilot-127/cadical`. A stochastic circuit search uses full 1024-input truth tables and varied false-positive weighting. This is heuristic, not exhaustive. Seeds are random circuits and 19-gate perturbations of a 20-gate monotone star-cover circuit.

Existing exact reductions: R_meta_2592_318, R_meta_2592_408, R_meta_2592_271. They already occupy the three reduction slots reported by the desk. Existing Petersen-nine and graph gate-elimination proofs have been shared with the structural strategy agent.

## Search methods and controls

`counterexample_sat.cpp` encodes circuit op and predecessor selectors with per-input multiplexer and gate semantics. It starts on the 76 independent inputs plus 15 edge inputs, and any model is tested against all 1024 inputs before refinement. One run searches exactly one NOT in 19 gates. A second searches one to four NOTs in 19 gates with nondecreasing maximum predecessor order. Case-bounds agent found a checked 15-non-NOT lower bound, motivating the four-NOT cap.

UNSAT for these encodings alone would not prove the posted statement: the encodings use predecessor-only binary gates, one-operand NOTs, and the final gate as output. The posted syntax also allows constants, short operands, invalid reads, and arbitrary output. A normalization proof would be needed.

`counterexample_validate.cpp` locked four controls and checked all 1024 inputs both directly and through the SAT encoding: a 20-gate monotone witness, a 21-gate witness with one unused NOT, a 22-gate witness with two cancelling NOTs, and an intentionally incorrect mutation. Results were SAT, SAT, SAT, UNSAT as expected. The same controls passed with the ordered encoding after topological reordering. Full logs are in scratch as `counterexample-validate.stdout` and `counterexample-validate-ordered.stdout`.

`counterexample_repair.cpp` searches near the best approximate monotone circuit by fixing random subsets of gates under temporary SAT assumptions. An initial run incorrectly fixed noncanonical commutative operand order; it was stopped and corrected. NOT ignored operands are also normalized to zero. No result from that failed initial run is evidence.

## Findings so far

The unrestricted heuristic reached a 19-gate monotone circuit with five false positives: independent sets containing the extra chord {2,4}. A NOT-required run reached eleven discrepancies, but its NOT was unused. Both are only approximations, not counterexamples. The current stochastic worker requires a NOT on the output dependency cone. Progress scores compare different false-positive weights across restarts; only explicit full-table evaluation gives an ordinary Hamming distance.

At 2026-11-25 14:39 UTC, no complete SAT result or actual counterexample had been found. The unrestricted heuristic and 18-gate monotone SAT run were stopped to reserve resources for useful searches and Lean work.

Root reported lease HTTP410 at 14:38:51 UTC. All four remaining search workers were terminated at 14:39:15 UTC. No SAT verdict or actual counterexample was obtained. Full diagnostics and best candidates were archived in `counterexample-logs.tar.gz`; no search continues while the lease is unavailable.
