# L-meta-1884 constructive search

The lease was withdrawn at17:03:59UTC; all work is stopped. No counterexample was found.

## Semantics

`FanInTwo` permits only AND, OR and NOT, with at most two listed inputs per gate. Empty AND/NOT are true; empty OR is false. NOT ignores any second operand. Evaluation reads every unavailable wire as false, including forward references, so these references do not create feedback. The circuit's first ten inputs can be permuted or repeated; its eleventh is one of the four unary functions of x0.

The constructive lane chooses the valid specialization with all ten raw inputs in their original order and free NOT(x0) as input10. Every candidate is an actual instance of the posted statement. This lane does not claim that its heuristic search is exhaustive or that other unary functions are irrelevant.

## Initial search

The C++ engine evaluates all1024 inputs for every mutated18-gate candidate. Gate choices include binary AND/OR, unary NOT, constant true/false, and unavailable input references returning false. Arbitrary output wires and unused gates are allowed. The score additionally weights the exact Petersen boundary in some population lanes; it never replaces full truth evaluation. More than one charged NOT incurs a heuristic penalty, not a semantic exclusion or a lower-bound claim.

Seeds come from20-gate monotone vertex-cover circuits and distributive21/22-gate variants, deleting enough gates to reach18. A separate21-gate control uses the free NOT(x0) input to restore x0 through one charged NOT, and then computes the20-gate circuit. All four controls pass1024 rows in the engine and a separate Python implementation of the posted circuit semantics. Full controls, source, driver, and logs are frozen in `gap1884/counterexample/presearch-manifest.json`. The initial compile name collision with `std::apply` was corrected; complete failed and successful build logs are separately retained.

The proposed initial lane is one CPU for900 seconds, with root and local STOP files checked at regular iteration checkpoints. No search was launched before the positive controls and preservation manifest were prepared.


## Prepared zero-internal-NOT exact lane

For a circuit with no charged NOT gates, fixing x0 also fixes its free complement, leaving a monotone circuit in the remaining nine inputs. The two target cofactors have38 combined minimal-positive/maximal-negative boundary rows. The prepared formula is the existing normalized `Defs.LratEncoding.enc2` at11 physical inputs and18 gates on those mapped rows. No statement about an arbitrary NOT circuit follows from38 rows alone; a known18-gate circuit with one charged NOT passes them but fails49 complete assignments.

The18-gate formula has144603 clauses and SHA256 `d70821d2b6c43b4a84fdda720013a11515d1d187ef8b89c97e61ba0d9eee49c4`. The20-gate normalized positive control has an explicit assignment satisfying all182863 clauses and independently matches every one of1024 real inputs. The reviewer regenerated both formulas byte-for-byte and independently checked the full control. The existing generic normalization bridge is being instantiated by sat_encoding; no UNSAT conclusion is claimed.

The solver driver waits for the heuristic lane to exit normally, checks STOP, keeps a disk reserve, writes full stdout/stderr and binary LRAT, and independently evaluates any SAT model on all1024 inputs. Preparation and driver artifacts are frozen separately in `mono-preparation-manifest.json` and `mono-driver-manifest.json`. No additional solver has been launched by this agent during the heuristic lane.


## Final cancellation status

The heuristic completed normally at16:55:49UTC after1,252,458,496 mutations in900.015seconds. Every one of17 unique improvements was independently replayed on all1024 inputs. The final18-gate circuit is monotone and has exactly four false positives at masks50,104,138,208; it is not a refutation. For the independent setA={0,2,8,9}, it computes the four star terms plus the product of their four neighbor-ORs. That product adds four unwanted independent triples to the three internal matching edges.

The reviewed normalized zero-NOT SAT lane began16:56:29UTC. Both its exact encoding and the portable normalization bridge were Lean-checked; the emitted Lean CNF was byte-for-byte identical to the frozen Python formula. At17:03:59 the root STOP file cancelled the solver. It exited via SIGINT(-2) at17:04:00, while the wrapper exited0. There was no SAT or UNSAT verdict. Complete stdout/stderr, exact command/PID/timestamps/status, source, input CNFs, and controls are frozen in final-search-manifest.json. The raw1,082,200,064-byte binaryLRAT is an incomplete prefix, not a certificate; its separate metadata records its hash and retained scratch path. No search continued after STOP, and no process remains active.
