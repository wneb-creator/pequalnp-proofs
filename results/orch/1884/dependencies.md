# L-meta-1884 dependency audit

Assignment: Petersen edge function cannot be computed using at most18 fan-in-two AND/OR/NOT gates, ten relabelled original inputs, and one arbitrary unary function of input0 supplied free.

All three live reduction slots are occupied. No complete proof or refutation obtained. The following is a dependency audit, not an implication that open claims are established.

- R_meta_1884_1: ordinary Petersen size18 impossibility (L4031 OPEN), Petersen-minus-vertex size15 impossibility (L4033 CHECKED, also L670), no-positive0/readers-of-negative0 core (L4035 OPEN), unique positiveOR/negativeAND reader core (L4037 OPEN).
- R_meta_1884_412: robust pivotal property (L6081 CHECKED), remaining circuit core (L6083 OPEN).
- R_meta_1884_773: input relabelling (stronger L7338 CHECKED), unary normalization, normalized free-negative0 lower bound.
- R_meta_4031_23: L670/L4033 plus L9206 OPEN (some zero restriction eliminates at least3 gates).
- R_meta_4031_1: L9037 and L9039 CHECKED; L9041 OPEN.
- R_meta_4035_452: L7312 trace and L7314 normalization CHECKED; L4031 and L7316 OPEN.
- R_meta_4035_1: L4031, L6474, L6476 OPEN.
- R_meta_4035_534: L8269 finite column distinctness CHECKED; L8271 circuit core OPEN.
- R_meta_4037_1: L6146 and L6148 OPEN.

Fresh upstream commit e125f04d0dc6fed67cee48a1d06692912e167c32 contained147 additional proof files beyond starting base; their statements did not close the missing Petersen18 claims.

Existing positive control L_meta_587 proves the exact target has a20-gate monotone circuit. External SAT controls checked that circuit on all1024 inputs. Counterexample searches cover18 gates with identity input order and free complemented input0. A subclass with AND/OR gates only uses38 extremal rows; coverage of all1024 assignments follows monotonicity of each input0 cofactor and was checked separately. No UNSAT result yet; neither search is a Lean lower-bound proof.

The nine-variable Live-circuit certificate proof L670 uses512-bit signatures and finite tables. No generator was found locally or in the cited contributor fork. Adapting it to ten variables requires new tables and a correctness argument; current table data cannot be relabelled into the new goal.
