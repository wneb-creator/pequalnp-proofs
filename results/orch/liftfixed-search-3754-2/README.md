# L-meta-3754 finite circuit searches: checkpoint 2

This continues ../liftfixed-search-3754. It contains computational evidence only, not a Lean proof or posted refutation. No dirty circuit at an established optimum has been found. Z3 UNSAT reports have no kernel-checkable certificates here; UNKNOWN/timeouts carry no exclusion. The earlier bundle supplies the unchanged generic synthesis sources and shared graph specifications. Full exact SMT2 formulas, stdout/stderr logs, and every found SAT model are preserved.

## Independent exhaustive control

`exhaustive-p4.py` directly enumerates 1,279,708 four-gate completions over four raw inputs, without SMT or gate-order symmetry. It rejects an OR when operand BelowF statuses disagree. Of the full-cone circuits computing the P4 edge function, six were found and none had a dirty AND. All evaluations use complete 16-assignment truth tables. This independently corroborates the P4 solver encoding; it is not a kernel certificate.

## Six-vertex forest census

The batch used a five-second cap for each of the 19 nonempty unlabeled forests on six vertices, including isolated vertices. It produced 18 UNSAT and one UNKNOWN (case19). A separately labeled P6 query then returned UNSAT in 2.667 seconds. Case19 is the path whose vertex order is [4,2,0,1,3,5], giving an explicit isomorphism to that P6 query. Thus every forest representative eventually has an unstrengthened dirty-query exclusion at its constructive |E|+tau-1 budget. This also covers smaller dirty full-cone circuits by appending AND(output,output) gates: padding preserves the dirty witness and every OR fixedpoint condition. Combined with the previous C6 exclusion, this covers the bipartite C4-free graphs through six vertices computationally, not formally.

The original batch UNKNOWN is retained unchanged. The batch consumes the graph representatives in ../forest-formulas-3754/forest6-formula-search.log; the exact generated graph JSON files are also included here. Formula-only results are not used as shared-circuit exclusions.

## Exactly-one-dirty-AND normal form

`dirty-one-synth.py` adds an exactly-one-dirty-AND cardinality constraint to the earlier generic necessary-condition query. The more compact `one-dirty-normalform.py` instead takes graph JSON, exact total size m, number q of clean terminal ANDs, and timeout milliseconds. It sets p=m-2q and synthesizes p+1 dirty prefix gates (p ORs and exactly one AND), followed by q clean ANDs. Their OR is the desired output; q-1 final OR gates are reconstructed in the SAT model.

Coverage is conditional on leastness, lift fixed point, and exactly one dirty AND. A clean wire cannot feed an AND in a least circuit, and cannot feed a dirty OR at a fixed point. Therefore clean ANDs read only dirty prefix signals, and feed only the final clean OR network. Its q indispensable terminal inputs require at least q-1 ORs and can be joined with exactly q-1; leastness forces that count. Moving the dirty prefix before the terminals and flattening the output OR network preserves all gate-to-zero pivotal tests. The prefix uses the earlier sampled distinctness, edge-criticality, topological-order, and input-automorphism conditions. The normal form and symmetry coverage were independently reviewed by the status-review agent. They are mathematical arguments, not a compiled Lean normalization certificate in this bundle.

These queries are exact-size, exactly-one-dirty subcases; do not infer a general circuit impossibility from them. In particular a negative query at a constructive upper budget does not by itself exclude a smaller minimum when the query also imposes minimum-circuit necessary conditions. The P4 five-gate positive controls pass but are not minimum. Every SAT model is checked again on every Boolean assignment and all gate-to-zero edge witnesses. `verify-models.py` is a separate plain-Python verifier.

## Completed queries

| Query | Result | Seconds |
| --- | --- | ---: |
| cycle8-size11-dirty-critical-auto-one | UNKNOWN | 180.023 |
| cycle8-size11-dirty-critical-auto | UNKNOWN | 300.05 |
| cycle8-size11-one-normal-q4 | UNSAT | 6.79 |
| cycle8-size11-one-normal-q5 | UNSAT | 0.486 |
| cycleleaf7-size9-dirty-critical-auto | UNKNOWN | 180.173 |
| cycletwoleaf8-size11-dirty-critical-auto | UNKNOWN | 180.018 |
| forest6case016-size1-dirty | UNSAT | 0.034 |
| forest6case026-size2-dirty | UNSAT | 0.01 |
| forest6case036-size3-dirty | UNSAT | 0.007 |
| forest6case046-size3-dirty | UNSAT | 0.007 |
| forest6case056-size4-dirty | UNSAT | 0.01 |
| forest6case066-size4-dirty | UNSAT | 0.043 |
| forest6case076-size5-dirty | UNSAT | 0.03 |
| forest6case086-size4-dirty | UNSAT | 0.052 |
| forest6case096-size5-dirty | UNSAT | 0.067 |
| forest6case106-size5-dirty | UNSAT | 0.035 |
| forest6case116-size5-dirty | UNSAT | 0.076 |
| forest6case126-size6-dirty | UNSAT | 0.275 |
| forest6case136-size5-dirty | UNSAT | 0.087 |
| forest6case146-size5-dirty | UNSAT | 0.075 |
| forest6case156-size6-dirty | UNSAT | 0.322 |
| forest6case166-size6-dirty | UNSAT | 0.329 |
| forest6case176-size7-dirty | UNSAT | 4.125 |
| forest6case186-size6-dirty | UNSAT | 0.293 |
| forest6case196-size7-dirty | UNKNOWN | 5.043 |
| path4-size5-dirty-critical-auto-one | SAT | 0.082 |
| path4-size5-one-normal-q1 | SAT | 0.12 |
| path6-size7-dirty | UNSAT | 2.667 |
| theta15510-size15-dirty-critical-auto-one | UNKNOWN | 180.051 |
| theta2449-size13-dirty-critical-auto | UNKNOWN | 180.028 |
| theta2449-size13-one-normal-q5 | UNSAT | 34.591 |
| theta3338-size12-dirty-critical-auto-one | UNKNOWN | 180.025 |
| theta3338-size12-dirty-critical-auto | UNKNOWN | 300.024 |
| theta3338-size12-one-normal-q4 | UNKNOWN | 60.009 |

Checkpoint created 2026-11-25T17:39:44.693166+00:00. Active query outputs were excluded.
