Few-NOT investigation for L-meta-2592

2026-11-25, initial route.

Known checked component: L_meta_4725 proves 15 + notCount C <= C.size for the exact Petersen function. Thus a <=19-gate counterexample containing NOT has 1 through 4 NOT gates. This does not itself exclude any of those cases.

Existing reductions already pursue this direction: R_meta_5236_2 and R_meta_5236_593 split the normalized first OR(x0,x2) case into NOT-count cases and shape constraints. A new pure case split is unlikely to add value.

The generic FewNot helpers under MetaComplexity concern simultaneous line-OR families, so they do not directly give a size bound for the single Petersen edge output. OneNotPiece offers semantic decompositions, not the desired cost lower bound.

Checked L_meta_2909 has a strong fixedFirstBound helper for the nine-vertex deletion graph, first gate AND(x0,x2); its final theorem ignores the one-NOT and essentiality hypotheses. This is a useful restriction result but does not by itself cover all first gates of the ten-vertex problem.

Research read 2026-11-25: https://pequalnp.com/papers/note-1 through web search result. Its prior-work section distinguishes monotone formula / restricted monotone bounds from NOT-allowed circuit bounds, and explicitly describes gaps in published exact graph-function values. No external theorem eliminating one NOT at no cost was found in the allowed-domain searches. General inversion complexity is not a size-preserving elimination theorem.

Independent review of root PetersenWitness.lean: PASS mathematically and by an independent parser/simulator. Twenty binary monotone gates, all operands strictly earlier than their gate output; output29 final; exact15 posted edges; all1024 truth-table rows agree. Lean compilation pending. This is an upper-bound partial only.

Structural observation for further search: every maximum independent set has4 vertices. Its six-vertex complement induces a matching of3 edges. The remaining12 edges form the incidence pattern between the4 independent vertices and the6 pairs of them (each complement vertex has two independent neighbors). A potential NOT-saving construction could exploit this K4-pair pattern, but no19-gate expression is currently known.

Independent SAT encoding audit, 2026-11-25:

The current counterexample_sat.py encodes legal earlier wires, an extra free false source, exactly one selected source for each operand, AND/OR source ordering, and at least one NOT. The local gate clauses are correct by truth-table inspection. NOT fixes its ignored second operand to input0, which does not change its meaning. The generic search allows repeated binary operands and false reads. The additional normalized mode forbids those and requires every nonfinal gate to feed another gate; those extra restrictions remain witness-search assumptions unless separately proved.

Audit experiments independently checked 309,630 non-output structural clauses against forward evaluations of 30 randomly generated five-gate circuits over 48 rows each. Six small synthesis controls using all1024 input rows gave expected outcomes: NOT(input) with one gate SAT; AND(inputs) with one gate and mandatory NOT UNSAT; AND(inputs) with two gates and a dead NOT SAT; true with one NOT gate SAT; false with one mandatory NOT gate UNSAT; false with two gates including NOT SAT. The provided pinned21-gate control model satisfies every one of its1,520,836 CNF clauses under an independent evaluator. Exact data: scratch sat-independent-audit.json; audit source audit_sat_encoding.py.

Generic exact19/final-output completeness can plausibly be proved without full-cone or distinct-operand normalization: truncate at the actual output gate; if this removes all NOT gates, the retained prefix has at most18 gates, so insert one dead NOT before it and shift indices; finally pad with identity gates. The Petersen output is neither a constant nor an input, so an output gate exists. Empty AND can become NOT(false) at equal cost; this may increase the number of NOT gates, so the argument fits the generic at-least-one-NOT encoding but not a fixed-NOT-count search without extra work. No such normalization has yet been formally checked by this reviewer, and no UNSAT certificate or lower bound is claimed from the audit.

Compiled new components:

IdentityPad.lean compiled exit0 and independently reviewed by status_1035: identity OR gates pad a canonical final-output circuit to any larger exact gate budget, preserving evaluation, input bounds, output position, and existence of a NOT. Current frozen source has148 lines.

OperandSort.lean compiled exit0 with no diagnostics and independently reviewed by status_1035: sort binary AND/OR operand indices while leaving NOT unchanged; preserve all wire values, gate count, output, canonical bounds and NOT gates. Current frozen source has148 lines.

2026-11-25T14:12:58Z: exact-four-NOT SAT run returned UNKNOWN (solver exit0) after900.39 seconds, no model/UNSAT. Initial instance:91 rows,5985 variables,138564 clauses. Full logs, compressed CNF and hash summary archived in sat-exact-four-not/. This is not a lower-bound result.

2026-11-25T14:15:07Z renewal from root preceded exact-one-NOT generic final-output CEGIS run,1200-second cap, initial41 rows (zero, singletons, edge pairs and maximal independent sets). Every solver model is checked against every CNF clause and all1024 inputs. Run ongoing.


2026-11-25 14:27 UTC updates:

- AIG orientation minimizer independently reviewed: signed incoming polarity is XOR with the destination orientation; each source pays one physical NOT iff its opposite-produced polarity is demanded, including output. Exhaustively checked 5,110 AIGs with 0–1 inputs and at most two binary nodes, 20,198 orientations, 38,826 truth rows. All reconstruction counts, semantics and minima passed. This is finite validation of accounting, not a lower-bound proof; mandatory-NOT preservation must be checked in the reconstructed witness.
- Exact-one-NOT generic 19-gate CEGIS remains on iteration0 with 41 rows and no verdict; 1,200 second cap started approximately14:15 UTC.
- Prepared local SAT repair of the 19-gate monotone candidate that computes Petersen minus edge7–9. Every at-most-four-changed-gates neighborhood is encoded by unchanged markers implying complete baseline gate descriptions, and every set of five positions must contain a marked unchanged position. Initial46 rows include all six known baseline errors. Counterexample agent independently reviewed160 structural assignments; own controls cover768 cardinality cases and six pinned SAT/UNSAT cases. Search not launched yet, pending exact-one completion and root lease renewal. UNSAT would concern this fixed-order neighborhood only.
- CanonicalSortedNotBound footer independently reviewed: sorting preserves gate count, indexed validity, last output, at-least-one NOT and full semantics; erased-false binary floor implies at most four NOTs. No circuit exclusion follows from this reduction alone.
