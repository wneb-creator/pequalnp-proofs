# Free-AND / bounded-OR finite evidence for L-meta-2962

All results in this directory are computational research, not Lean proof or a statement about the full posted theorem. The small positive controls were independently reviewed by status_review, including every CNF clause and every full truth-table row.

Normalization: allow an arbitrary conjunction of previous wires on each input of each OR generator, and an arbitrary conjunction of generator outputs at the end. This represents AO 2 circuits with the given number of OR gates and unlimited AND gates. The SAT program encodes the monotone dual, using AND generators whose ports are ORs. All operands and final output are nonempty. For cycles, excluding direct original inputs from the final conjunction is complete, because no input belongs to every required positive edge. The partial-edge encoder checks that intersection condition explicitly.

Truth rows: every maximal independent set is negative; required edge pairs are positive. Monotonicity makes these rows sufficient for the full BelowF condition and required accepted pairs. For exact runs all edges are required. Each SAT model is decoded to the original AND/OR interpretation and tested on all full input assignments.

- C6, four OR generators, exact edge function: UNSAT, CaDiCaL exit 20, 384 variables / 1292 clauses / 11 rows; 0.52 seconds solver-reported real time. Five-OR pinned positive control SAT; all 64 original truth rows and 1914 clauses checked.
- C4, two OR generators, exact edge function: SAT positive control; all 16 truth rows and 222 clauses checked. This intentionally violates the NoFourCycle hypothesis.
- C8, four OR generators, six required edges: UNSAT in all four symmetry cases, omitting edge 0 and edge distance 1,2,3,4. Each 545 variables /2058 clauses /16 rows,0.11–0.18 seconds wall time. The five-OR partial positive control SAT; all 256 input rows and 2884 clauses checked.

The bounded-OR conjecture is that a circuit below a bipartite C4-free graph, accepting D, needs at least |D|-1 OR gates. It is equivalent to the exact graph-function lower bound: OR in each missing edge monomial at one additional OR each to obtain the exact graph function. No proof of that conjecture was obtained here. UNSAT is an ordinary solver result, not a proof checked by Lean.

## Dense four-by-four graph census

Exhaustive enumeration of all 65536 bipartite 4-by-4 adjacency matrices found 1608 C4-free graphs having at least 8 edges. Up to separate permutations of the two parts, there are six classes: five 8-edge classes, and one 9-edge theta graph. The enumeration was independently checked with explicit 2-by-2 square masks and all 24-by-24 group actions; see census-independent-review.json. This is a Python enumeration, not a Lean theorem.

The four 8-edge classes other than C8, masks 43399/43377/43380/38483, are all UNSAT with 6 OR generators and unrestricted AND, using the reviewed disjoint-port normal form. Run times 27.5/42.0/28.5/36.6 seconds. The existing C8 computation was independently run by combinatorial_bound. A 7 OR positive control for mask 43399 passes all 256 input assignments. These together support the OR lower bound computationally for all 8-edge graphs in the 4-by-4 census.

The 9-edge theta graph is three internally disjoint length 3 paths joining two endpoints. Both unrestricted and normalized 7 OR searches reached their 300 second caps with UNKNOWN (exit 0). No conclusion follows for that budget. Both 8 OR positive controls were SAT and passed every 256 full truth rows.

## Final theta status

Six OR generators: UNSAT in 30.26 seconds real time. This separately justifies the conditional live-at-seven optimization discussed in normalization.md. Seven OR generators remain unresolved: unrestricted, disjoint-only, disjoint+live, and disjoint+live+predecessor-order variants each reached their 300-second cap; the alternative disjoint+live+graph-automorphism variant reached its 180-second cap. All returned UNKNOWN, not UNSAT. The eight-OR controls for each representation were SAT and validated completely. No active solver remains from this agent's batch.
