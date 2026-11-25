# Free-AND / bounded-OR finite evidence for L-meta-2962

All results in this directory are computational research, not Lean proof or a statement about the full posted theorem. The small positive controls were independently reviewed by status_review, including every CNF clause and every full truth-table row.

Normalization: allow an arbitrary conjunction of previous wires on each input of each OR generator, and an arbitrary conjunction of generator outputs at the end. This represents AO2 circuits with the given number of OR gates and unlimited AND gates. The SAT program encodes the monotone dual, using AND generators whose ports are ORs. All operands and final output are nonempty. For cycles, excluding direct original inputs from the final conjunction is complete, because no input belongs to every required positive edge. The partial-edge encoder checks that intersection condition explicitly.

Truth rows: every maximal independent set is negative; required edge pairs are positive. Monotonicity makes these rows sufficient for the full BelowF condition and required accepted pairs. For exact runs all edges are required. Each SAT model is decoded to the original AND/OR interpretation and tested on all full input assignments.

- C6, four OR generators, exact edge function: UNSAT, CaDiCaL exit20, 384 variables / 1292 clauses / 11 rows; 0.52 seconds solver-reported real time. Five-OR pinned positive control SAT; all64 original truth rows and1914 clauses checked.
- C4, two OR generators, exact edge function: SAT positive control; all16 truth rows and222 clauses checked. This intentionally violates the NoFourCycle hypothesis.
- C8, four OR generators, six required edges: UNSAT in all four symmetry cases, omitting edge0 and edge distance1,2,3,4. Each545 variables /2058 clauses /16 rows,0.11–0.18 seconds wall time. The five-OR partial positive control SAT; all256 input rows and2884 clauses checked.

The bounded-OR conjecture is that a circuit below a bipartite C4-free graph, accepting D, needs at least |D|-1 OR gates. It is equivalent to the exact graph-function lower bound: OR in each missing edge monomial at one additional OR each to obtain the exact graph function. No proof of that conjecture was obtained here. UNSAT is an ordinary solver result, not a proof checked by Lean.
