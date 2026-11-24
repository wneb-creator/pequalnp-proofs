ER3 polarity graph factoring, L-meta-2028

The thirteen-vertex graph in theory/polarity3.json has A={8,9,11,12}, B={0,1,4}, and C={2,3,5,6,7,10}. A is independent. C is indexed by the six K4 edges, with A-C adjacency given by endpoint incidence; the three opposite K4 edge pairs are adjacent in C. B forms a triangle, and each B vertex joins one opposite C pair.

Deleting B leaves the Petersen graph: ten vertices, fifteen edges, cubic and girth five. The three local seven-edge pieces each admit the formula

  (p OR q) AND (b OR ((p OR t) AND (q OR s))),

where s is the OR of the two A-neighbors of p and t the OR of the two A-neighbors of q. Each piece uses eight gates. The B triangle uses four, and joining four outputs uses three: total 31, meeting the proposed bound. The generated straight-line circuit was independently evaluated on all 8192 input rows and matches the graph exactly. No single gate can be replaced by any earlier wire while preserving the output function.

The four A-centered OR sums of their three C-neighbors do not directly provide a cheaper matching test: their conjunction equals the three-edge C matching function plus four spurious independent C-star triples. Such a sharing attempt introduces false positives.

Cross-piece pure-A pair sums are all distinct. A saving cannot arise merely by sharing those six OR gates across the local eight-gate pieces; a more substantial nonlinear rearrangement is necessary.

Files: /tmp/oec/pequalnp-pilot-31/toolchain/er3_factor.py, er3-factor31.json, er3-factor31.log. These are computational observations, not Lean proofs of optimality.

After root renewal at 15:36:17 UTC, started an unrestricted-OR normalized seven-AND synthesis query with a 600-second cap, using search/and-synth.py and Kissat. Exact examples are the graph edge pairs and maximal independent sets; any satisfying model must be independently checked on all 8192 rows and expanded to binary gates before claiming a total-size witness. Query/metadata/log files: toolchain/er3-and7.* and er3-and7-encode.log, er3-and7-solve.log. No binary gate budget is imposed by this query.

Additional complete finite checks

- Exhaustive rewrite neighborhood of the explicit 31-gate DAG: delete one gate by aliasing any earlier wire, then change one other gate to any binary AND/OR on earlier wires. No success among 5,789,570 replacements in 4,352 viable contexts. Code/log: toolchain/er3_rewrite.cpp, er3-rewrite.log. This excludes only this rewrite neighborhood, not all 30-gate circuits.
- Exhausted 12,603 loopless input partitions with at most three identifications. Only the original graph remains C4-free; every proper quotient fails that requirement. Runtime 1.05 seconds. Code/log: toolchain/er3_quotients.py, er3-quotients.log.
- The graph is 4-chromatic: three colors on the B triangle force each opposite C pair to use the other two colors. The four A neighborhoods select one C from each pair with a fixed parity. The two rainbow selections are complementary and have opposite parity, so exactly one A neighborhood is rainbow in every assignment. A fourth color for all A vertices completes a coloring.

Prepared new structured synthesis: five shared AND/OR gates on A alone, then six gates for each local seven-edge piece, then seven gates for the B triangle and output joins: total 30. A 31-gate positive control fixes the six shared pair-OR functions. Encoder and full truth-table decoder are toolchain/er3_shared.py and er3_shared_decode.py; target CNF has 1659 variables and 21597 clauses. Each local function is constrained on its seven edge pairs and three maximal independent sets, which suffices because every synthesized helper and gate is monotone. Status reviewer is checking this encoding before solver results are trusted.

At 15:46 UTC, the seven-AND query reached its 600-second wall cap with UNKNOWN, after 5,608,367 conflicts and 480.37 CPU seconds. It found no witness and established no impossibility result.

The shared-A 31-gate positive control solved SAT in 0.09 seconds. The independent decoder verified its output on all 8192 inputs, checked C4-freeness, and recomputed minimum cover 8 and bound 31. It is a control, not a counterexample. Saved as toolchain/er3-shared-control-witness.json, with solver and decoder logs alongside it.

The independently reviewed 30-gate shared-A target was UNSAT in 2.25 CPU seconds (93,502 conflicts). This excludes only five A-only helper gates followed by six gates per local piece and the fixed final combination.

Alternative safe-OR gadget: an ER3 circuit with 31 gates that also exposes OR(a,c) on an adjacent A-C pair would yield a counterexample after adding a new center adjacent to a,c and a new private leaf. Such pairs have zero common neighbors, so the extension remains C4-free. The edge count rises from 24 to 27 and minimum cover from 8 to 9; the private center-leaf edge forces one new cover vertex, and the new center achieves that bound. Reusing the auxiliary OR takes three new gates, giving 34 versus the bound 35.

Prepared the safe-OR template with five shared A gates, local budgets 7/6/6, and seven final gates: 31 total. The first local piece selects both its main output and OR(11,7) from any of its gates. The encoder/decoder passed independent review. Its positive control uses six fixed shared pair ORs: 32 gates before the extension, 35 after, verified on all 32768 enlarged inputs. The target has not yet run while the parent's renewal response is pending.

Neither exact 31-gate model contains a useful safe-pair OR. Exhaustive single-gate semantic rewrites checked 22,227 and 21,482 alternatives respectively without finding any that preserve the main function and change the selected gate's function. The 30-gate evolutionary near miss computes the graph with edge {5,6} deleted exactly; that graph has 23 edges and minimum cover 8. Its 18 safe pairs also yield no exposed OR or successful single-gate rewrite among 20,240 alternatives.

Completed evidence is preserved in results/orch/er3/ (programs, input data, controls, metadata, and complete logs). Distance-3 and distance-5 repairs of the evolutionary 30-gate near miss are prepared in scratch but have not run.
