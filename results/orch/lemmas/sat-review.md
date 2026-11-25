# Independent Fano SAT encoding review

Reviewed fano_sat.py SHA256 be2deb3b190d2bb9bdda8636fb191a64fd6f3c2b8731b4b54048c20bc5f94c1d. No encoder edits.

The encoding correctly uses one-hot operand selection, earlier wires, commutative operand ordering (equal operands allowed by IsAO2), AND/OR truth recurrences, root falsity on every maximal independent set, and exact read-1 singleton/pair recurrences. Because AO2 gates have no constants or empty proof trees, an AND cannot have a one-leaf read-1 derivation; its two-leaf derivations are exactly cross products of distinct singleton derivations. Root BelowF rules out singleton derivations, so a false pair-read variable at an accepted edge means ReadTwiceAt.

The root is forced AND, accepts a repeated edge, and at least one operand is true on a maximal independent set, ensuring not both operands are implicant. Every nonroot gate is used later, so every gate reaches the last root and the root is the only maximal core.

The residual-cover constraints give a genuine vertex cover Y of G-D. The cardinal constraint is q+(14-|Y|)>=k+9, equivalent to q+7>k+1+|Y|, the strict target violation for the Fano incidence graph with tau=7.

Support filtering permits exactly the selected syntactic input set and forces each selected input to be used. Independent enumeration found maximum possible q+7-tau(G-D) by support size0..9 equal to [0,0,1,2,4,5,7,8,10,13]. Therefore supports<=8 cannot violate the k=9 bound. Independently reconstructed336 distinct Fano automorphisms and verified five eligible size9 support orbits are disjoint with sizes56,168,168,336,84, totaling812, exactly the eligible support count. Excluding supports>=10 additionally uses the checked strict core leaf bound communicated by root.

Local CNF truth-table checks:32 gate/equivalence cases passed. Complete check output is in scratch structural/fano-encoding-review-checks.txt.

Limitations: a SAT model must be independently replayed on all2^14 truth assignments and the precise core/read-vector definitions, then formalized in Lean. The no-core option drops essential core conditions and returns candidates only. UNSAT is computational search evidence, not a Lean proof or a statement about all circuits.


## Multiple-core extension review

Reviewed `fano_multi_sat.py` SHA256 `5d58de5c857b655fac4f5cdc1b24fd98bb35b098d699555fd4258ce678b64301`, plus the pinned shared-P4 calibration and its reproducible `pin_multicore_control.py`. No encoder edits. This is a computational encoding review, not a Lean correctness theorem.

The last r gates are terminal and pairwise incomparable because none may read any earlier designated root. Every earlier gate must be read later; finiteness and increasing wire indices therefore put every gate in a designated root cone. Once every designated root satisfies the core clauses, any other core lies strictly below one of them. Thus the maximal cores are exactly the designated roots and their cone union has k gates. Removing gates outside the original cone union and topologically moving its maximal cores to the end justifies this shape for the restricted circuit class.

The read-1 recurrences and root core clauses retain the single-core semantics. Projected maximal independent sets suffice for BelowF because the circuit uses only its prescribed inputs and is monotone. Every AO2 wire is satisfiable on the all-true assignment; an operand true on an independent assignment therefore witnesses failure of the implicant condition. Root acceptance plus failure of the exact pair read-1 variable witnesses ReadTwiceAt, since BelowF excludes a singleton proof.

The accepted-edge variables represent the union across roots. The residual cover clauses and cardinality q+(14-|Y|)>=k+r+8 are exactly q+7>k+r+|Y|. Since an actual minimum cover can be chosen for Y, existential cover variables introduce no additional restriction. This remains a Fano-graph search, not a search over every bipartite graph.

Ordering is safe separately within the internal and root blocks: greedily choose the available internal gate with minimum (maximum operand, minimum operand, operation). A newly available internal gate reads the just-produced, largest wire, so cannot require a smaller key. All roots can subsequently be sorted without changing their operands. Skipping the internal/root boundary is necessary and implemented. Duplicate operands are permitted.

The operand-arc budget is 2k minus one reader for each of m input wires and k-r internal output wires, hence k-m+r. The generic forward threshold clauses impose only the corresponding upper bound, and actual thresholds give a satisfying auxiliary assignment. An independent exhaustive check of 4,805 fixed-input cases (two reader groups of lengths 0 through 4, budgets 0 through 4) confirmed exact acceptance and explicit satisfying completions. This requires the supplied support list to have distinct valid input indices, as in all reviewed runs.

Independent positive-control replay checked all 19,572 CNF clauses, all 16,384 Boolean inputs, and 147 exact capped read-vector computations. The 19,551 base-clause metadata plus 21 gate-pinning units accounts for the clause-count difference. Both cores are gates 5 and 6, their cone union is all seven gates, and their repeated accepted edge is (1,8). Their union accepts five edges: (0,7), (1,7), (1,8), (2,8), (2,9). Brute-force residual-cover minimization gives seven, so the posted bound is 12<=16 in this control. The control does not refute the target. Full replay results: scratch `structural/fano-multi-calibration-independent-review.json`.

Coverage limits: each solver result applies only to its explicit k, r, support, minimum accepted-edge count, omitted-edge restrictions, and options. The earlier single-core support-orbit census cannot by itself certify a multiple-core search census. A complete finite search needs its own support/orbit and budget accounting; higher gate counts, other core counts, and other graphs remain outside any completed finite run. Timeouts give no verdict. Positive controls test consistency, not completeness. UNSAT certificates have not been linked to Lean, and every SAT candidate still requires full independent semantic replay and eventual Lean checking before it can count as a result for the posted gap.


## Free-OR AND-budget encoding review

Reviewed scratch `core-counterexample/and_free_or_sat.py` SHA256 `1cf9c30322ca23063b65ff548918bb5ee7bf33e7b3c6c48c01b6c46006a91b53` and `and_free_decode.py` SHA256 `012345b2d7af02cd36495a141f9012613908b76df9dd7b198a3cfd73e9c93bf5`. No encoder edits.

Each AND operand is a nonempty OR subset of primary inputs and earlier AND outputs. Every monotone AO2 circuit can be put in this form by flattening intervening OR gates, without increasing its AND count. A circuit with fewer than the declared number of ANDs can be padded with unused gates. The final OR ranges only over AND outputs; this loses no BelowF function because a direct primary input in the final OR would accept its singleton, which the graph function rejects. Repeated operands are permitted and no unproved gate-order symmetry constraint is imposed.

Root falsity on all maximal independent sets is equivalent to BelowF by monotonicity. Exact mode also requires every graph edge, which makes the function exactly Fano. Matching mode requires only the fixed diagonal perfect matching; it is a restricted search, not a census of all accepted matchings or all graphs. This searches an auxiliary AND-count claim, not the full posted core-cover target directly.

Independently replayed all 16,715 clauses of the pinned seven-AND control and all 16,384 Boolean assignments of its decoded circuit. The circuit has seven ANDs and twenty ORs and computes Fano exactly. Replay results: scratch `core-counterexample/and-free-positive-independent-review.json`. The decoder version reviewed semantically verifies witnesses but does not itself check every CNF clause; this validation improvement was reported to its owner. No six-AND SAT/UNSAT or Lean claim follows from the positive control.


The free-OR decoder owner subsequently added full CNF clause replay, and this addition was inspected. Its updated SHA256 is `230e56396dacbe4ced164944d6dfd931e3b857ec471c88418b954fe2cdd84db0`. The decoder still performs full truth-table semantic checks after clause replay.

## Free-AND OR-budget encoding review

Reviewed scratch `combinatorial-bound/free_and_sat.py` SHA256 `ac2d32cf79ed61ec9193e1060e3dd3d13389fbdfc1562ed3f4983f3cc5f079eb` and `control.py` SHA256 `ab3328d6c9fa68657db2a8d91eabbeab9744282531c6919095d96265265605d7`. No encoder edits. This searches the auxiliary strong OR-count lower bound, not the posted core-cover theorem.

Each OR operand is a nonempty conjunction of input wires and earlier OR outputs. The final output is another such conjunction. Flattening intervening AND gates puts any monotone AO2 circuit into this form without increasing its OR count; smaller budgets can be padded by unused OR gates. The selected-term implication `not selected OR value` correctly implements a conjunction over the chosen wires. Nonempty selectors avoid adding a true constant absent from the AO2 model.

The only symmetry clause sorts the two conjunction masks of each OR. Its XNOR variables and equal-prefix tracking compare the highest differing bit, so swapping the two commutative operands supplies an equivalent ordered representative. An independent exhaustive check verified all 1,364 mask pairs of lengths one through five. No ordering between different OR gates is imposed.

Edge-positive and maximal-independent-negative rows determine the exact graph function by monotonicity. Replayed the C4/two-OR and C8/seven-OR controls: all 16 and 256 truth assignments, and all 726 and 13,466 CNF clauses respectively, passed. Full review metadata: scratch `combinatorial-bound/independent-review.json`. These controls do not decide the six-OR C8 search. Any SAT witness must be decoded to an explicit AO2 circuit and independently checked; any UNSAT verdict remains computational and is restricted to the encoded graph and budget.


Optional ordered free-OR mode reviewed at SHA256 `13a91f4fc32c484bc61b5c69e6c7f3e6dacc50180d3996f7a2067330f19cc3e1`: its AND-port prefix comparison selects one of the two interchangeable orientations. Its adjacent-gate clauses require nondecreasing maximum selected source wire. Greedy topological ordering supplies this order because every newly available node uses the newly numbered largest wire. Requiring each AND output to be consumed later or selected finally is complete after removing dead nodes and padding a selected output with idempotent ANDs; that output remains live as the padding operand. Every function sought here accepts graph edges and rejects singletons, so it has at least one AND to pad. These constraints are optional and do not alter previous unordered runs.
