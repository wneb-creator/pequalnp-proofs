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


## Compact dual OR-budget encoding review

Reviewed scratch `free-and/or_free_and_sat.py` SHA256 `b08057757c4f22bdb0a1f2cad98fe5374c558013873ad028595287cec8864ea1` and `decode.py` SHA256 `0b645c8fb0d5f07888d837b2bca38ec4617761b3c816cad278013c49c3ff45be`. The encoder complements the original cycle MIS/edge rows and reverses their labels, encoding the dual function g(y)=not f(not y). Swapping AND/OR in the decoder recovers the original function. Nonempty OR subsets between budgeted AND gates in the dual correspond to nonempty conjunctions between budgeted OR gates in the primal.

The dual final OR excludes direct inputs. This is complete for cycles with at least four vertices: a direct input in the primal final conjunction would have to belong to every positive edge, but no vertex belongs to every cycle edge. This restriction would require separate justification for arbitrary graphs. No additional gate-order pruning is present in the reviewed version, and unused generators allow a smaller budget to be padded.

Independently replayed the C6/five-OR and C4/two-OR controls: all 1,914 and 222 clauses, respectively, and all 64 and 16 truth assignments, including the complement-duality identity, passed. Metadata: scratch `free-and/independent-review.json`. The four-OR C6 search remains separate; these positive controls establish neither an exclusion result nor the posted core-cover theorem.


## Variable-graph AND-budget encoding review

Reviewed scratch `core-counterexample/unknown_graph_and_sat.py` SHA256 `f66df66ac76a4208f4b1040d51cd3fc2db441da1e395f1d399bc744df17938f9`. It loads the CNF helper from the reviewed local free-OR encoder, whose current SHA256 is `13a91f4fc32c484bc61b5c69e6c7f3e6dacc50180d3996f7a2067330f19cc3e1`. Decoder SHA256: `e30d8996ad0506b6ec5210c723489e4eca013d206abe19fe1cf0aafe69b34e8c`.

The graph varies over balanced bipartite graphs on m+m vertices. Diagonal-edge units require a specified perfect matching, while a negative clause for every two-left/two-right square exactly forbids four-cycles. Every Boolean assignment is represented. Its implication from circuit acceptance to at least one selected graph edge inside that assignment is exactly BelowF; acceptance of all diagonal pairs is imposed separately. The free-OR normal form and the previously reviewed operand ordering, source-maximum ordering, and live-only padding argument apply unchanged. No graph-isomorphism pruning was imposed.

The decoder filters the selected graph edges, checks the common-neighbor characterization of four-cycle absence, replays all CNF clauses, and tests the full decoded circuit. Independent positive-control replay verified all 31,085 clauses and all 256 assignments for four disjoint matching edges and a four-AND circuit. Results: scratch `core-counterexample/unknown-positive4-independent-review.json`. The proposed three-AND/four-pair and four-AND/five-pair searches are separate finite instances; no verdict or Lean theorem follows from this positive control.

## Optional disjoint-port normalization, mathematical review

For the free-AND OR-budget model only, common factors C of the two conjunction ports can be extracted using (A AND C) OR (B AND C) = C AND (A OR B). Process generators in order, substitute earlier conjunction representations into later ports, and replace each later occurrence by the residual generator together with C. If a residual port is empty, the generator collapses to C and can be removed. Any remaining two nonempty ports are disjoint and can be swapped to order their minimum indices. Unused padding preserves an at-most budget; live-only padding with disjoint ports has not been justified. Excluding raw input factors from the final conjunction still requires the positive edge family to have no common vertex. This normalization is informal, not a reviewed code implementation or a Lean theorem, and does not preserve AND count or total gate count.


## 4-by-4 incidence census and normalized fixed-mask search

Independent enumeration used explicit four-edge square masks over all 65,536 incidence matrices. Exactly 1,608 C4-free labelled bipartite graphs have at least eight edges. Independent full row/column group actions on the six reported representatives give disjoint orbit sizes 288, 576, 288, 288, 96, and 72, covering exactly that set. Maximum edge count is nine. Side swaps are not quotiented. Census source SHA256: `2975657d0a8253165aa07b9187490a5e51804a8b4ca311a469c791ee61fb5a8e`; replay metadata is scratch `free-and/census-independent-review.json`.

The reviewed fixed-mask generator builds exactly the encoded incidence matrix. Its disjoint-port and minimum-index ordering clauses implement the previously reviewed free-AND normalization and permit unused generators. Initial CLI pinning caveats were reported to its owner, who added a prohibition on combining a fixed mask with the cycle-specific pin and reordered disjoint pinned ports. Current unpinned search instances were unaffected. This census concerns only 4+4 graphs with at least eight edges and does not establish a general lower bound.

## Direct variable-graph core-cover target encoder

Reviewed scratch `core-counterexample/unknown_core_target_sat.py` SHA256 `e8903efce3cb4553b942ebc8eaa5daf0f2c98886d02682ebb33a7b7b311201b2` and decoder SHA256 `061b89624e83c456920539b1ccb13c8345351134854937c2775342d03ea68ed6`. The graph is bipartite 4+4 with variable edges, square-exclusion clauses, and a fixed diagonal matching of size p. All 256 Boolean assignments are checked. Every gate implicant variable is its exact BelowF condition; satisfiability is automatic for valid positive AO2 gates.

Each designated root is AND, BelowF, has at least one nonimplicant operand, and accepts an edge lacking a read-1 pair proof. At an AND root, such a pair proof is exactly the cross product of distinct singleton proof supports of its children; no empty proof is possible. Every internal gate is consumed later; the final one or two roots are incomparable. Consequently every gate lies in the root-cone union and the designated roots are exactly the maximal cores.

The D variables are the union of accepted edge pairs. The selected Y covers every selected graph edge outside D. Cardinality enforces |D|+p>g+r+|Y|, a sound strict violation certificate because tau(G)>=p and tau(G-D)<=|Y|. For p=4, tau(G)=4 on 4+4 vertices, so the matching witness is exact. For p<4 the fixed certificate can exclude witnesses whose graph has larger cover number; search scope must retain this parameter. The optional gate ordering acts separately within the internal and root blocks and preserves the established greedy renumbering argument.

Independent replay checked the P4 equality control (38,252 clauses, 256 inputs, exact capped read vectors, sole maximal core3, U4, D3, tauG4, residual tau2, margin0) and the deliberately excluded C4 control (38,303 clauses, 256 inputs, U4, D4, tauG4, residual tau2, margin-1). The P4 run relaxes the strict threshold by one; the C4 run disables the four-cycle prohibition. Neither is a posted-gap refutation. Full metadata: scratch `core-counterexample/target-controls-independent-review.json`.

A genuine SAT candidate still needs the canonical exact live-output extension, its lift-fixed property, and the complete Lean-checked posted assumptions before it can count as a refutation. Finite UNSAT results remain computational evidence only.


## Matching-preserving 4-by-4 graph orbits

Independently enumerated all 65,536 incidence masks with the full diagonal required, using explicit square masks to reject four-cycles. Exactly 311 survive. Their orbits under simultaneous row/column permutations and transposition are pairwise disjoint and cover all 311 matrices; the 16 orbit sizes are 1,12,24,8,24,24,12,48,24,8,24,48,24,12,12,6. Maximum edge count is nine, with one nine-edge orbit. Source SHA256: `39e999ee97ed145a55e056c297f81ed436c93a5005b919943801d492502099b3`; metadata: scratch `core-counterexample/graph44-orbits-independent-review.json`.

Restricting p=4 direct-target searches to these representatives preserves completeness by relabeling graph inputs and then restoring the valid gate order. Core, read-vector, cone and cover properties are invariant under that relabeling. This exact census does not apply to p<4.

## Conditional liveness and ordered theta generators

A normalized seven-OR theta witness with a dead generator can delete all dead generators, preserving disjoint ports and leaving at most six ORs. Unused disjoint padding then gives a fixed-six instance. Therefore, conditional on the separate normalized six-OR UNSAT result, requiring every seven-OR generator to reach the final output loses no witness. This is a computational reduction, not a Lean theorem. It does not justify live-only padding unconditionally.

The optional maximum-predecessor ordering is implemented on the union of both selector ports; the reviewed greedy topological argument preserves disjointness and liveness. Inspected `or_free_and_live_sat.py`, `decode_live.py`, `or_free_and_ordered_sat.py` and `decode_ordered.py`. Independent ordered eight-OR theta positive control replay passed all 8,479 clauses and 256 inputs, and explicitly checked live reachability, disjoint oriented ports, and nondecreasing maxima. Encoder SHA256: `5cf905f9ed622a9598eb75e5117382c37c97df442b290b93cd2e34c0720f9c98`; decoder SHA256: `3ee08880224e9494634a3a8ca633b06bcc9326c1e020d4dfd2b8ecb2ed7663d4`. Metadata: scratch `free-and/theta-ordered-independent-review.json`.

A proposed first-generator graph-automorphism canonicalization was deliberately not combined with predecessor ordering: relabeling inputs can change the first gate selected by canonical topological sorting. That combination needs a joint argument. A minor cycle-specific pin/order CLI incompatibility was reported; current unpinned theta searches are unaffected.


## Exact-theta total-gate search and three-copy wrapper audit

Reviewed scratch `structural/exact_graph_sat.py` SHA256 `494ffb1a94119f0feb1f318c7141b1b351575d97010b7d07947778c1f36513fb`. Its CNF helper AST matches the previously reviewed multi-core helper. Root operation is unrestricted. One-hot earlier-wire operands, exact AND/OR truth equations, rejection of every maximal independent set, and acceptance of every graph edge imply the exact graph function by monotonicity.

All vertices in the encoded graph are nonisolated, so each variable is essential: its edge pair is accepted but its neighbor singleton is rejected. Requiring every input to occur therefore loses no exact circuit. Every nonroot gate is used later, so all gates reach the output. Dead gates may be removed, and a smaller circuit within the specified AND/OR budgets can be padded by idempotent gates of the needed types on the output. Greedy (max operand, min operand, operation) ordering and the extra-reader budget k-n+1 are valid. Fixing AND count restricts the search to that gate-type budget; it does not independently cover every circuit of the same total size.

Independent pinned theta control replay checked all 25,800 clauses, all 256 truth assignments, all-input/all-gate output reachability, sorted gate keys, four AND/eight OR gates, and five extra operand arcs. Metadata: scratch `structural/theta-exact-independent-review.json`. No eleven-gate witness or exclusion follows from this positive control.

The three-copy wrapper argument was independently checked mathematically. If A is a live eleven-gate exact circuit for the nine-edge theta graph with minimum cover four, three vertex-disjoint copies and two OR joins give an exact circuit F with 35 gates, 27 edges and cover number 12. Appending q=F OR x and r=q AND F adds two gates. q accepts singleton x and is not implicant. Every proof tree of F on an accepted pair must use both endpoints, because F rejects every singleton; combining such a tree with either another F tree or the x leaf repeats an endpoint. Thus r is a core, with every earlier gate below it, and is the only maximal core. An independent live edge-DNF output creates no new cores (edge ANDs have read-1 proofs; ORs cannot be cores) and is lift-fixed because every live OR is BelowF. Then D has 27 edges, U has 37 gates, mc=1, and the residual cover is empty: 39>38. This remains an informal conditional construction until an actual eleven-gate circuit and all Lean construction/read-vector/cover details are checked.

## Normalized free-OR AND-budget model

Reviewed `core-counterexample/normalized_and_sat.py` SHA256 `1daeb0301f7845966c457e98c72b750b69326ff4548418c2b679e8fc8ff788f0`. For common source set C, distributivity (A OR C) AND (B OR C) = (A AND B) OR C permits extraction and substitution into all later OR operands and the final OR. Absorbed gates are removed. A raw input term in the final OR would violate BelowF, so the generator-only final selection remains complete. The code imposes disjoint ports and correctly removes live-only requirements; unused disjoint dummy ANDs can pad the budget. Port symmetry and greedy source ordering remain valid. This transformation need not preserve OR count or total gate count and is not used to justify the direct target encoder.

Independent positive replays passed the normalized Fano control (20,521 clauses, 16,384 truth assignments, seven AND/twenty OR gates) and C12 control (11,964 clauses, 4,096 assignments, six AND/eleven OR gates). All selector ports were checked nonempty and disjoint. Metadata: scratch `core-counterexample/normalized-controls-independent-review.json`. No smaller-AND conclusion follows from the controls.


The exact-total-gate encoder was extended to Fano and an automatic star-cover control, reviewed at SHA256 `74b49a6ab429241eb31d805a6cd3438bbf2649d8cc1a1dfce6e4f4ebea7e710f`. The star builder and greedy reindexing preserve its function and gate types. Independent 27-gate control replay checked all 351,922 clauses, all 16,384 inputs, full output reachability, ordering and extra-reader budget 14; it has seven AND and twenty OR gates. Metadata: scratch `structural/fano-exact-independent-review.json`. The 26-gate query does not restrict the operation counts. A hypothetical 26-gate exact Fano circuit would yield, through the same three-copy wrapper, D=63, tau=21, U=82, mc=1, residual=0, hence 84>83. No such circuit is claimed.


## Fano first-input-pair orbit minima

Reviewed `structural/fano_first_orbit.py` SHA256 `e267871bb32be881bb467b4194c7d24dc6cc9c95fd07366224738334d72b9174`. Independent checks found 336 distinct permutations containing identity and closed under composition. The known graph-preserving group gives exactly four minima on the 105 unordered input pairs, allowing equal operands: (0,0), (0,1), (0,7), (2,7), ordered by (maximum input, minimum input).

This pruning is compatible with greedy gate ordering. Among all initially ready input-only gates, choose one whose pair has the least orbit minimum, and map it to that minimum. Every other ready gate has transformed key at least its own orbit minimum and hence at least the chosen one. Thus the first gate can have a representative pair. Ties in operation do not change that pair; both operations remain allowed. Newly available non-input-only gates use a larger generated-wire index. This minimum construction differs from the previously unproved first-port orbit-maximum combination.

The code adds a disjunction of four exact selector-pair conjunctions. Independent replay of the transformed 27-gate positive control verified all 351,935 clauses, all 16,384 truth assignments, the representative first pair, and sorted gate keys. Metadata: scratch `structural/fano-first-orbit-independent-review.json`. No 26-gate SAT/UNSAT result is inferred.


## Exact-function heuristic and final evidence preservation

Reviewed the direct exact-function minimizer `combinatorial-bound/exact_minimize.cpp` at SHA256 `8210b12fa20ec148bc4363ecd1314cfbf8dbb7fa92b046fd34f864e78ead759e` and its data generator. Its signature rows consist of all graph edges and all maximal independent sets, so a zero signature loss implies the exact monotone graph function. Gate edits select only earlier wires, and independent adjacent swaps/deletions update wires and output consistently. Active bit masks and fixed arrays cover the current theta/Fano sizes. This is a heuristic: a nonzero result excludes no circuit. A freshly seeded zero-loss circuit is not inspected until mutation, a benign completeness limitation that cannot create a false witness.

Independent validation checked all 128 theta seeds on all 256 assignments, all 128 Fano seeds on all 16,384 assignments, maximal-independent-set coverage, serialized masks, and a recovered 12-gate theta control. Full metadata is `combinatorial-bound/minimize-independent-review.json`. Any future heuristic witness still requires independent truth evaluation and Lean verification.

The final `free-and-2962` folder has 144 manifest payloads and one manifest file, totaling 2,104,808 bytes. Every SHA256 and file name matches the manifest; all 25 CNF headers match their clause counts. Theta seven-OR variants terminate without a SAT/UNSAT verdict at the documented 180/300-second limits, consistent with UNKNOWN. No credential, lease identifier, or network-client code was found. Its finite exclusions remain ordinary computational evidence, not Lean theorems.

The refreshed `core-counterexample-evidence.tar.gz` has 217 regular relative-path members. Every index name, size, and SHA256 matches the actual archived bytes. Its two reconnect-interrupted final jobs are explicitly INTERRUPTED_NO_VERDICT, while complete UNSAT/UNKNOWN jobs retain their full logs. No credential or active lease content was found.

## Final wrapper composition review

`WrapperMaximal.lean` (1275 lines, SHA256 `9b573b4da4a849fc5f349a9c9a361adf368e8c461b6575571178ce49f30291d1`) preserves the reviewed 1146-line `AbsorbWrapperCore` prefix exactly and copies the reviewed cone helper block exactly. Its new composition proves that all old gates and the new OR lie below the final wrapper AND, assuming all old gates reach the valid old output. Exact nonempty graph semantics and AO2 then give a singleton maximal-core set; the cone is the full range of m+2 gates. The cone identity alone does not require the semantic hypotheses.

`WrapperDominance.lean` (1304 lines, SHA256 `0950841c4735b103b08a949ca33b15fef4f613345d5a2e6884a44a50eebf6590`) preserves all 1275 prior lines. Its final lemma proves a core is uniquely maximal when it strictly contains every other core in its cone, using ReadsBack to rule out a cone cycle. The designated core need not be the last gate. Both sources have clean forbidden-construct scans and empty full compilation logs with successful validations. Neither establishes fixed-point padding or the posted target.
