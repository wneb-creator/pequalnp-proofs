# L-meta-2962 counterexample investigation

No counterexample found yet. The Python finite search checks arbitrary dead AO2 networks on C4-free bipartite graphs and can be completed to a lift-fixed exact circuit by appending a canonical DNF output. It computes all truth-table values, singleton read-once supports, pair read-once supports, implicant status, core status, maximal cores, and both the target inequality and stronger |D|+tau(D)<=|U|+mc. The read-once recurrence is exact for fan-in-two circuits without constants: an OR unions supports; an AND can create a read-once pair only by joining disjoint singleton supports.

A tight example was found and kernel-checked in scratch Equality.lean (initial six lemma version exited 0; complete hypotheses version compiled successfully for its initial structural components). Graph edges {01,02,13}. Gates: e=3 AND 1; s=1 OR 2; t=0 OR e; core=t AND s; live=0 AND s; output=live OR e. The core and t are dead; other gates may be shared with the live output. It is AO2, computes the graph exactly, and is a lift fixed point. Maximal cores={3}; D has three edges; U={0,1,2,3}; minimum cover has size 2; deleting D leaves cover size0. Therefore the target is equality 3+2=4+1+0. Dead cores invalidate any hoped strict surplus.

General equality family: edges star a-B plus edge d-b with b in B. Compute e=d AND b; S=OR B; T=a OR e; core=T AND S. Core function=aS OR e, with reread at d-b. Cone cost |B|+2, accepted edges |B|+1, cover2, one core: equality. Sharing e between several such cores saves only one gate per additional core, offset by the mc term. Sharing S between distinct centers with |B|>=2 makes a forbidden 4-cycle.

Random search completed: 1,481,447 circuits over 50 sampled C4-free bipartite graphs with n=4..8, 240 seconds; no negative margin, smallest0. The stronger inequality also survived. Complete output in /tmp/oec/pequalnp-pilot-71/core-counterexample/search.log.

Guided search started on cycles10/12/14, Heawood14, and trees10/12/14, seeded from equality P4 gadgets. Full truth tables and exact read-once supports; gate mutation/insertion/deletion and shared-gadget additions; 15-minute budget, root renewing lease.

Evaluator positive control (outside posted hypotheses): on K2,2, u=a OR b; v=c OR d; w=u AND v; core=w AND u gives |D|=4, tau=2, |U|=4, mc=1, hence target margin -1. This confirms the negative branch; K2,2 fails NoFourCycle, so it is not a refutation.

Padding observation: any finite valid AO2 network may be treated as entirely dead and followed by an independent canonical DNF output for G. New AND edge gates are read1; new OR gates have both operands implicant. Therefore no new cores occur, old U/D/mc stay fixed, and the resulting output is exact and lift-fixed. Counterexample search on arbitrary dead networks is sound as a route to a posted-statement counterexample.

Input-leaf bound check for single_core agent: 210,593 seeded/mutated Heawood networks over45 seconds; smallest |U| minus number of distinct original input leaves is0, no violation. This is computational sanity for the proposed union-cone lemma.

Fano/Heawood support analysis: all16,384 vertex subsets enumerated. Gain |E[S]|+7-tau(G-E[S]) maxima by support size0..14 are [0,0,1,2,4,5,7,8,10,13,16,18,21,24,28]. There are336 graph automorphisms, independently checked edge-preserving; support9 has15 orbits, only5 permit gain>=11. Representatives959,1951,1967,1979,2975. Full data and support/edge stabilizer orbits are under scratch core-counterexample/fano-*.json. Maximal independent sets:37 (2size7,14size5,21size4). These computational data guide structural agent SAT searches.

Read2026-11-25: Jukna, Disproving the Single Level Conjecture, primary author PDF https://web.vu.lt/mif/s.jukna/ftp/single1.pdf . The counterexamples use saturated non-bipartite extensions, which contain large bicliques. They do not directly supply a counterexample under the current bipartite NoFourCycle hypotheses. Pair-adjacency representation alone can accept larger independent sets, which our BelowF requirement excludes.

Completed guided runs: 12,591,400 evaluations in900 seconds for cycles10/12/14, Heawood14, trees10/12/14; 3,823,400 evaluations in600 seconds for branched tightcore seeds onHeawood and subdividedstars10/12/14/16. No violation of target or stronger bound. Counts include repeated states; searches are heuristic, not exhaustions. The archives retained one best state per accepted-edge mask/maxcorecount, so neutral topological exploration was limited. A new dense-cyclic-gamma search includes neutral moves and annealing.

Important conditional reduction: if the global lower bound |E(G)|+tau(G)-1 is known forG, it implies the present core-cover bound. Compress the closed union of maximal-core cones into |U| gates, OR their outputs inmc-1 gates, and OR with a canonical residual-edge circuit costing |E(G)\D|+tau(G-D)-1. Monotonicity and BelowF imply that the resulting function is exactly fG, and the combined size is |U|+mc+|E(G)\D|+tau(G-D)-1. Apply the global bound and cancel residualedges. Emptycore/residual cases need separate handling. The compression/construction is informal here, not Lean-checked. This explains why tree/cycle counterexample searches are unpromising given the repository existing global bounds for those classes.

One-extra-fanout acyclic-gamma argument (informal): if a closed cone hasg gates andg used input leaves, exactly one nonoutputwire has fanout2 andall othersfanout1. Its sharedwireW has a read-once cone. Replacing bothW occurrences byz in the outer formula and settingz tofalse/true gives two read-once formulasf0,f1 on disjoint outsideinputs, with output=f0 OR(W AND f1). BelowF forcesf0 no singletonterms, so its quadraticgraph is a starforest underbipartite NoFourCycle. If f1=true, W alsoBelowF andadds a disjointstarforest. Otherwise newquadraticedges formA×B from singleton-supports ofW,f1. NoFourCycle forces thiscrossgraph tobe astar; bipartiteness andNoFourCycle prevent a newcenter from meetingany existingstarcomponent twice, hence theunionremainsforest. Formalization unfinished.

SAT symmetry independently checked: after sorting eachbinarygate inputs a<=b, everyDAG admits topological order nondecreasing lexicographic(b,a,operation). Greedily pick availablegate withminimumkey; newlyavailablegates necessarily read thenew highestwire andtherefore have strictlylargerb. No gateCSE/dedup restriction wasassumed.

MIS-compressed evaluator: for monotone AO2 gates, BelowF is equivalent torejecting all maximal independentsets. Store truth bits onlyfor these rows plusedgepairrows. Exactmatch withfull2^14 evaluator on10,000 seeded/mutatedFano networks. Order3plane26 has52edges and704MIS; data in plane13-mis.json. Current15min search uses fullplane52edges andC4free subgraphs44/40edges, allowsoneortwo overlappingdensecores, andtests cyclicgamma withatleasttwo-thirds ofedges. NooldL-meta-2602 goalisbeingworked; these areinstances ofhelduniversal L-meta-2962.

## 06:57 UTC: exact MIS semantics and component searches

The order-3 plane run finished after 900 seconds: 2,283,000 circuit evaluations,
1,013,115 eligible cases with a cyclic accepted-edge graph and at least two thirds
of the graph edges accepted. No target or stronger-bound counterexample appeared.
Best target margins were 2 for the full 52-edge plane, and 1 for the sampled
44-edge and 40-edge subgraphs. These are heuristic evaluations with repeats,
not an exhaustive census. Full stdout is in scratch `plane-dense.log`.

The sparse evaluator checks each graph edge and every maximal independent set.
This is exact for positive AND/OR circuits: any input where the graph function
is false extends to a maximal independent set, so monotonicity reduces BelowF
to rejection of those rows. READ-1 tests use the exact singleton/pair recurrence,
with singleton READ-1 support empty at every AND gate. Ten thousand random Fano
networks were compared against the independent full truth-table evaluator; all
results matched, including maximal cores, D, U, and both numerical margins.

Separate component checks on saved candidates and fresh mutations found no
failure in 187,631 evaluations of
`|D| <= OR(U) + mc` and `tau(G) - tau(G-D) <= AND(U)`.
A second 45-second run checked the stronger `tau(D) <= AND(U)` on 227,440
networks, also without a failure. Both component margins attained zero.
These tests do not prove either proposed decomposition.

Explicit full-plane seeds are saved as `explicit-one-over-plane7.json` and
`explicit-one-over-plane13.json`. Given a star decomposition `W OR (a AND B)`,
replace its final join by `(W OR a) AND (W OR B)`. The function is unchanged,
and the root is a repeated-read core. The Fano example has 28 gates (7 AND,
21 OR), all 21 edges in D, and target margin 1. The order-3 example has
65 gates (13 AND, 52 OR), all 52 edges in D, and target margin 1.

Parent authorized a new 20-minute phase optimizing three objectives separately:
OR(U)+mc-|D|, AND(U)-tau(D), and AND(U)-tau(G)+tau(G-D). It uses both planes,
allows the uncharged gate type to increase, and starts with the explicit seeds,
shifted overlapping copies, and randomized star/guard constructions. Its complete
log is `cuts-optimized.log`; findings will be appended after completion.

## 07:04 UTC: normalized AND-budget SAT

Implemented `and_free_or_sat.py`: each of k AND gates takes two arbitrary nonempty
OR-subsets of original inputs and earlier AND outputs. The final output is an
OR-subset of AND outputs. This represents every monotone circuit with at most k
AND gates; direct input terms at the final OR are impossible under BelowF. A
smaller circuit can be padded using idempotent AND gates.

Two six-AND Fano instances are running with 300-second solver limits: exact fG
(all 21 edges accepted and all 37 maximal independent sets rejected), and the
weaker condition accepting the fixed seven-edge diagonal perfect matching while
rejecting those 37 maximal independent sets. The latter would already produce
an accepted-edge graph with matching number 7. No SAT/UNSAT result is claimed yet.

The pinned seven-AND positive control passed. Its decoded binary circuit has
7 AND and 20 OR gates and computes Fano exactly on all 16,384 assignments.
Independent status_review checked both the encoding and all 16,715 pinned CNF
clauses and all truth assignments. The decoder now replays all CNF clauses itself
before checking semantics. Exact-size instance: 3,395 variables, 12,742 clauses;
matching-only instance: 2,625 variables, 9,942 clauses.

An optional ordered mode was separately reviewed: order the two interchangeable
AND ports lexicographically; order AND nodes by nondecreasing largest selected
source-wire index using greedy topological ordering; require every AND output to
be consumed or output. Dead-node deletion and idempotent padding preserve
completeness. The ordered seven-AND control also passes CNF and full truth replay.
