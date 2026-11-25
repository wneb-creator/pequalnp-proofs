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

## 07:17 UTC: completed component optimization and variable-graph SAT

The 20-minute separate-component optimization finished: 6,476,400 evaluations,
3,007,729 eligible cyclic accepted-edge cases. All six minima were zero: each of
OR+mc-|D|, AND-tau(D), and AND-tau(G)+tau(G-D), on both Fano and the order-3
plane. No component or target counterexample was found. Across the completed
search phases in this agent, the count is 30,570,811 evaluations (with repeated
circuits and overlapping tests; this is not a count of distinct networks).

Both initial six-AND Fano SAT jobs and their reviewed ordered follow-ups reached
their 300-second limits: UNKNOWN in all four cases. This does not establish any
lower bound for six-AND Fano circuits.

A new exact finite encoding lets the C4-free bipartite graph vary. It fixes a
perfect matching, allows all other cross edges to be Boolean variables, forbids
every four-edge square, and enforces output(S) implies an edge exists inside S
for every Boolean assignment S. It requires acceptance of the matching pairs.
The same arbitrary-OR-subset AND normal form is used. Independent review passed
both the graph constraints and the full-row BelowF implication.

Results:

* Four-by-four graph, three AND gates, 256 truth rows: UNSAT; solver reported
  0.52 seconds wall time, 9,920 conflicts (5,013 variables, 20,235 clauses).
* Five-by-five graph, four AND gates, 1,024 truth rows: UNSAT; solver reported
  156.24 seconds wall time, 1,906,360 conflicts (29,966 variables, 130,123 clauses).
* Positive control: four AND gates compute the four-edge matching, expanding to
  4 AND plus 3 OR binary gates. All CNF clauses, C4-freeness, and all 256 truth
  assignments were replayed independently.

These are solver results, not Lean theorems. Restricting an arbitrary larger
counterexample to endpoints of four or five accepted matching edges, then
eliminating the resulting zero constants, would give one of these finite
instances. Thus the UNSAT findings provide evidence for the stronger AND-cover
claim through AND budget four, but do not prove the general claim.

Direct target encoder `unknown_core_target_sat.py` now searches variable graphs
on four plus four vertices with a fixed diagonal matching witness. It designates
one or two incomparable terminal cores and makes every other gate reach one of
them, so U is the full gate set and the maximal cores are exactly the designated
roots. Core tests use full BelowF, not-both-implicant operands, and exact root-AND
READ-1 computed from child pure-OR singleton supports. A chosen vertex set covers
the residual graph. The inequality tested is |D|+p > g+mc+|Y|, where p is the
matching witness cardinality. Since tau(G)>=p and tau(G-D)<=|Y|, every model is
an actual numerical violation. With p=4, tau(G)=4 exactly. Parent/reviewer were
notified of the p<4 undersearch caveat.

Direct encoder controls: the embedded P4 equality network decodes to margin 0;
the known K2,2 excluded-assumption example decodes to margin -1 when the no-C4
constraint is deliberately disabled. Both replay all CNF clauses and all truth
assignments. A real model still requires the independent canonical live-output
extension and Lean checking before it would refute the posted statement.

## 07:27 UTC: direct-target result, graph symmetry, and equivalence

The direct variable-graph query with nine gates and one core returned UNSAT in
263.02 seconds wall time (2,804,391 conflicts). Its scope is all C4-free bipartite
four-by-four graphs containing a perfect matching, after relabeling that matching
to the diagonal. The ten-gate/two-core query reached 300 seconds: UNKNOWN.

An independent complete census found 311 C4-free four-by-four graphs containing
the diagonal matching. Simultaneous row/column permutations and transposition
partition them into 16 orbits. The maximum edge count is nine; its graphs form
one orbit, representative bit mask 38371. Reviewer independently checked all
65,536 Boolean matrices, all square constraints, and all 48 matching-preserving
relabelings. The p=4 direct-target follow-up may therefore restrict its graph to
these 16 representatives without losing any witness. This does not apply to the
p<4 case. An orbit-reduced ten-gate/two-core follow-up is running.

The stronger AND-cover test was also explored through fixed antichain-code CNFs.
The six 2-subsets of four coordinates give a five-AND CNF accepting exactly a
six-edge matching on pair assignments. No C4-free bipartite graph can contain
that matching and dominate the entire CNF: a 36-edge-variable completion SAT is
UNSAT. Likewise, all four isomorphism types of seven 2-subsets selected from five
coordinates give six-AND CNFs with no such graph completion. Each completion
instance has 50 variables and 534--538 clauses after reducing full truth tables
to 85--89 minimal true assignments; all four are UNSAT immediately. These are
auxiliary tests of the stronger claim, not refutations of the posted statement.
Agent combinatorial_bound supplied independent degree/counting explanations.

Independent mathematical review of the global-bound equivalence:

1. Suppose the exact gate lower bound m >= |E|+tau(G)-1 is true for every
   nonempty bipartite C4-free graph. Compress the union of maximal-core cones
   into |U| gates, OR their mc outputs with mc-1 gates, and combine with a star
   circuit for G-D. All core outputs are below fG and accept the pairs in D,
   so their OR together with f(G-D) computes fG exactly. The size is
   |U|+mc+|E-D|+tau(G-D)-1. If the residual is empty, use only the OR of cores;
   its size |U|+mc-1 gives the same cancellation. D empty is trivial. Applying
   the global lower bound yields the posted core-cover inequality.
2. Conversely, prune any circuit A computing nonempty fG to its output cone;
   let F be its output and m its original gate count. Choose any input x and
   append q=F OR x and r=q AND F. The q wire is nonimplicant (singleton x);
   F is implicant. No READ-1 pair proof can pass through r because F has no
   singleton proof. Thus r is a core, dominates every previous core, and
   has cone size at most m+2. Append an independent canonical graph-DNF live
   output so that the earlier block is dead and the whole circuit is lift
   fixed. This preserves the sole maximal core r and gives D=E. The posted
   inequality yields m >= |E|+tau(G)-3.
3. Apply this construction to the disjoint union of three copies of G. Three
   copies of A joined by two OR gates cost at most 3m+2. Both |E| and tau add
   across components, so the posted inequality gives
   3(|E|+tau(G)) <= 3m+5. Integrality implies m >= |E|+tau(G)-1.

Thus the posted statement is informally equivalent to the global exact monotone
binary-gate lower bound on bipartite C4-free graph functions. The transformations
are not yet Lean formalized. In particular, one gate saved below the canonical
star bound could be amplified into a genuine core-cover counterexample using
three disjoint copies and the wrapper, even when the unamplified small graph
has no direct core-cover counterexample.

## 07:32 UTC: normalized auxiliary model

`normalized_and_sat.py` adds a sound restriction for the free-OR AND-budget
model: the two operands of each AND select disjoint sets of source wires. If
both operands contain common source set C, the identity
(A OR C) AND (B OR C) = (A AND B) OR C
extracts C and routes it into all later OR operands and the final OR. Gates
whose residual operand becomes empty are deleted. The resulting circuit uses
no more ANDs; unused ANDs of two distinct inputs pad the budget. Consequently,
the normalized model removes the old live-only requirement. Port symmetry and
greedy source ordering remain valid. This normalization can increase OR count
and must never be imposed on a total-gate-count query.

Independent reviewer checked this completeness argument and the implementation.
Pinned positive Fano/seven-AND and C12/six-AND controls passed full CNF replay
and full truth tables. The C12 control expands to six AND plus eleven OR gates.
The normalized C12/five-AND query returned UNSAT in 9.36 seconds wall time,
with 279,744 conflicts. This is a solver finding, not a Lean theorem.

The orbit-reduced ten-gate/two-core direct-target query still timed out at 300
seconds (UNKNOWN). At 07:31 UTC, after parent renewal, launched the normalized
exact Fano/six-AND query and a normalized variable-graph six-by-six/five-AND
query, each capped at 300 seconds. The latter has 4,096 full truth rows,
168,362 variables, and 767,989 clauses. No further search expansion is planned
without a new candidate or strategy.

## 07:39 UTC: interruption and final research handoff

The environment disconnected/reconnected during the final two normalized
auxiliary jobs. On resumption, their process IDs 16191 and 16194 were defunct
(zombie state), although earlier process-presence checks had suggested survival.
Their complete available logs stop around 204--205 CPU seconds, without a
SAT/UNSAT/UNKNOWN footer, and their solution files contain no result. These two
instances are therefore **INTERRUPTED, NO VERDICT**. They are not reported as
300-second timeouts or UNSAT results. No duplicate jobs were launched.

No posted-statement proof or counterexample was found by this agent. The checked
P4 equality witness remains a valid Lean partial already delivered to parent.
All computational evidence, scripts, complete available stdout/stderr, CNFs,
metadata, controls, and candidate networks are being snapshotted in
`results/orch/core-counterexample-evidence.tar.gz`, with an index generated from
actual archive members. `STATUS.json` in that archive records final query states.
The separate parent archive may also contain copies of this evidence.
