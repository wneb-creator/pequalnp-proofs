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
