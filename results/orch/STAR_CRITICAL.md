# Critical-edge structural analysis for L-meta-2448

Research notes, 2026-11-25 UTC. These are mathematical observations and obstacles, not a proof of the posted theorem. Root holds and renews the lease. The conditional restriction lemma is separately Lean-checked in CriticalRestriction.lean.

## Safe prefix progress

In a backward-reading circuit, replacing only gate j without changing its index or earlier gates preserves all earlier gate values and strict ancestor cones. The backward-reading hypothesis matters for syntactic cones; it must first be obtained by normalization. Therefore an induction on the first nonstar gate, or maximization of the initial star-profile prefix among minimum circuits, is sound. Descendant ownership can grow after decreasing an earlier gate, so maximizing the total count of star gates does not provide the same progress argument.

If an exchange also deletes earlier support gates, preservation requires a separate proof through the reindexing and changed cones. It is not automatic from the one-gate observation.

## Optimal P4 obstruction to a stronger pivotal-star claim

The graph on a,b,c,d with edges ab, ad, bc is a path. Its exact graph function has this four-gate circuit:

1. t = b AND c.
2. A = a OR t.
3. B = b OR d.
4. F = A AND B.

By distributivity and absorption, F = ab OR ad OR bc. The last AND owns ab and ad, but not bc, because its earlier AND ancestor t is true on bc. Thus its owned graph edges form a star around a. However, forcing the last gate false loses all three graph edges, which have no common endpoint.

Four gates are minimum: all four variables are essential. A three-gate binary circuit involving four essential inputs must be a read-once binary formula. At its root, an OR decomposition would disconnect the graph, and an AND decomposition would disconnect its complement. Both P4 and its complement are connected. Unary or constant gates cannot improve the three-gate bound. This minimum argument is mathematical here, not a new Lean certificate.

Consequently even minimum circuits can have critical graph edges that are not owned by the gate, and their critical-edge family need not be a star. Any bridge to CriticalRestriction must use bad ownership specifically, or modify the circuit globally. The example does not refute the posted existential theorem: all its AND ownership profiles are stars.

## Pair-clean prefixes imply global soundness of their AND gates

Assume every AND before or at j rejects every singleton and every nonedge pair. Then every such AND is globally below the graph function. Induct on the AND order. Expand each operand through its OR-only predecessor paths until reaching either a variable or an earlier AND. A true earlier AND already implies the graph function by induction. If neither witness is an earlier AND, the two true variable witnesses make the current AND true on their singleton or pair, so pair soundness supplies a graph edge in the assignment. The same argument handles repeated witnesses by singleton rejection. Nullary true ANDs are excluded by singleton/empty-input soundness, and an empty graph or zero-variable case needs that empty-input clause explicitly.

This is stronger than the incorrect statement that an isolated pair-clean AND is globally sound: a three-variable conjunction accepts no pairs but may accept an independent triple. Its earlier two-variable AND is necessarily dirty, so it does not contradict the prefix claim.

Possible use: choose an earliest pair-dirty AND, whose operands are ORs of variables and already safe AND signals. New false positives come from products of linear variable supports. A full proof still needs a cost-preserving exchange or an accounting argument for shared OR gates; this observation alone does not establish the requested normal form.

## Safe bypasses and the actual gate-cost obstacle

When P is a previously computed signal globally below the final graph function, the local rotation (A OR P) AND B to (A AND B) OR P decreases nothing outside the graph function and retains the old gate value wherever needed. The surrounding monotone circuit therefore remains exact. This uses the same two gates if the inner OR node is private. If that OR has other consumers, the rotation can require copying a gate; it is not a free exchange for the actual all-gates objective. OR gates would be free in a pure AND-count argument, a different objective.

The separate file private_support_counterexample.json supplies an eight-vertex graph with ten edges and a fifteen-gate exact circuit. Every support OR of its dirty matching gadget is shared by an outside clean star. The graph has no triangle or four-cycle. It therefore refutes an unconditional private-support lemma. Its recorded circuit has seven AND gates and eight OR gates, so it also refutes an unrestricted lower bound of |E|-1 on the number of OR gates. The star-cover construction uses thirteen total gates, so this is not a minimum-circuit counterexample. A correct total-size lower bound must allow a trade between extra AND gates and saved OR gates.

A candidate sharpening attaches one private leaf to each outside star center 4,5,6,7, using new vertices 8,9,10,11. Extend each reused OR sum by its leaf before the corresponding center AND. This gives a twelve-vertex, fourteen-edge graph and a nineteen-gate dirty circuit. Its vertex-cover number is six: the four pendant edges together with 01 and 23 are a perfect matching, and centers 4,5,6,7 plus vertices 0,2 give a six-vertex cover. Thus the dirty circuit attains the canonical bound |E|+tau-1=19. Its first bad AND still has the disjoint pivotal edges 01 and 23. MINIMALITY IS UNVERIFIED: equality with an upper bound is not a lower-bound certificate. If minimum, this would refute a claim about every minimizer but still admit a good nineteen-gate star circuit, so it would not refute the posted existential theorem.

No proof or counterexample to the posted least-circuit ownership statement has emerged from this analysis. The optimal P4 example and the shared-support example invalidate stronger local shortcuts but leave the actual statement unresolved.

## Minimum AND count does not exclude empty ownership

For the P4 function ab OR ad OR cd, the circuit (a OR c) AND (b OR d) AND (a OR d) has five total gates and two AND gates. Its last AND owns no graph edge: the earlier AND is already true on every graph edge. Two AND gates are optimal for this function, since a single AND with arbitrary OR wiring can produce only one biclique after singleton outputs are excluded, and P4 is not a biclique. The total gate count is not optimal, since four gates suffice. Therefore minimizing only the AND count does not prove that every AND owns an edge; a proposed exclusion must use the full size objective. This is a mathematical example, not an additional Lean-checked result.

## Clean readers of edge-containing OR supports

In a backward-reading binary monotone circuit for a triangle-free graph function, suppose an AND gate is globally below that function and one operand has OR-only paths from both endpoints u,v of an actual graph edge. Its opposite operand rejects every singleton. Indeed, if it accepted singleton w, the AND would accept both pairs uw and vw. If w equals an endpoint, it would accept a singleton, impossible for a graph function. Otherwise global soundness would make uw and vw graph edges, producing a triangle with uv.

Every accepted graph-edge pair therefore activates an earlier AND in the opposite operand's OR frontier; the current AND owns no graph edge. In a minimum circuit, at least one such frontier AND must be globally dirty. If all were globally below the graph function, the singleton-silent operand itself would be globally below it; bypassing the current AND to that operand and deleting the resulting copy would contradict minimum size. This is a mathematical deduction, not yet formalized here.

This connects clean readers of shared supports to dirty components and identifies empty-owning AND gates that might fund an exchange. No global cost bound or normalization theorem follows from the observation alone.
