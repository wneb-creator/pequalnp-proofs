# Clean demasking strategy

This is a mathematical strategy note, not a Lean proof of L-meta-2602.

## Exact semantic surgery

Let a monotone circuit compute F, and let an internal wire g compute a function satisfying g <= F on every assignment. Treat the occurrences of this wire as an independent input of the remaining circuit, and replace all of them by false, obtaining C[g:=0]. Then

    F = g OR C[g:=0].

If g is false, replacement changes nothing. If g is true, F is true by the hypothesis, and the restored OR is true. Every direct consumer of g simplifies after replacement: an AND consumer becomes false, and an OR consumer becomes its other operand. The resulting false wires and repeated inputs can be simplified without new gates. Retaining the original computation of g and adding at most one final OR therefore saves at least fanout(g)-1 gates. A clean wire with at least two distinct consumer gates cannot occur in a minimum circuit.

A direct AND consumer of a clean wire can also be bypassed immediately: replace AND(g,h) by g. This changes no assignment where g is false, and any possibly enlarged output on an assignment with g true is already allowed because g implies F. Thus a minimum circuit has no direct AND consumer of any clean wire.

Both statements need a formal reindexing/simplification lemma before they can be used in Lean. They concern gate count, not just expression identities.

## Why local bypass alone is insufficient

The four-gate circuit

    g = x AND y
    a = g OR z
    b = g OR w
    out = a AND b

computes xy OR zw and kills both formal derivatives at xy. None of its four gates can simply be bypassed to an operand while preserving the function. Global demasking g gives the three-gate circuit xy OR zw.

There is also a bipartite example with only one gate of double-reread overhead:

    g = x AND y
    h = p OR g
    a = h AND y
    b = q OR a
    out = h AND b

It computes xy OR py OR pq, and both derivatives at the leaf edge xy are false. Every AND output implies the final function. Its five gates compare with the ordinary four-gate implementation xy OR p(y OR q). Thus a universal two-gate double penalty is false even for a bipartite forest. The earlier three-edge-path experiment marked the middle edge, not a leaf edge.

The root's bowtie counterexample is even stronger: an eight-gate circuit on two triangles sharing a vertex whose ordinary minimality is supported by the SAT solver, not certified in Lean, has a double edge, while all of its AND outputs are clean. Therefore clean demasking can preserve size and destroy double reread. Bipartiteness is essential to a further rigidity argument.

## Conditional route for the projective plane

If every AND output is clean, repeatedly extract the earliest remaining AND. Its residual inputs are ORs of literals. The extracted product is a biclique in the target graph; the absence of rectangles makes it a star. Demasking costs no extra gates because at least one consumer disappears before adding an output OR. If a residual AND becomes false, or an extracted clean wire has several consumers, there is a strict saving.

After all extraction, a flat star circuit remains. In a rectangle-free graph a nontrivial linear OR cannot be shared between distinct star centers, since two shared neighbors would form a rectangle. Repeated centers can be merged with a gate saving. This should give the standard lower bound

    number of incidences + vertex-cover number - 1.

For the plane this is 52+13-1=64. Equality would force exactly thirteen stars and exactly one occurrence of each incidence. The checked mixed-cover lemma shows that those thirteen centers must all be points, or all be lines.

The remaining equality argument can use one fixed orientation, say point-centered stars. For an incidence (p,l), its owner is the unique p-star. Before the first double collision, a later accepting AND with center q different from p can propagate this edge only through its point-side operand; its line-side operand must already be true at singleton l. Thus the derivative in the p direction survives. A clean wire cannot branch under equality. A dirty point-side OR wire can feed only the star with its singleton center, so branching into two accepting ANDs would repeat that center. A dirty line-side OR wire cannot carry the marked edge into a later accepting AND before a collision unless the center p is reused. This suggests there is no first collision.

This paragraph is a proof plan. Formal gaps remain in the extraction-cost accounting, classification of equality in the OR networks, and the first-collision invariant. Dirty AND gates are not handled at all by this route; the global demasking identity cannot restore a dirty gate at the output because it may accept forbidden assignments.

## Direct clean-circuit accounting

A more economical version may avoid constructing the entire flat circuit. Assume every AND is clean, and choose a minimum-size circuit among circuits with this property. Both surgeries above preserve the property: downstream functions decrease under false substitution; under bypass they can increase only on assignments where the clean wire is true, hence where F is already true.

Every wire with empty singleton support is clean: it is assembled by OR from clean AND outputs, since no raw input has empty singleton support. Such wires have exactly one consumer in a pruned minimum circuit, except the output, and their consumer cannot be an AND. Consequently each AND has two nonempty singleton supports. Bipartiteness forces those supports to lie on opposite sides, and no rectangle forces one of them to be a singleton. Thus every AND has an assigned nonempty star, obtained from its singleton supports. The assigned stars cover all graph edges, by considering the earliest AND accepting a given edge.

Let a be the number of AND gates. Separate OR gates with two nonempty singleton supports from OR gates with at least one empty support. The empty-support wires form a forest whose leaves are AND outputs, whose internal nodes are ORs of two empty-support wires, and whose exits are either a mask OR (one empty and one nonempty operand) or the final output. Each component with k AND leaves requires k-1 internal ORs, and each component not ending at output requires one exit mask. Thus at least a-1 OR gates belong to this empty-support/mask class.

Any nontrivial singleton-support OR (support at least two) belongs to a unique assigned star center: if its support reached stars at two different centers, those two shared neighbors would form a rectangle. For a center c with a_c assigned AND roots and combined neighbor set U_c, the positive-support OR network needs at least |U_c|-a_c gates. This is the elementary union-network bound: a binary union can reduce the number of components among its leaves by at most one. Mask ORs do not grow singleton supports and do not help this count. Summing yields at least |E|-a positive-support ORs, since the stars cover all edges.

The total is therefore at least a+(a-1)+(|E|-a)=|E|+a-1. The assigned star centers form a vertex cover, so a is at least the vertex-cover number. For the plane, equality at64 gives a=13, distinct centers, no duplicated incidences, and pure orientation by the checked mixed-cover bound. This direct accounting still needs formal surgery, forest-counting, union-network-counting, and equality-trace lemmas. It does not address dirty AND gates.

## Finite evidence

An independent semantic-state enumeration on four inputs considered all graphs containing marked edge (0,1), with full truth tables and both derivative bits. Through six gates it found ordinary minima for all 31 non-complete graphs and double circuits for the same 31 graphs; no double circuit occurred at the ordinary minimum. K4 has ordinary minimum greater than six. This duplicated a stronger search already performed by status_review, and was stopped when root identified the duplication. The script and complete logs are archived in results/orch/search/clean-demasking/all_graphs_four.py and all-graphs-four-final.log. This evidence is not a Lean result.
