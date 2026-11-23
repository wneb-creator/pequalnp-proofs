# A graph bound for binary circuits computing OR operators

This is an informal proof, not a Lean proof. It is stronger than the one-NOT claim when every variable occurs in at most two target sets, but it does not settle arbitrary variable degree.

Let d(v) be the number of target outputs containing input v, and let N1 and N2 count inputs with d(v)=1 and d(v)>=2 respectively. Assume distinct inputs with d(v)>=2 have distinct singleton output vectors. For a linear family of target sets, that condition follows because equal columns of weight at least two would put the same two variables in two different target sets.

Claim: every fanin-at-most-two Boolean circuit with g gates computing these OR outputs has

    g >= N1 + 2*N2 - m.

If the circuit contains a unary NOT gate, then g >= N1 + 2*N2 - m + 1. Gates may otherwise compute arbitrary Boolean functions.

Prune every gate with no path to a designated output. Discard inputs with d(v)=0 from the counting. Add a separate sink vertex and one edge for every designated output. An internal wire used as an output therefore contributes an output edge as well as its ordinary consumer edges. Count repeated argument occurrences as parallel edges. Ignore invalid or future wire references, which denote constants under the actual sequential semantics.

Every remaining gate has augmented outdegree at least one. Every input with d(v)>0 has outdegree at least one. Let D consist of the d(v)>=2 inputs having circuit outdegree exactly one. For each v in D, follow its unique outgoing edge and continue through gates of outdegree one. The path cannot end at an output sink: otherwise v would affect at most one output. Finiteness and acyclicity therefore make it reach a first gate b(v) with outdegree at least two.

The map b is injective. Suppose b(v)=b(w) for distinct v,w in D. All paths from v to any output pass through b(v), and the same holds for w. Freeze all other inputs to zero. The entire output vector is then a function of the single Boolean value on b(v), so can have at most two possible values. But the assignments 0, e_v, e_w produce three distinct output vectors: zero, the nonzero column of v, and the different nonzero column of w. Contradiction. This also covers chains meeting before their first branching gate: such a meeting yields the same eventual b.

Let E be the number of edges including the m sink edges, and let

    R = sum over gates u of (outdegree(u)-1).

Injectivity gives R >= |D|. Inputs contribute at least N1+2*N2-|D| edges. Thus

    E >= N1+2*N2-|D| + g + R >= N1+2*N2+g.

Fanin at most two gives E <= 2*g+m, proving the claim. A surviving unary NOT improves this to E <= 2*g+m-1, giving the strict bound. If every unary NOT was pruned, at least one gate was removed; applying the non-strict bound to the pruned circuit gives the same strict bound for the original circuit.

If every target degree is at most two, then N1+2*N2=sum_v d(v)=sum_i |S_i|, and the desired exact bound is g>=sum_i(|S_i|-1). In particular, the K5 star family (10 edge variables,5 outputs) requires at least15 gates over an arbitrary binary basis; a circuit containing a NOT gate requires at least16.

Remaining gap: for degrees above two, this method only counts the first branching event of each deficient input. Later branching events can merge different input influences. A proof for L-meta-951 needs to use the one-NOT restriction to control that later sharing or a different invariant.

## Stronger bound after removing antitone-oracle edges

For an AND/OR circuit with an additional free antitone Boolean input z(x), the preceding proof strengthens. Remove all edges from z and retain just the ordinary input nodes and AND/OR gates that have a remaining path to a designated output. Let k be the number of retained gates and r the number of deleted z argument-occurrences into those retained gates. Every retained gate has positive outdegree. Its fanin can now be zero, one, or two; in total the retained graph has E <= 2*k-r+m edges after adding output sinks.

Every required input-output incidence still has a path in this graph. Without such a path, that output depends on the input only through the antitone parameter z, while its decoder is monotone in z. It could not have the required increase from0 to1 on the corresponding singleton input.

The first-branch injection remains valid, but now requires incomparable singleton output columns. If two unique chains meet at b, fix all other ordinary inputs to0. The output vector has the form H(b,z) for a monotone map H from two Boolean coordinates. Let (b0,z0), (bu,zu), (bv,zv) be the channel values on0,e_u,e_v. Antitonicity gives zu,zv <= z0. Since H(b0,z0)=0 and each singleton output vector is nonzero, neither (bu,zu) nor (bv,zv) can be below (b0,z0). Consequently b0=0 and bu=bv=1. The two pairs (1,zu),(1,zv) are comparable, so their output vectors are comparable. Contradiction.

For a linear family, columns of degree at least2 are incomparable: if one were contained in another, their two variables would occur together in at least two target sets. The same edge count therefore yields

    k >= N1+2*N2-m+r.

In an actual one-NOT circuit, replacing the NOT node with the free parameter leaves at most g-1 retained AND/OR gates. If a path from the NOT output to a designated output exists, then r>=1, and hence

    g >= N1+2*N2-m+r+1 >= N1+2*N2-m+2.

If the NOT does not reach any output, remove it and use the original monotone lower bound. Thus a potential counterexample to L-meta-951 must have total variable-degree excess sum_v max(d(v)-2,0) at least3. This is only a necessary condition, not the unrestricted proof.

Audit notes: repeated argument positions are parallel edges and are counted with multiplicity. Invalid or future wire reads are constants and create no dependency edge. A retained ordinary predecessor of a retained gate is necessarily retained, so pruning never replaces a genuine positive dependency with a constant. Gates whose only nonconstant input was z may become indegree0 and remain in the graph; this only reduces E. Outputs cannot be the antitone NOT wire because target ORs are nonconstant increasing functions. Output sinks are separate even when output wires are internal. The linearity and size-at-least2 hypotheses ensure distinct target functions, although distinct sinks would also handle repeated designations in the graph argument itself.
