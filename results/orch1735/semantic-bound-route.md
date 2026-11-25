# Coarse semantic edge bound: investigated route and obstruction

The sufficient goal is a universal constant K with |E(G)| <= K (size(C) + 1)
for the least TopForm circuits in the posted statement. Since Ustar is a subset
of the edge set, this would finish the gap. No proof of that bound has been
obtained here. The library search is owned by lemma_route; its current result is
that known reductions of this generic coarse bound return to Ustar, while a
checked bounded-depth result requires incomparable dirty AND gates.

## Why pair evaluations alone cannot establish the proposed bound

There is a useful asymptotic obstruction to a proof that uses only evaluations
on singleton and two-vertex inputs. Put q = 2^k and take the affine incidence
graph with point vertices (a,b), line vertices (s,t), and adjacency b = sa+t over
the field of q elements. It has 2q^2 vertices and q^3 edges; two distinct points
lie on at most one such line, so the graph is bipartite and has no four-cycle.

On an input containing one point vertex and one line vertex, each coordinate
bit and its complement can be read as an OR of the appropriate one-hot vertex
variables. The two rails are both positive ORs, rather than a NOT operation.
Dual-rail Boolean field arithmetic then tests b = sa+t using AND and OR gates.
Point-presence and line-presence factors reject singletons and same-side pairs.
The resulting pair-slice computation uses O(q^2 log q + poly(log q)) gates.
The constants and a finite Lean implementation have not been constructed;
this is a mathematical construction sketch, not a machine-checked result.

This construction supplies no guarantee on larger independent sets. It is not
a counterexample to the posted statement: neither the full graph-function
semantics nor leastness nor TopForm has been established. It explains why a
successful charging argument must use rejection of arbitrary independent sets,
or exploit leastness and TopForm, beyond the accepted pair pattern.

## Local surgery observation

If an internal monotone gate is false on every graph-edge pair, substituting
false for it preserves every positive minterm at the output and cannot create
new positive inputs. Hence it preserves the full graph function. Turning that
substitution into a strictly smaller IsAO2 circuit requires the usual constant
cleanup and removal of dead gates. This observation does not itself bound the
number of pairs carried by any remaining dirty gate.

The unresolved step is a cost bound for nested dirty gates. At the first clean
AND accepting an uncovered edge, that edge may already be true in one or both
dirty operands. No-four-cycle constraints bound complete clean rectangles,
but do not directly bound those inherited pair sets. A constant-factor
homogenization or an independent-set witness potential would bridge this gap;
neither has been proved here.
