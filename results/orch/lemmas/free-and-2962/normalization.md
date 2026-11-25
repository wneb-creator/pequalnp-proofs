# Mathematical normalizations under investigation

These are informal transformations, not kernel-checked Lean theorems. They apply to free-AND bounded-OR auxiliary models and need not preserve total AO 2 gate count.

## Free-AND generator normal form

Process an AO 2 circuit in topological order. Represent each wire by a conjunction of raw inputs and OR-generator outputs. An AND gate unions the two factor sets, with duplicates removed. An OR gate becomes a generator with its two wire conjunctions as operands. The final output is one conjunction. This gives one generator per original OR gate. Conversely every such generator program expands to a valid AO 2 circuit.

## Disjoint operands

For a generator with conjunction operands A and B, let C be their common factor set. Distributivity gives

    AND(A) OR AND(B) = AND(C) AND (AND(A\C) OR AND(B\C)).

If both residual sets are nonempty, replace that generator by the OR of those residual conjunctions, and replace each future occurrence of its original output by the new generator together with every factor in C. This preserves topological order because all factors of C preceded the generator. If one residual set is empty, absorption makes the original generator simply AND(C); remove the generator and expand its future occurrences to C. Here C is nonempty because the original operands were nonempty. Processing in order obtains disjoint nonempty operands for every useful generator. Unused generators on two distinct raw inputs can pad the budget to the desired fixed number when n is at least 2. Once the ports are disjoint, swapping them allows the harmless convention min(left)<min(right).

The final conjunction of a cycle or theta exact graph function cannot contain a raw input factor, because no vertex lies in all graph edges. This remains true after factoring, since the computed function is unchanged. For partial-edge cases the encoder explicitly checks that the intersection of all required edges is empty.

## Exact versus partial OR lower bounds

Suppose a monotone function h is below the graph edge function fG and accepts all edge pairs in D. OR h with every edge monomial missing from D. The result is exactly fG: each assignment containing an edge from D was already accepted by monotonicity; each other edge is explicitly supplied; no nonedge assignment is added. This costs |E(G)\D| additional OR gates and unrestricted AND gates. Consequently the conjectural exact lower bound ORcount(fG)>=|E(G)|-1 implies the partial bound ORcount(h)>=|D|-1.

## From exact single-output bounds to the two core charges

Let M be the nonempty family of maximal cores and U its union of gate cones. OR their outputs together, using |M|-1 new OR gates. The resulting function is below fG and accepts exactly the edge pairs in D, the union of their gammaE sets. Combining the previous completion construction with the conjectural exact OR lower bound yields |D|<=OR(U)+|M|. Empty M is immediate.

For the cover charge, use a minimum vertex cover ofG\D to compute its edge function as an OR of stars, with at most one AND per cover vertex and otherwise free OR gates. OR this with the function from the core outputs. The result is exactly fG. Thus the conjectural exact lower bound ANDcount(fG)>=tau(G) yields tau(G)<=AND(U)+tau(G\D).

Neither general exact lower bound is established here. In particular, no normalization to a bilinear or read-once circuit has been justified. High-degree intermediate terms and upper AND filters prevent that shortcut.

## Conditional liveness and alternative ordering symmetries

The theta model with six OR generators returned UNSAT. Conditional on that finite solver result and the reviewed disjoint-port normalization, every seven-generator witness may be required to have all generators live: otherwise delete dead generators, renumber, and pad the remaining at-most-six program with unused disjoint generators to contradict the six-generator result. This is a computational completeness justification, not a Lean theorem.

One complete ordering symmetry is nondecreasing maximum predecessor index. Choose a ready gate with the smallest such maximum; any newly ready gate has the just-numbered predecessor, larger than all old predecessor labels. This greedy topological ordering establishes the convention. Orienting disjoint ports afterward does not change their union or maximum.

An alternative symmetry fixes the first generator's two selector vectors to the lexicographically greatest pair under theta graph automorphisms and port swap, preferring true at the first differing coordinate. Relabeling raw inputs preserves the original topological generator sequence and liveness; later ports may be reoriented independently. This alternative MUST NOT simply be combined with maximum-predecessor ordering: input relabeling may change which gate that ordering places first. The two search variants use these symmetries separately.
