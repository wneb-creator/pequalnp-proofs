# Single dirty AND: accounting investigation

2026-11-25 UTC. Constructive, coordinating with lower_bound. No full one-dirty-gate lower bound or normalization theorem has been proved. The observations below separate verified algebra and local geometry from the still-missing global accounting bridge.

## Pair-level decomposition

Before the sole pair-dirty AND d, every AND is pair-clean relative to the target graph G. On assignments of weight at most two, each operand of d therefore has the form

`hit(A) OR E` and `hit(B) OR F`,

where `hit(A)` means that the pair meets the singleton support A, and E,F contain only target edges supplied through earlier clean ANDs. The genuinely new raw component of d is `hit(A) AND hit(B)`. Terms involving E or F are old clean contributions, not new raw births.

At a first clean AND consumer of d, both operands cannot carry d through OR-only paths: then every dirty pair accepted by d would still be accepted by the consumer. Hence at most one operand carries d directly. If S_i is the other operand's singleton support, all new d-derived pairs lie in

`hit(A) AND hit(B) AND hit(S_i)`.

Pair cleanliness makes that entire raw triple filter safe. Union over all consumers is exactly the same filter with `S = union_i S_i`. The checked adjacent-center theorem therefore covers all such new raw edges by one adjacent pair, giving at most five raw edges in Heawood. lower_bound has independently formalized the arbitrary-family union corollary.

This is not a bound on all edges lost by setting d to zero. Old E/F contributions may also be essential to the final output.

## Local credits

If an accepted triple-filter graph contains the two outer edges of a P4 and rejects the outer endpoint pair, one of A,B,S contains both middle vertices. If the middle pair is a target edge, that support contains an actual edge. lower_bound has formalized this propositional observation and the accompanying fact that, in a triangle-free graph, a support containing an edge cannot cross completely into any nonempty opposite support.

Consequently such a mixed support cannot participate in an ordinary clean AND's new edge births. It can still filter previously generated clean edge terms, so it is not automatically an unused circuit node.

There is a second caveat: S is a union of consumer supports. Its two adjacent centers might lie in different S_i. Then no actual OR gate computing their union need exist. A gate credit must come from the distinct consumers or their later recombination, not from inventing a union-support gate.

## Precise refinements of the existing OR budget

The proof of `edge_finset_gate_bound` in `L_meta_1983.lean` uses `F(c,w)=S(w)` only if every vertex in S(w) is adjacent to c; otherwise that F-value is empty. Thus it only needs to charge large OR supports having a common neighbor. Mixed supports containing an edge are excluded in triangle-free G. lower_bound's `GoodOrEdgeBound` implements this refinement.

The same proof can also exclude ORs whose output singleton support equals one child's support. Their F-value copies that child and uses the unary branch of `dag_union_bound`. Only strict support-growth ORs with a common neighbor need be charged. lower_bound is making this a separate `GoodOrGrowthBound` assembly.

The no-growth exclusion is relevant to old clean terms: every clean AND output has empty singleton support. To enter a positive-support operand of d through OR-only paths, it must cross an insertion OR with one empty-support child and one nonempty-support child. This OR does not enlarge singleton support, so it supplies a potential cover-budget credit. The unproved part is importing all old clean covers using these credits without charging an OR twice when it already participates in the ordinary cover DAG.

## An abstract union-DAG observation

Consider a finite live directed acyclic network leading to one output, with b binary union nodes, u unary-copy nodes, and s sources. Every source labels a singleton except one source labeling at most two elements. If the underlying undirected live graph contains a cycle, the output union has size at most b+1.

Proof: the output union has size at most s+1. The edge count is at most 2b+u. The live graph is connected and has a cycle, so its edge count is at least its vertex count s+b+u. Therefore s<=b and the claimed bound follows. This counts distinct sources, so sharing is handled directly.

A shared two-center dirty source which reaches the output through genuinely distinct effective consumers suggests exactly this compensating cycle. If only one consumer is effective, either its raw contribution is one star or its actual support contains both centers. This is a possible route to canceling the extra cover-center cost.

UNPROVED BRIDGE: the actual pair-level cover trace must be converted to such a live union network while preserving old clean contributions, accounting for context-dependent filtering, and assigning each counted node to one original gate. The abstract counting lemma alone does not settle the circuit bound.

## Illustrative pair-level example, with correction

Let `d=(c OR a) AND (d0 OR b)`,
`q1=(d OR r) AND (c OR t)`,
`q2=(d OR s) AND (d0 OR u)`, and output `q1 OR q2`.

This uses ten gates. Its weight-two acceptance graph has edges `c-d0,c-b,a-d0,c-r,r-t,d0-s,s-u`, a seven-edge tree with cover number four. The two consumer cover sets both contain the dirty source's two centers, illustrating overlap at their final union.

This is NOT an exact circuit for that graph function: the independent triple `{a,b,t}` is a false positive. An earlier message called it a tree example without this qualification; the correction was sent immediately to root and lower_bound. It is only a pair-accounting illustration, not a construction or counterexample.

## Constructive route omitted by the factor prototype

The two-supergraph prototype assigned both pure-side false rows to both factors, excluding singleton terms from both factors. Allowing singleton terms is a substantially different family and may give more economical starting circuits.

For any vertex v there is the exact identity

`F_G = (x_v OR F_(G-v)) AND (OR(N(v)) OR F_(G-N[v]))`.

Indeed `F_(G-v)` implies the second factor, and setting x_v=true reduces the target to the neighborhood disjunction together with the remaining induced graph. This gives a cofactor construction at the scale of the 27-gate baseline. It is not a 26-gate construction; no further CPU-heavy search was started.

## Current status

New raw births are now controlled globally, and the OR budget has concrete removable charges. The exact single-dirty gate bound remains open in this work. No claim that the posted existential statement is false follows from these notes.

## Paid frontier for old clean contributions

Further review on 2026-11-25 UTC gives a concrete way to charge the old clean contributions entering the dirty gate, without reproducing their downstream filters. Formalization has taken on this lemma.

Consider the prefix strictly before the sole dirty AND d. Let S(w) be the singleton support and H(w,u,v) the pair-acceptance relation. Every AND in this prefix has empty singleton support. OR supports are unions, OR pair hits descend to at least one parent, and input pair hits meet the input singleton support.

Let I consist of all OR gates i in this prefix such that S(i) is nonempty and one child has empty support. Such a gate has exactly one empty-support child, and its output support equals the other child's support. It is therefore a no-growth OR excluded from the edge budget in `GoodOrGrowthBound`. Let R be the image of I under the function selecting its empty-support child. Then every member of R is earlier than d, has empty support, and |R| <= |I|. Taking all insertion gates avoids a reachability definition and still pays for every selected root.

For any positive-support wire w before d, a pair accepted at w without meeting S(w) is accepted at some j in R. Proof is strong induction on w. An input contradicts the no-hit hypothesis. An AND contradicts positive singleton support. At an OR, choose an accepting child. The pair misses that child's support because it misses the output union. If the child has empty support, the current gate belongs to I and that child belongs to R. Otherwise recurse.

Both dirty operands necessarily have nonempty singleton support: if one had empty support, its pair hits would be unions of earlier clean edge contributions and hence lie in G, making the dirty AND pair-clean. Thus the frontier statement captures every old clean term entering either dirty operand.

Apply the existing cover-certificate DAG argument with the members of R as multiple roots. Their common cover has size at most |R| plus the number of small-support ORs in the prefix. Consequently it has size at most |I| plus that number of small-support ORs. Sharing and duplicated boundary children are counted once. This pays for the extra cover roots with the insertion ORs themselves, rather than charging the potentially many downstream merges of inherited clean terms.

This is a precise local accounting improvement, not yet the combined one-dirty lower bound. A final proof must integrate these paid roots with the dirty source's adjacent two-center contribution and the ordinary final-output cover trace. In particular, merely adding all old clean edges to every H relation is invalid: it violates the input hit condition, and adding them only at selected wires can violate the OR or chosen-AND predecessor rule. Explicit paid roots preserve the original DAG order and expose the remaining extra-center accounting obligation.

Accounting correction: I can include insertion ORs whose support has cardinality one. Those gates also belong to the small-support OR set, so the preceding raw sum can charge one gate twice. Formalization identified this overlap independently. The proposed repair is to modify the cover certificate at every insertion OR to copy its nonempty child's certificate, while its empty child is an explicit member of the root set R. The binary union nodes are then only the small-support ORs outside I. Correctness is a statement about the union of all root certificates, not each local certificate separately: whenever a pair hit descends into the omitted empty child, its earlier explicit root accounts for it. Strong induction supplies this global correctness. The resulting proposed bound is |R| + |small ORs minus I| <= |I union small ORs|. This repair has been sent to formalization; it is not yet recorded as a checked theorem here.

There is also a useful scope reduction. If either operand of the dirty AND has singleton support of cardinality at most one, the hypothesis `handS` of the original `cover_half` already holds at that gate. Pair cleanliness is not needed for the AND pair-predecessor rule. Thus that entire cover half applies unchanged in this case. Its exceptional case is specifically a dirty AND whose two operand supports both have cardinality at least two.

## Proposed global cover bridge: explicit trace argument

The following is a mathematical proof plan, not yet a Lean theorem. It sharpens the remaining combinatorial obligation rather than asserting the final gate bound.

Let D(w) mean that w carries the dirty gate through OR gates only: D(d) is true, an OR takes the disjunction of its parents' D flags, and every other AND/input has false D. A fixed false pair accepted by d is accepted at every D wire. Thus a clean AND cannot have D=true on both parents. An empty-support wire with D=false is pair-clean, since its OR-only ancestry consists of clean AND outputs and the false constant.

Use insertion ORs whose empty child has D=false; make those clean empty children explicit global roots R. At such an insertion the modified cover certificate copies its nonempty child, so its gate is charged only as a root. At each clean AND choose a small-support parent; if exactly one parent has D=true and the other parent also has small support, prefer the D=false parent. Other small-support ORs take unions. Inputs carry their singleton labels. The difficult dirty node receives the two-center label for its safe raw contribution. If its own singleton support has size greater than one, it is never visited by this small-support certificate trace and no exceptional label is needed.

For a target edge accepted at a clean empty root and absent from every root certificate, trace accepting predecessors backward along the certificate. At an omitted insertion child, jump to that earlier explicit root. Reaching an input contradicts the missing certificate hit. If the trace reaches d, inspect its operands. If the pair misses one operand's singleton support, the frontier argument produces an earlier clean boundary root accepting the pair. Otherwise the pair hits both raw operand supports.

In this latter case, inspect the first clean AND consumer of d along the selected trace. Its opposite operand cannot have D=true. Because the selected parent carries d and has small support, the preference rule implies that the opposite operand has large support. If the pair meets that opposite support, it lies in the safe raw triple filter and is covered by the dirty center label. If it does not meet that support, the frontier argument for a D=false OR cone again gives a clean boundary root accepting the pair. This root is earlier than the consumer, hence earlier than the current root. All root jumps decrease the wire index, giving a well-founded contradiction. This explains how post-dirty clean contributions can be accounted for too, without falsely treating them as pre-dirty terms.

The initial cardinal bound from this construction is one vertex too loose when the dirty label uses two centers. There are two proposed exact credits:

* If an actual operand or effective filter support contains both adjacent centers, the first OR in its singleton-support ancestry to acquire an edge is a strict-growth OR with no common-neighbor owner. It is neither a paid growth OR nor an insertion/root OR nor a small-support union OR, so it pays the extra center.
* Otherwise the virtual mixed union must use two effective first consumers, one for each center-star. A single effective consumer with no mixed support needs only one center label. Two distinct effective consumers force a fork in the live certificate DAG, which saves one source in the union cardinality count.

Here is the exact abstract fork count. In a finite live unary/binary union DAG with r designated roots, s sources and b binary nodes, each non-root has at least one outgoing edge, while the total edge count is at most u+2b. A non-root with two outgoing edges, or a designated root used by another live node, supplies one additional outgoing edge. Hence u+2b >= s+u+b-r+1, so s <= b+r-1. If one source labels two vertices and all other sources label at most one, the union size is at most s+1 <= b+r. This cancels the exceptional center. Parallel identical predecessors can be treated as unary nodes.

The outstanding formal obligations are to construct the modified certificate DAG, extract its effective first consumers, and connect the local owner/mixed-support lemmas to the two cardinality cases. The source-count identity itself is elementary, but it must not be substituted for these circuit-to-certificate obligations. The edge-budget bridge also remains a separate component.

A later simplification avoids classifying the two star orientations. Let J be the live clean ANDs whose selected predecessor has D=true. Every member of J has a selected OR-only path to d. If J has at least two members, these two paths force a shared child with distinct parents: neither clean-AND start can lie in the other's OR-only interior. The checked `TwoPathFork` helper now gives exactly this fork, and the checked `LiveDagSupportBound` helper cancels the extra center. If J has exactly one member, its relevant graph is one actual triple filter. Either that graph is a star and needs only one label vertex, or the P4/mixed-support lemma gives an actual mixed support A, B, or S_j and hence the unused ownerless strict-growth OR. If J is empty, d cannot be live, since every designated root has D=false. These cases leave only the selected-graph construction and escape correctness to connect; the helper lemmas do not themselves establish that connection.

For the accepting-path escape proof, an arbitrary D=false to D=true transition suffices; a last-transition condition is unnecessary. Once the pair hits both raw supports at d, every D=true wire accepts that raw pair by its OR-only connection to d, independently of the accepting path's later choices. At any selected clean consumer on the accepting path, its opposite operand accepts the pair by AND semantics. Hitting its singleton support gives the safe raw filter; missing that support gives the clean-frontier escape. This refinement was sent to formalization after reviewing the prepared selected-path interface.
