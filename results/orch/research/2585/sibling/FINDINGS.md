# L-meta-2585 sibling and public PR audit

Audited 2026-11-25 after the 00:23 UTC assignment. No desk calls or final-file edits.

## Meaning of read-1

ReadK.IsReadK n C 1 requires each prime implicant to have a successful proof tree in which every input variable occurs at most once. It is not global read-once syntax. Incidence edges are prime implicants, so endpoint count vectors are the relevant invariant.

## Known cost of read-1 circuits

L_meta_4897 (1961 lines) proves for C4-free bipartite E and a read-1 AO2 circuit C that a vertex cover A,B exists with |E|+|A|+|B| <= C.size+1. L_meta_2237 is the corresponding general graph result. This gives minimum cost |E|+tau(E)-1 for nonempty E, provided the star construction is used for the upper bound. Empty E has cost zero through an invalid output wire.

L_meta_3692 (714 lines, Defs-only imports) and L_meta_2874 (738 lines) construct a star-cover AO2 circuit with cost <= |E|+|A|+|B|-1. Their additional invariant partitions pure OR-cone wires by the point/line side; every AND reads one from each side.

L_meta_3760 (10039 lines) excludes exactly one dirty AND gate in a least AO2 circuit for a C4-free bipartite graph. Multiple dirty gates are the unresolved regime; this does not prove the requested normalization.

## Duplicate exact target and reusable public proof

The conclusion of public PRs #9697 and #9707 for L-meta-4895 is the same statement as L-meta-2585, up to names of bound variables. Both were open in the fully paginated census and were fetched directly by immutable head SHA.

- https://github.com/open-goat/pequalnp-proofs/pull/9707 : head c19bca0988052aad6ddf9527332f310ae3770d8b (LDSS-Nauvoo). source-9707.lean is a 32-line reduction into the unrestricted cover budget and a read-1 star constructor. Repeating this exact two-premise cut would add no mathematical progress.
- https://github.com/open-goat/pequalnp-proofs/pull/9697 : head 9a7b2ba1647d0d43e87d2ff4017b977e6fd7e044 (Amritpal-Nijjar). source-9697.lean is 329 lines. It proves the matching-to-cover conversion by Hall and proves the read-1 bridge from the partitioned OR-cone construction. The bridge occupies roughly lines 109-318: use a unit count-vector for a true pure-side wire; opposite-side ANDs add disjoint unit vectors; OR preserves a successful child. It reduces the target to the unrestricted matching lower bound plus the already checked L3692 star constructor.
- https://github.com/open-goat/pequalnp-proofs/pull/9933 : source-9933.lean is just a 20-line statement of L2976 with sorry; unusable.

R_meta_2976_418 in the checked repository already uses our entire normalization statement, L4897-style charging, and L3692-style construction to derive separated point/line OR-cone normalization.

## Normalization and failed accounting routes

L_meta_4295 (563 lines) proves termination of CircuitMoves.Lift: in the resulting circuit any OR gate reading a gate below output has both inputs below output. Helpers/NormalFormLift.lean and Helpers/LiftFixMain.lean contain an AO2-preserving implementation and size-preserving OR-lift iteration. These helpers are outside the allowed Defs import closure, so proofs must be adapted rather than imported.

The stronger normalize predicate in structural/ReductionDraft.lean additionally excludes AND readers of below-output wires. This is plausible by F = w OR F[w:=false] for w <= F, using removed downstream AND/OR gates to pay for the final OR. It is stronger than the exact result of L4295.

Beware L_meta_3444 and L_meta_3446: their checked counterexamples refute naive additive core accounting even with all gates in the output cone and LiftFixedPoint. L_meta_2969 gives the simpler unread-core counterexample. The structural agent has avoided such per-cone additive hypotheses.

## Search records

- broad-related-files.txt: 292 local Outside candidates.
- theorem-index.txt: extracted relevant theorem statements.
- related-open-prs.json: filtered entries from the complete initial 2135-PR census.
- pr2585.json: current targeted GitHub all-state search returned an empty list.
- pr-9697.json/pr-9707.json/pr-9933.json and source-*.json/.lean preserve structured metadata and fetched source.

## Forest gate-count split (2026-11-25; NOT Lean checked)

**Status:** closed informal argument only. No unrestricted C4-free incidence theorem or refutation is claimed. The formal constant-propagation compiler is owned by the certificate agent in `direct/ForestElim.lean`; no duplicate compiler is being built here.

Let G be a finite simple forest, possibly disconnected or with isolated vertices. Let C be a valid monotone circuit whose gates have exactly two inputs and whose output computes f_G(z)=OR_{uv in E(G)}(z_u AND z_v) on every Boolean input. Count OR and AND gates separately, including unused gates. The intended conclusions are

- OR(C) >= max(|E(G)|-1,0).
- AND(C) >= tau(G), where tau is minimum vertex-cover cardinality.

Constant propagation retains a gate with its original opcode or deletes it; it never introduces the opposite opcode. For a nonconstant residual graph function the output is a retained wire. If the residual graph is edgeless, no induction step is needed; in the repository representation the false constant may also be represented by an empty circuit with an out-of-range output, since `IsAO2` does not require output validity.

### Generic one-gate losses

If input y is essential, there is a syntactic path from y to the output. This follows contrapositively by induction along the circuit: a wire with no dependency path from y computes a y-independent function.

1. Suppose f restricted to y=0 is not identically false. Since f is monotone, the assignment y=0 and all other variables=1 is accepted. Consequently no y-to-output path is made entirely of AND gates: such a path would force output false on that assignment. Pick any path and its first OR. Its prefix contains only AND gates, so propagating y=0 makes the selected predecessor of this OR constant false. The OR is deleted, whether its other predecessor is false, true or a surviving wire. The resulting circuit therefore has at least one fewer OR, and no more ANDs.

2. Suppose the singleton assignment {y} is rejected. No y-to-output path is made entirely of OR gates, since such a path would force acceptance of {y}. Pick any path and its first AND. Its prefix contains only OR gates, so propagating y=1 makes its selected predecessor constant true. This AND is deleted, regardless of the other predecessor. The resulting circuit has at least one fewer AND, and no more ORs.

Repeated fanout does not affect either argument: only one path and the first gate of the indicated opcode are used. No claim that different paths or cones are disjoint is required. The repository's `ReadsBack` and exact-two-input clauses provide the finite acyclic path model. Correctness ensures the output cannot be an invalid wire when the graph has an edge.

### OR induction

If |E| is0 or1, the asserted lower bound is0 and is immediate. Otherwise pick a leaf y with its unique neighbor x in a component containing an edge. The variable y is essential: the assignments {x} and {x,y} have outputs0 and1. Setting y=0 deletes exactly the one edge xy. Since at least one other edge remains, the restricted function is nonzero. Generic loss1 removes an OR. The residual graph is a forest with |E|-1 edges, so induction gives at least |E|-2 ORs in the residual circuit and hence |E|-1 in C. Isolated vertices and isolated-edge components cause no exception.

### AND induction

If |E|=0, then tau(G)=0 and the claim is immediate. Otherwise choose a pendant edge xy with y the leaf. Essentiality holds as above; the singleton {y} is rejected because the graph is simple and has only quadratic edge terms. Generic loss2 removes an AND under y=1. Now additionally set x=0. Because y is incident only to x, the resulting function is exactly f_{G-{x,y}}; the second restriction cannot add AND gates.

For any graph with a pendant edge, not just a forest,

    tau(G) = 1 + tau(G-{x,y}).

Adding x to a cover of the residual graph covers every deleted edge. Conversely, any minimum cover can be chosen to contain x and omit y: if it contains y but not x, replace y by x; if it contains both, delete y. Removing x then covers the residual graph. The residual graph is a smaller forest, so induction plus the deleted AND proves AND(C)>=tau(G). There is no requirement that x have degree2 or that y have a sibling leaf.

For nonempty G, adding the two bounds gives C.size >= |E|+tau(G)-1. For empty G, use the trivial C.size>=0 directly. This completes only the forest case informally; cyclic C4-free graphs remain unresolved.
