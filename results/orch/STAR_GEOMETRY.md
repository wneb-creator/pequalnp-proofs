# L-meta-2448: graph geometry route

The graph-combinatorial part needs only triangle-freeness: any nonempty family of graph edges whose pairs intersect has a common endpoint. The standalone proof compiled successfully after cache restoration.

For an arbitrary computing circuit, star ownership is false. On the two-edge matching with vertices a,b,c,d, the circuit

`((a OR c) AND (b OR d)) AND ((a OR d) AND (b OR c))`

computes `(a AND b) OR (c AND d)`. Its first AND owns the disjoint edges ab and cd. It has seven gates, whereas the canonical circuit has three. Therefore least-size selection or an exchange argument is essential.

Accepted reduction `lean/PEqualNP/Outside/R_meta_2448_263.lean` has the stronger local fact needed for normalization: if one monotone two-input AND gate owns two disjoint pairs, in a C4-free graph it fires on some nonedge pair (possibly a singleton) among their four endpoints. The proof is its local `pairDirt` fact. It proceeds by extracting OR-only reachability from each endpoint to the gate's two inputs; a clean four-endpoint truth table would otherwise create a C4. The reduction assumes separate size-preserving repairs for singleton and distinct-nonedge false positives and minimizes the number of gates owning disjoint edges.

The root assigned formalizing the common-center lemma and a clean-gate-to-star wrapper to this agent. The global size-preserving repair remains with the normalization strategy.

## Checked components

`lemmas/StarGeometry.lean` now has 453 lines and uses only `import PEqualNP.Defs`. It compiled with pinned Lean 4.36.0, exit code 0, via direct `lake env lean`. Logs: `/tmp/oec/pequalnp-pilot-74/star-geometry-combined-002.stdout` and `.stderr`. One unused-simp warning remains; there are no errors.

Declarations under `PEqualNP.Outside.L_meta_2448`:

- `common_center_of_pairwise_meeting`: the graph-only common-center lemma, independently written here.
- `owned_disjoint_edges_have_false_positive`: the 340-line local `pairDirt` fact adapted from accepted `R_meta_2448_263.lean`, with no outside-file dependency.
- `hasStarProfile_of_pairwise_meeting`: packages common centers for the circuit profile definition.
- `hasStarProfile_of_pair_sound`: a monotone circuit has star profile if every AND gate is true only on adjacent pairs, assuming the graph has no triangle or C4.

This is a partial component, not a proof of L-meta-2448. The unproved step is finding an optimal circuit whose relevant gates satisfy such cleanliness, or another property ensuring pairwise-intersecting ownership.

## Alternate AND-count route

Requested alternate target: prove that a monotone circuit computing a triangle/C4-free graph function uses at least its minimum vertex-cover size in AND gates; combine with an OR lower bound and an explicit star-cover circuit.

Existing checked evidence is limited. `L_meta_217.lean` proves the root-circuit AND lower bound for an arbitrary C4-free graph only when the cover lower bound is at most five. `L_meta_2399.lean` proves a related exact-fan-in-two formulation. Both proofs are around 7,400 lines and use finite host classification via the OR-free model in `Defs/AndCountCircuit.lean`. This is not an immediate available general theorem.

A tempting counterexample, `L_meta_1006.lean`, is NOT a counterexample for exact graph computation. Its six-AND circuit is specified only on maximal-independent-set boundaries. Direct local evaluation shows it misses graph edges (4,10), (5,9), (6,7), (6,10), (7,9), (8,9). The graph also contains triangles. Therefore that file neither refutes nor establishes the proposed exact triangle-free AND bound.

The main obstacle recurs in counting: an AND gate can create a rectangle of positive pairs containing nonedges, then later AND gates filter those pairs. Assigning a star center to each generating gate is invalid, and counting rectangle decompositions separately duplicates shared subcircuits. A circuit for the two-edge matching obtained by intersecting two C4 functions illustrates this phenomenon, although its three AND gates are worse than the two-AND star circuit.

The counterexample agent is probing the exact OR-free model on the 11-cycle with five AND gates and Petersen with five AND gates. Edge-pair positive tests plus maximal-independent-set negative tests suffice for exactness under monotonicity.

## Pivotal-edge structural route

`lemmas/PivotalNecessary.lean` compiled successfully on its first build, exit 0, no warnings. Full validation is in `lemmas/PivotalNecessary.validation.txt`.

New checked facts:

- `eraseZero_fun`: a forced-false gate can be deleted without changing function, remapping its old wire to an index beyond the whole circuit and shifting later wire indices. This holds without a backward-reading hypothesis and handles forward and missing wires correctly.
- `eraseZero_mono`: deletion preserves `Monotone2`.
- `eraseZero_size`: deletion saves exactly one gate.
- `every_gate_has_pivotal_edge`: every gate of a minimum exact graph circuit is pivotal on at least one edge pair under false substitution. This includes OR gates, needs no triangle/C4 hypotheses, and follows from sandwich preservation plus the deletion.

The full bridge remains unresolved: a first bad AND may have inherited pivotal edges that are not owned by it, and downstream gates may filter false positives on crossed pairs. The matching negative control shows that earliest-bad plus correctness alone does not force a pivotal star; the optimal C5 control shows that even a good gate can have a nonstar pivotal set because it carries an earlier edge.

`lemmas/PivotalUnique.lean` adds a checked repair beyond the earlier operand restriction: if a gate has exactly one pivotal graph edge {u,v}, replace it directly by AND(input u,input v). Monotonicity of the original gate makes this replacement pointwise downward, because the gate was true at the edge pair. Nonpivotal edges survive above false-substitution; the unique pivotal edge survives explicitly. Size and Monotone2 are preserved, and the new gate owns a star. No ReadsBack, girth, gate-operation, or operand-singleton implication is needed. Compilation exit 0, no warnings; complete validation in the adjacent `.validation.txt`.

Combining unique-pivot repair with necessary pivotality narrows a maximal-good-prefix obstruction to at least two distinct pivotal graph edges, once preservation of earlier cones/values is assembled. It does not settle multiple pivotal edges, nor does it identify pivotal edges with owned edges.

## Arbitrary-reader four-vertex repair

`lemmas/FourVertexGeometry.lean` compiled with exit 0 and no warnings; full logs are `four-vertex-003.stdout` and `.stderr` in the job scratch directory. The checked core is preserved separately as `FourVertexGeometryCore.lean`.

For two disjoint graph edges ab and cd in a triangle/C4-free graph, at most one of ad, bc, ac, bd is also present. The file chooses two clean stars covering all induced graph edges, with each star computable using input literals and the existing raw disjunctions b OR d and b OR c. Its `repair_choice` proves both global cleanliness and coverage of every graph pair on which either crossed rectangle `(a OR c) AND (b OR d)` or `(a OR d) AND (b OR c)` is true. This is the geometric input to the other agent's `ExternalRepair` transformation, which supports arbitrary unchanged outside readers and rescues affected pairs through an OR path from the replacement output.

## Remaining global component issue

The general obstruction is a shared OR support. If such support contains an edge ad and feeds a globally clean AND, its other operand can have no bare input in its OR frontier: otherwise that input v creates both graph edges av and dv, contradicting triangle-freeness. In a minimum circuit, the other operand cannot be globally below the target graph function, so its AND frontier must contain another dirty gate. This suggests closing a whole dirty component transitively through shared supports. It does not yet prove a gate budget for repairing the component.

A clean context `(OR P AND OR Q) AND OR R` with disjoint P,Q and p in P intersect R, q in Q intersect R forces p adjacent to every vertex of Q and q adjacent to every vertex of P. A four-cycle then shows every graph edge across P and Q contains p or q, giving two clean stars that preserve every positive pair of the first rectangle. The extra OR gate needed to join the stars must still be funded by deleting or reusing context support circuitry, and shared readers/scheduling must be handled. The formal version `DoubleStarGeometry.lean` subsequently compiled with exit 0 and no warnings after cache restoration; complete validation is in the adjacent `.validation.txt`.

## Precise unresolved component budget

A promising objective is to choose a circuit lexicographically minimizing total size and then AND count. The checked three-AND matching/P4 exchange preserves size and decreases AND count. It therefore requires no preservation of earlier ownership.

Critical-structure analysis strengthens the support-sharing closure: a globally clean AND reading an OR support containing a graph edge has a singleton-silent opposite operand. It consequently owns no graph edge. Minimum-size AND bypass then implies that its opposite OR frontier contains another globally dirty AND. Closing through shared edge-containing supports therefore adds empty-owning AND gates, which may fund replacement OR joins. This is structural progress, not yet a complete budget argument.

For a pure conjunction of OR clauses, an independent clause support S that covers every pivotal edge and is shared with an outside clean star center v has a stronger limitation. Every vertex outside S has at most one pivotal neighbor in S, since two would form a four-cycle with v. Thus the pivotal graph is a disjoint star forest centered in S. This provides a possible boundary split: edge-containing support forces closure, while independent shared clause support forces a star-forest pivotal graph. General components also contain ORs of dirty AND signals, so treating every support as a clause would be unjustified.

A global replacement can avoid preserving individual outside readers: force the chosen component false, remove dead gates and propagate zero values, and let H be the graph edges then lost. The residual is pointwise below the original graph function and still accepts every edge outside H. Appending a star-cover circuit for H and an OR with the residual computes the original graph function by monotonicity. The required fresh-gate budget is |E(H)| + tau(H), or one less if the residual is identically false. Gates freed by zero propagation, especially an OR becoming a copy, must be included in the budget. In the shared-support matching example, deleting the three-AND block alone is short by one for this reconstruction, but collapsing its outer OR supplies that fourth gate.

The unresolved assertion is that some nonempty dirty component admits this reconstruction budget, or an equally strong local exchange, with a strict AND-count improvement whenever size ties. We have not proved it. In particular, neither the existence of one private support OR nor empty-owning readers alone gives the required bound for an arbitrary component. No unconditional lower bound |E| + tau - 1 has been established here.

## Pure-CNF clause count (mathematical argument, not formalized)

For a triangle/C4-free graph H with minimum vertex cover C of size tau and I its complementary maximum independent set, the neighborhoods N_I(c), for c in C, are nonempty and pairwise distinct. Nonemptiness follows from minimality of C. Equal neighborhoods with two vertices create a C4. Equal singleton neighborhoods {u} would allow replacing c,d in the cover by u: triangle-freeness excludes the edge cd, and all edges from c,d to I meet u, contradicting minimum cardinality.

For each c, extend the independent set (I minus N_I(c)) union {c} to a maximal independent set J_c. If J_c = J_d, independence gives N_I(c) subset N_I(d) and the reverse, contradicting distinctness. These tau different maximal independent sets all differ from I, so H has at least tau+1 maximal independent sets. An irredundant exact CNF therefore has at least tau+1 clauses. This supports a possible private-clause-root budget but does not establish the total circuit inequality.

The counterexample agent checked the proposed external-center support family at its simplest bases. A support reusable by a new clean star must be a distance-two packing, and distinct supports may overlap in at most one vertex. C6 has only three allowed pairs, C7 seven, and Petersen none (every pair is adjacent or has a common neighbor). Canonical shared CNFs have core sizes 14 for C6 versus star size 8, and 20 for C7 versus star size 10; the respective sharing gains 3 and 7 do not cover those excesses. No counterexample was obtained. These are finite construction checks, not an impossibility result for all such constructions.

The full clean-star reconstruction and the bound |E|+tau-1 may be stronger than the posted ownership-only normal form. Inherited graph edges can pass through nested clean AND gates while ownership remains a star. Therefore failure to prove the stronger budget is not a refutation of the target, and a general ownership-preserving rotation could still be cheaper than rebuilding all stars.
