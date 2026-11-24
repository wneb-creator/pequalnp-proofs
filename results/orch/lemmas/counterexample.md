# Skeptical strategy: L-meta-5349

No counterexample to the actual statement found. The existential absolute constant makes a single finite circuit with a bad constant insufficient; a refutation needs an unbounded family (or a structural inconsistency).

## Existing checked routes

- `lean/PEqualNP/Outside/L_meta_3805.lean` proves the unfiltered Ustar witness cardinality bound with constant 54 when the junk AND gates form an antichain for InCone. Its `main_bound` begins at line 1194. It therefore covers a substantial special case of the current step.
- The same file's `at_most_two_centers` (line 571) is the key elementary geometry: in a C4-free graph, for a fixed set S, at most two vertices c have at least three neighbors in S while S is covered by N(c) union N(p) for some p.
- `edge_bound_bucketA` (line 633) charges OR-support boundary edges to gates, giving 8 times circuit size. This portion does not need junk antichain or leastness, only AO2 and NoFourCycle.
- `edge_bound_bucketB` (line 812) uses a dirty nonedge pair for each junk gate and singleton/intersection exceptions. Its antichain assumption is used via `junk_gateVal_iff`, reducing junk gates to products of their two OR-input supports.
- `lean/PEqualNP/Outside/L_meta_4005.lean` says an active junk gate implies some active junk gate whose two sides both hit the given input. It does not preserve OrReaches from the original top: descent through an AND blocks that relation.

## Small-case check and warning

The ordinary Python check recorded in `counterexample-small-check.txt` evaluates a 5-input, 6-gate circuit on every input. Let the graph have edges x-c and x-y, let g=(x OR a) AND (x OR b) AND (c OR y), and output x AND g. This is in top form and computes the graph edge function, but g is dirty only on inputs with at least three true vertices. Its accepted pairs are only graph edges. The circuit is not least: x AND (c OR y) uses two gates.

Thus an attractive structural hypothesis, every junk gate has an accepted nonedge pair, is false if minimality is omitted. This example also explains why the antichain proof does not extend directly to nested junk. If pursuing a reduction through bounded dirty certificates, IsLeastAO must remain, and the certificate assertion needs independent proof or stronger empirical evidence.

## Reduction direction worth investigating

A substantive two-piece cut would separate (1) local normalization or bounded dirty certificates for nested junk gates in a least circuit from (2) a gate charging result using those certificates. Avoid merely assuming an injective map from witnesses to a bounded number of gate slots: that is nearly the target cardinality bound reformulated. Likewise a bound on the sum of all OR-support sizes is unsafe because shared OR gates permit large repeated supports.

No reduction file has been proposed yet: the plausible local certificate hypothesis is not sufficiently established.

## Heawood stress tests

Nonempty four-rich witness sets cannot occur on very small graphs. Their oriented edge relation has every nonempty source and target fiber at least three. If one vertex is used in both roles, its degree in the witness graph is at least six, and the girth-five depth-two tree count gives at least 19 supported vertices. Otherwise the witness graph is bipartite of minimum degree at least three and girth at least six, requiring at least 14 vertices. Thus Heawood is a first meaningful test case.

`heawood-stress-check.txt` records an exhaustive 16384-input test on the 14-vertex/21-edge Heawood graph. With one gadget g_p=(p OR q_p) AND OR(N(p)) and top p AND g_p per point, plus a final OR, the 41-gate circuit satisfies AO2, TopForm, the exact edge function, all 21 Ustar assignments, all four fiber-size-three conditions, and opposite-side disjointness. Only leastness fails: an ordinary star circuit has 27 gates.

`heawood-nested-check.txt` strengthens this to raw-free nested junk. Put h_p=(p OR q_p) AND (p OR r_p), then g_p=h_p AND OR(N(p)), top p AND g_p. The 55-gate circuit still meets all the same hypotheses except leastness, but the entire raw-exposed set of L_meta_4322 is empty (checked over all possible tops, orientations and reachable junk). This stress test cautions against proving an empty core solely from graph geometry and OR support semantics.

## Proposed reduction review

The parent's proposal uses the checked support bound L_meta_2074, the checked raw-exposed bound L_meta_4322, and an unproved local obstruction saying every nonempty four-rich core contains a raw-exposed edge. Peeling after deleting the exposed set then yields constant 37. This is structurally meaningful, and two hypotheses already have checked proofs.

However, the local obstruction is stronger than the original linear bound: that bound could hold despite a small nonempty raw-free four-rich core. No actual least-circuit counterexample was found, but the Heawood experiments do not validate leastness. A weaker alternative is existential bounded degeneracy: there is d such that each nonempty raw-free witness subset has a role fiber of size at most d. Peeling gives d times the total available role labels plus the exposed charge. This avoids choosing the unverified threshold two while keeping the remaining task local to nested raw-free incidence.
