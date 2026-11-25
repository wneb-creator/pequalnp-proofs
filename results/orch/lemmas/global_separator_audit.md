# Junk-component and separator attempt

No rigorous isolation step retaining all hypotheses of L-meta-3760 was found. Three separate requirements fail under the natural operations.

## Induced restriction preserves the graph class but not leastness

The C4-free P4 function F = p0(l0 OR l1) OR p1 l1 has a minimum four-gate circuit: the OR l0 OR l1, its AND with p0, the AND p1 l1, and the final OR. Four inputs are essential, so three gates would force a binary read-once formula. A read-once formula for a connected quadratic graph cannot have an OR at its root, because the graph would disconnect across its disjoint variable sets. An AND root requires both factors to have only singleton minterms, hence would represent a complete bipartite graph. P4 is neither a star nor K2,2, so three gates are impossible.

Set l0 = 0. After constant and identity propagation, the surviving circuit is p0 l1 OR p1 l1, with three gates. Its induced graph is a two-edge star, with a two-gate circuit (p0 OR p1) AND l1. Thus restriction of a globally least circuit need not remain least even after routine simplification. Re-minimizing the restriction may discard the junk gate one intended to retain.

## Junk ancestry components need not be semantic modules

For points p,r and lines q,s, let g = (p OR r) AND (q OR s), h = (p OR s) AND (r OR q), and output g AND h. This seven-gate circuit computes the matching pq OR rs exactly. Each matched edge makes both g and h true. If neither matched edge is present, any way to make g true uses a forbidden crosspair ps or rq, which makes h false.

Both g and h are strong junk: g accepts ps, and h accepts the same-side pair pr. Neither is an ancestor of the other. A junk interaction graph using only junk-to-junk ancestor edges therefore has two separate components, yet the clean output AND couples them. A useful interaction graph must also connect junk gates sharing a clean top or another shared continuation. Such a graph may have no separating component.

Cutting h to an independent boundary variable y gives y(p OR r)(q OR s). Its minimal positive assignments have three variables, so the boundary function is cubic and is not a quadratic graph incidence function. Carrying the interface as independent variables therefore loses the target class required by the one-junk theorem.

## Input-zero restrictions need not isolate one junk at all

In the matching example, retain any subset of the four original variables and set the others to zero. With all four or any three vertices retained, both g and h remain strong junk. With exactly the endpoints of one matched edge retained, both are below the induced target, giving zero junk. Restrictions with exactly one junk have an empty target. Therefore no input-zero restriction retaining a nonempty induced graph isolates exactly one strong junk.

This last claim was checked by all 16 masks and all 16 assignments per mask; complete output is `global_separator_restrictions.json`. It is finite Python validation, not a Lean theorem. The matching circuit is nonminimal, so it does not refute a specially strengthened isolation theorem for globally least counterexamples. It does show that minimum-size assumptions would need a new substantive argument, rather than merely passing through a syntactic separator.

Conclusion: input restrictions preserve C4-freeness but can lose leastness and may never leave one junk; circuit-interface cuts can preserve local replacement costs but lose quadratic incidence semantics. No available operation preserves both properties simultaneously. A multi-junk budget or a new optimal-circuit decomposition theorem is still required.
