# V3 bounded-degeneracy assessment

The proposed local hypothesis says: there is a constant d such that every nonempty set of assigned witnesses either contains an edge in the raw-exposed set from L_meta_4322 or has a fiber of size at most d in one of the four roles (first endpoint, second endpoint, oriented top, junk gate). Unlike the fixed threshold-two obstruction, this does not prescribe the required density constant.

No counterexample satisfying IsLeastAO was found. A finite Heawood example could at most force d to be at least three; refuting the existential assertion needs an unbounded family.

This is a genuinely stronger structural assertion than a linear bound in total circuit size. A d-regular bipartite high-girth witness set with one top and one junk label per left vertex has all four role fibers of size d, while building the neighbor disjunctions can require order d times the number of vertices gates. Thus a linear global bound alone does not imply bounded degeneracy in the four selected labels. The hypothesis isolates a circuit-elimination problem rather than simply renaming the desired inequality.

A plausible elimination mechanism is repeated endpoint activation: along a nested AND chain accepting the pair {u,v}, descent eventually reaches a raw gate. If another branch accepts the singleton u, and the external top is guarded by u, that top can bypass the repeated branch because u AND (h AND k) equals u AND h whenever u implies k. A least circuit can retain that shared AND only if other readers need it. The unresolved difficulty is showing that arbitrarily dense raw-free witness dependencies cannot all be anchored by essential readers outside the selected witness set. Girth at least five should be relevant to preventing such sharing, but this is an argument to prove, not an established fact.

## Targeted synthesis

I encoded a possible cost-matched Heawood counterexample: a 20-gate AO circuit g, followed by the six-gate OR of all seven point inputs and a final AND. Total size is 27, matching the standard star-circuit upper bound. The desired g agrees with the graph edge function whenever any point input is true, is true on the all-lines/no-points input, and ends in an AND with a nested AND child. Such a candidate would have an empty raw-exposed set at its final top and the whole 21-edge four-rich core. Exact leastness would still need an independent lower bound, even if synthesis succeeded.

The initial SAT test rows included all assignments of size at most two containing a point, plus the all-lines/no-points assignment: 78 rows, 5,640 variables and 129,790 clauses. CaDiCaL was capped at 55 seconds. Three additional 70-second runs fixed the first gate to an OR of line inputs, an OR of point inputs, or an AND of line inputs, respectively. All four runs returned UNKNOWN on their time limits; none returned SAT or UNSAT. No candidate or exclusion proof was obtained.

Complete CNFs, scripts, and solver stdout/stderr are preserved under `/tmp/oec/pequalnp-pilot-48/`, with summary logs `heawood-synthesis.log`, `rightor-synthesis.log`, `leftor-synthesis.log`, and `rightand-synthesis.log`.

Verdict: V3 remains plausible and was not falsified, but it is unproved. The exhaustive nonleast Heawood stress tests show why IsLeastAO must be retained. The targeted synthesis timeouts supply no positive or negative evidence about satisfiability.
