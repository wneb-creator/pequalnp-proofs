# Alternative local cores

This computational census visits every4..8-point subset of the posted21-point projective plane. It groups subsets by the histogram of intersections with all21 lines. It records one representative per histogram; it does not claim that each histogram is one isomorphism class. There are35 histogram classes across these five subset sizes.

Identical nonempty line neighborhoods in a selected point set are combined by an OR. The plane has no repeated line neighborhood of size at least2, so only private singleton columns merge. Each merge costs one fewer gate than its number of original lines. A core circuit of size6k−2−outside_or_cost, followed by these aggregate-input ORs and the21−k remaining full stars, would use124 gates. This is a conditional construction, not a found counterexample.

The prioritized six-point set is[0,1,2,3,8,15]. Its core has19 inputs and24 edges, four triple columns, three pair columns, and six private aggregate columns, each combining two original line bits. Standard core size is29; target28 plus6 aggregate gates plus90 remaining-star gates would give124. Exact input order, groups, and edges are in alternative6-core.json.

The seven-point Baer/Fano subset[0,1,2,3,8,15,16] has21 core inputs,28 core edges, and7 aggregate-input OR gates. Its core target is33 versus standard34. No private-leaf complexity theorem is assumed.

The census was rerun from its saved source and exactly reproduced the initial JSON. Numerical results are computational diagnostics; the separate Lean geometry/lift files provide checked conditional certificates.
