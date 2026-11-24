# Disjoint two-product census including singleton operands

This extends the independently reviewed JointUnion diagnostic by allowing singleton clauses while retaining nonempty, disjoint operands within each product. Both products must be dirty, their conjunction must be globally below the host graph function on all256assignments, and they must jointly accept at least one host edge. Effective variable masks are also checked on every assignment.

The tested union U contains all host edges accepted by any effective variable mask or by the joint. The budget is |U|≤K+2, where K=sum(|clause|-1)-sum(max(|cross intersection|-1,0)) is the explicit shared-quadrant OR construction. Singleton clauses have zero OR cost. This package does not test the stronger K+1 criterion.

All3025 distinct disjoint nonempty product forms on8variables are enumerated. Clean forms are removed separately for each of five explicit bipartite C4-free hosts. Every unordered pair of remaining dirty forms was checked; the complete counts are in JSON/log. No counterexample and no timeout occurred. This is bounded computational evidence only, not a general theorem or a proof of the posted gap.

Reproduce: `python3 SearchSingletonJoint.py --vertices 8 --disjoint --edge-budget --seconds 60 --output result.json`. Source/results were independently reviewed by counterexample_search; complete stdout/stderr is preserved.
