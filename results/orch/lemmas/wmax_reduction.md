# Semantic wmax route

- Every selected center u belongs to wmax G C g. The semantic proof is the checked helper L_meta_3805.top_wmax (lines 520–533), also available in the raw-exposed proof L_meta_4322. It uses only AO validity and the top/OR-reach witness, not leastness or TopForm.
- Consequently g is false on singleton u. With monotonicity, if g is true on singleton v, every w in wmax G C g is adjacent to v. Thus the singleton support of g and wmax G C g span a biclique. Under no four-cycles, one of the two sets has cardinal at most one.
- This suggests a meaningful structural division between junk gates with multiple accepted singletons (unique allowable center) and junk gates with at most one accepted singleton. However this alone does not give a circuit-size bound: a unique center can have arbitrarily many leaves, and the repeated-label conditions allow many tops and junk gates at the same center.
- A broader wmax active-edge bound is not a new problem. The `oneSing` child in R_meta_1770_1 already asks for a linear bound on edges whose endpoints both fail singleton tests but whose pair is accepted by a junk gate with one endpoint in wmax. Therefore replacing the actual top-side witness by wmax risks duplicating an existing stronger unresolved statement, and loses the useful fixed-v side-disjoint condition.
- Bottommost pair-producing AND descent is blocked when the other AND operand requires v rather than singleton u; u-context does not propagate to the descendant. This is the same nesting obstruction found by circuit_geometry.

No counterexample to the actual step found. No finite example alone refutes the existential uniform constant; a family with unbounded edge/gate ratio would be needed.
