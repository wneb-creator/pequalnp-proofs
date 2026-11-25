# Gate elimination / tight branching route

The checked bound in L_meta_4725 gives at least15 non-NOT gates for full Petersen. L_meta_8039 strengthens its nine-vertex deletion to14 non-NOT using a tight branching budget and a finite signed profile ledger.

For full Petersen, a hypothetical15-non-NOT circuit has at most6 branching wires. The minimum vertex cover is6; the five complementary independent4-sets are equivalent under automorphisms. Tightness should imply each of the4 independent variables appears once in the unrolled output formula. The remaining6 vertices induce a matching of3 edges, while the4 independent-variable neighbor profiles correspond to the four triangles in K4 on6 edge-coordinates.

On the six singleton core assignments these profiles have masks56,38,21,11 (free-negation canonical forms7,25,21,11). Every pair of original profiles overlaps in one coordinate. Need establish a finite signed circuit/cover ledger budget ruling out15 non-NOT; this would at least exclude4NOT in a19-gate candidate. No full proof yet. Existing8039 finite cover checker uses7sample rows and shared active-term accounting and is a plausible source.
