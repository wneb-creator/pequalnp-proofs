# Local C6 with three private leaves

The cached Lean check passes for `c6leaf_three_eligible_impossible`: a strict live nine-input binary AND/OR Dag computing the incidence function with edges `(0,3),(0,5),(0,6),(1,3),(1,4),(1,7),(2,4),(2,5),(2,8)` cannot have at most eleven gates while all three point labels 0,1,2 are eligible. Here eligibility means the label occurs in the singleton support of some branching wire.

The proof first constructs pure first branches only for the three point labels, whose neighborhoods satisfy the required local separation. Their three surplus units exhaust the entire size-eleven budget. Thus no line label is eligible. The shared lines 3 and 5 each have one pure consuming operand whose opposite operand carries point 0. The edge from point 0 to its private leaf 6 forces a third distinct consuming position for point 0. Singleton carrier flow permits at most two, a contradiction.

Degree-one private leaves do not satisfy the accepted global graph-separation hypothesis. The new generic lemmas deliberately require separation only for the particular point or shared-line labels where it is used; the private-leaf edge uses the weaker loopless joint-meeting argument. No global graph-separation assertion is made.

This is a local component obstruction. Transporting a Fano circuit to this component while preserving all three eligible point labels and saving the necessary gates remains unproved. In particular, a wire with singleton support {i} may compute i OR H for a nonlinear H. Zeroing i does not by itself delete its assigned star gate. Neither functional purity nor protected-star deletion is claimed here.

The cached source uses the accepted source module PNPAccepted6659. A separate permitted-import standalone is prepared from the exact accepted first2534 lines, closing SemCodes, followed by the new tail under the pilot namespace. Accepted source attribution: https://github.com/open-goat/pequalnp-proofs/pull/13206 . The standalone is not yet checked. The first cached attempt failed only on definitional projections before rewriting/arithmetic; its complete source and diagnostics are preserved separately.
