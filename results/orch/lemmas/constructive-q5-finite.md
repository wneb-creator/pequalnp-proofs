# Five ineligible points: finite residual-support obstruction

This is a smaller finite lemma for the canonical ineligible points {0,1,2,3,4}, with protected points {0,1,3}. It is not a proof of the full posted gap.

Use six line labels [7,8,10,11,12,13], omitting line9. Their incidences with points0..4 are exactly the five rows of q5_neighbors. After indexing the three residual units by Fin3, let r[t] be the set of units carrying line t. Every selected line has a nonempty residual mask: each has either three ineligible neighbors, or two ineligible neighbors and a third eligible neighbor, forcing at least three consumption positions.

Residual-mask inclusion r[x] subset r[t] forces line t into the assigned operand of every ineligible neighbor of x. This is q5_forced, using algebraic equality_residual_co_label. If a protected point has an adjacent selected line other than7 whose residual mask has size1, equality_three_slot_full makes its assigned operand exactly its neighborhood. Finally, assigned positions are injective; for lines8,10,11,12 an additional edge-slot at an eligible point is distinct from all five assigned positions. The accepted code-count budget gives the final inequality in q5_constraints.

There are five free nonempty masks on three units. The kernel certificates examine all Fin8 mask codes (including empty masks, excluded by the hypotheses). If the line7 mask is {0}, no assignment satisfies the constraints. If it is {0,1}, exactly four assignments survive, and every one has line13 mask {0,1,2}. The four code vectors are [3,5,5,6,6,7], [3,5,6,6,5,7], [3,6,5,5,6,7], and [3,6,6,5,5,7]. Independent Python enumeration by status_review agrees.

When all three residual units carry line13, every other line with a nonempty residual mask shares a wire with13. The omitted line9 shares the protected point1 neighborhood mask with13 even if its own residual mask is empty. Cofactoring at13 then loses its three residual units and the reserved units of all seven lines, contradicting the accepted K4 lower bound. The explicit cofactor list is [0,3,5,6,7,10,8,12,11,9]. If all three residual units already carry7, the same argument uses accepted cfL7.

The actual residual-set indexing, derivation of q5_constraints, saturation geometry, and final cofactor contradiction are owned by algebraic_route. The finite certificate is an independently reviewable component of that argument.
