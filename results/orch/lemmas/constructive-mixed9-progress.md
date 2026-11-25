Mixed p9 work, 2026-11-25

Canonical ineligible set: {0,1,2,5,11}. This work currently addresses the case with two missing cap-neighborhood masks, normalized to missing points {2,5} and protected points {0,1}. It does not yet close the one-missing-mask case or the posted gap.

The residual supported budget is three. Coordinate lines are [7,8,10,13,9,12], and cap rows are [0,1,2,5]. The row neighborhoods in these coordinates are {0,1,2}, {0,3,4}, {1,3,5}, {2,4,5}.

Finite predicate interfaces:

- Every line residual mask is nonempty. Two ineligible cap neighbors plus one eligible neighbor give three distinct consumption positions.
- No line mask contains all three residual units. Cofactoring at that line with the other five eligible lines would give 3+5+7 <= 14. The six explicit cofactor orderings and circuit transfer are algebraic_route's task.
- Neither missing point's exact neighborhood occurs as a residual unit's line support.
- Each missing point's assigned operand contains a chosen additional secant line. The extra choices are {0,2,4} for row2 and {0,1,3} for row3.
- Residual inclusion forces labels into assigned operands. Known assigned consumers plus one eligible-neighbor edge slot obey the supported-unit consumption budget.
- If this budget is exhausted at a neighbor of a protected point, its entire assigned operand is exactly that point's neighborhood. The generic equality_saturated_slot_full helper passed cached Lean and independent review.
- A nonempty eligible-point residual mask would force point labels into cap assigned operands, and line labels into line11's assigned operand. The point and line consumption budgets give m9_point_constraints.

An independently reconstructed Python predicate has 120 models with explicit extra choices, representing 30 residual line tuples. Every model saturates both protected rows and forbids all seven nonempty eligible-point residual masks. The actual-circuit transfer passed its complete permitted-import standalone build. The first complete finite run checked all128 kernel blocks and certificate assembly, then failed only in the two final API wrappers. The repaired996-line full build now passed exit0 with two unused-simp warnings and empty stderr, exporting unconditional m9_point_empty. The source and successful build are independently reviewed. The compact source uses 128 separate Boolean decision blocks, after normalizing the first residual mask to a singleton or pair. No native decision procedure or new axiom is used.

Proposed cofactor closure at point3:

- The fixed-false eligible neighbors7/12 have reserved branches with empty cofactor singleton support. equality_cofactor_neighbor_branch_empty passed cached Lean; a full standalone assembly is still pending.
- The original empty branches of missing points2/5 also have empty cofactor support when their assigned AND siblings lack point3. constructive-cofactor-empty-branch-tail.lean passed cached Lean and independent review. It combines the checked chain-agreement blocker with the checked nonedge-pair domination theorem.
- Protected points0/1 map to the opposite K4 edge vertices5/8. status_review has checked the scoped K4 supported-surplus lower bound8, requiring protection of vertex5. The stronger protection transport and SAME-E supported lower bound have both passed cached Lean and independent review.
- The compiled cached upper bound excludes exactly five reserved units at labels{3,4,6,7,12} and two distinct original empty branch units, leaving raw cofactor supported surplus at most7. It does not need to cover every original empty-supported unit. The same raw cofactor has supported lower bound8 under the checked protection hypotheses.

Remaining obligations are instantiating the checked conditional analytic composition with the now-checked finite certificate, its permitted-import standalone build, and the one-missing-mask case. Symmetry normalization of arbitrary pairs has separately passed cached Lean with its canonical contradiction premise explicit. The exact normalized missing-{2,5} composition is written with an explicit finite-certificate premise and independently source-reviewed; it is not yet claimed as an unconditional case theorem. Full standalone helper/composition builds and final checker remain required before final delivery.
