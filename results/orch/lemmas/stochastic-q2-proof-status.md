# Remaining p10 line case: exact finite interface and proof status

Canonical labels are local line positions 0..6, corresponding to actual inputs 7..13. Point neighborhoods are [11,69,98,49,88,44,22]. The ineligible points are {0,1,2,3}; missing neighborhoods are points {2,4,5,6}. Required occurring masks are 11,69,49. The assigned mask S of ineligible point2 strictly contains98.

## Simplified residual obstruction (computationally complete; root owns Lean certificate)

Choose any S strictly containing98, with no size restriction. Let B={11,69,49,S}. Choose each assigned mask A_i from B containing N_i, for i=0,1,2,3, and require A_2=S. Choose three residual-unit support masks U_0,U_1,U_2, each either of size at most2 or a member of B. Empty support is allowed. Define r_t={j:t belongs to U_j}.

Budget: for every local line t, the number of assigned masks A_i containing t, plus 0 when t=0 and1 otherwise, is at most2+|r_t|.

Co-label: for each i<4, x in N_i, and t<7, if r_x is a subset of r_t and either r_x is nonempty or x,t occur together in one of the fixed required triples 11,69,49, then t belongs to A_i. Equality x=t is harmless, since the assigned-neighborhood condition already supplies it. It suffices to use these known masks as witnesses; unknown additional shared wires impose only stronger constraints.

Center bound: |r_0| + number of t in {1,...,6} with r_t subset r_0 is at most5. No shared-wire condition is needed here: required masks11,69,49 contain0 and together cover all seven lines.

The relaxed C++ enumeration covers all15 strict supersets S, all33 allowed support masks per S, and all assigned choices. It checks1,221,858 ordered tuples;34,140 satisfy budget,382 also satisfy co-label, and none satisfy the center bound. Source stochastic-q2-simple-colabel.cpp retains unused stronger diagnostic predicates after this decisive test; they are not assumptions of the simplified conclusion. Its direct_center_survivors_before_protection is the decisive0 field. The independent set-based script stochastic-q2-simple-independent.py treats units as unordered multisets with multiplicity, and checks this exact simplified predicate.

## Saturated seven-mask family and closure

The parent-family census takes one parent choice for each required triple: a contained pair, a containing4-set, or two5-sets whose intersection is the triple. It also includes S. Of15,000 choices,5,307 produce a family Y of size7. Count saturation permits all empty/singleton masks, all12 pairs contained in none of the required triples, and the seven Y masks; every actual projected wire mask must lie in that allowed set.

Starting from empty/singleton masks, repeatedly admit unions and intersections when the result is allowed. Both gate operations are essential. All actual wire masks belong to this least restricted closure by induction on the circuit. Of the5,307 families,181 have all their masks reachable. Each such family consists of the three required triples, S, and three pairs. Thus every allowed residual mask has size at most2 or lies in B, and every assigned mask lies in B. This is the only family-shape consequence needed for the simplified residual obstruction. These finite computations are not yet kernel certificates.

Exact181-family domains, assigned choices, and the six automorphisms preserving I0123 and missingpoint2 are in stochastic-q2-finite-domain.json. They form42 family orbits:19 of size6,22 of size3, and one singleton orbit. Unit ordering is symmetric in every predicate, so one can use nondecreasing support masks (unordered multisets). The entire181-family table and all5,307 seven-families are preserved as text files.

## Existing checked ingredients and remaining transfer work

Already kernel-checked generic ingredients: equality_residual_co_label; equality_assigned_budget and equality_assigned_budget_extra; equality_count_mask_family and equality_hw_mask_family; sup_triple_parent from the accepted source. Their uses require actual occurring-mask or shared-wire witnesses, not mere numerical overlap. The budget extra1 at t!=0 uses an eligible adjacent point; local line0 has three ineligible neighbors and receives no such extra.

The +9 cofactor wrapper equality_cf_nine_free is cached kernel-checked and independently reviewed. Use center actual7, J={1,2,3} of K4 original labels, which maps to eligible points4,5,6. X contains only line inputs, so is disjoint from those three free points and the center. Its conclusion gives exactly the center bound under total surplus at most14. Its full standalone archival rebuild is separate and was still running when this note was written.

New count-saturation allowed-mask bridge is owned by algebraic_route (algebraic-line-q2-saturation-tail.lean). Generic restricted-mask closure induction is owned by lean_setup. Their current receipts must be consulted before claiming them compiled. Root owns the finite Lean certificate. Actual-circuit coordinate transport, closure-shape certificate, simplified residual certificate, and final q2 contradiction still need composition and kernel verification. None of the computational survivor counts is a complete circuit or a proof of the posted L-meta-1479 statement.

Protected three-slot equality and all-center old cofactor inequalities were used in preliminary diagnostics but are unnecessary for the simplified predicate. Preliminary342 combined states, their11 symmetry classes, and later18 old-cofactor states remain archived as exploratory data; they are not counterexamples or claims of circuit feasibility.
