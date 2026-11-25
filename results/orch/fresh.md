# Fresh full-theorem attempt

Scope: read README.md, CONTRIBUTING.md, exact gap.json, ownership definitions, current global/structural/library notes, and the critical-obstruction/countdown proof in L_meta_2399. No desk, git, publication, or named-file mutations.

## Status

No full proof or counterexample found. No new Lean declaration is proposed for the deliverable. The obstacle remains global sharing between two or more dirty AND gates.

## Routes examined

1. **Global AND cover extraction.** In canonical free-OR top form, each clean AND whose two operands both have singleton supports creates a complete bipartite set of new graph edges. No four-cycle makes that set a star. This does not cover all edges: an edge can be created at a dirty ancestor and inherited through the clean AND, even when an operand has no singleton support. A proof must assign at most one cover vertex per distinct AND across these shared inherited contributions, rather than one vertex per clean output. The C7 four-AND witness in the structural notes rules out demanding that the original gate ownership itself supply that assignment.

2. **Induction by restrictions.** Setting one vertex to zero drops vertex-cover number by at most one, but does not remove an earliest AND with two wide OR supports. Setting a vertex to one removes some ANDs but replaces the target with unary neighbor terms plus a residual graph; the residual cover number can drop by more than one (already on C5). Thus the obvious gate-elimination induction does not establish the desired bound.

3. **Generic normalization of quadratic functions.** Arbitrary monotone quadratic functions do not admit an AND-count-preserving homogeneous normal form in general. The known saturated-graph counterexamples prevent using such a theorem without girth. A subdivision transfer to remove short cycles has no evident savings-preserving construction: the incidence function has fresh edge variables and exactness on independent assignments prevents direct reuse of the code gadgets. Structural_proof independently reached the same obstruction.

4. **Formula unfolding / local distributivity.** Unfolding a shared circuit into a formula cannot use the checked formula lower bound at the original gate budget. At a dirty gate g, the monotone Shannon context has the form (g AND H) OR K. Correctness forces H to block false-positive inputs of g; its other AND gates may share operands and contexts. No argument found that extracts a complete rewritable component with enough input gates to pay for all output interfaces. The existing boundary-count lemma isolates exactly this missing inequality.

5. **Generalizing the small-cover theorem.** L_meta_2399's cover-size-at-most-five bound is a real finite catalogue/countdown proof. Its general critical-obstruction reduction gives a graph on at most 2t vertices, but the concluding AND lower bound still depends on finite enumerations for t<=5. No symbolic induction follows from the obstruction reduction alone.

## Potential next mathematical target

A useful genuinely global statement would be an extraction theorem assigning a vertex cover T to a canonical top-form circuit with |T| no larger than its AND count, together with an independent OR-count lower bound |E|-1. Neither inequality is established here. Even the first needs to handle several dirty cones sharing AND ancestors; local ownership stars and pair-truth constraints are insufficient. Exactness on independent inputs of size three and larger is essential.
