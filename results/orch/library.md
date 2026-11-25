# Library route notes

## Established pieces

- `L_meta_2666.lean`: existence of a minimum monotone fan-in-two circuit for every finite graph edge function. Construction enumerates ordered edges with one AND and OR per edge, then takes `Nat.find` of feasible sizes. Adapted into `L_meta_2448.lean` as `L_meta_2448_aux.minimal_exists`, 142 lines, awaiting local toolchain/build.
- `L_meta_7069.lean`: same minimum existence with no-triangle/no-four-cycle assumptions (unused). No advantage over 2666.
- `L_meta_2668.lean`: every AND gate of a minimum circuit has some graph edge lost by replacing the gate by false and deleting it. Does not establish ownership.
- `L_meta_8237.lean`: if a gate in a minimum graph circuit fires on singleton p, replacing the gate by p loses some edge avoiding p.
- `L_meta_8415.lean`: a false-positive gate signal in a minimum circuit must eventually encounter a downstream AND that blocks it.
- `L_meta_7141.lean`: same deletion witness as 2668, with unused star-profile hypotheses; cannot supply star profile.
- `L_meta_7860.lean` and `L_meta_8567.lean`: existence of least circuits in TopForm, but TopForm permits dirty AND gates, so does not immediately imply ownership stars.

## Existing decompositions

`R_meta_2448_1`: minimum existence plus a star-profile replacement of each minimum circuit.

`R_meta_2448_17`: first find a minimum circuit whose each owned-edge graph has cross edges between disjoint edges; classify gate graphs as empty/double-stars/five-cycles, then iteratively repair one gate.

`R_meta_2448_263`: the clearest repair strategy. Define conflict gates as those owning two vertex-disjoint edges. Choose a minimum circuit minimizing the number of conflicts. A complete local lemma `pairDirt` shows a conflict gate must fire on a singleton or nonedge within the four endpoints. Remaining hSingle/hPair repairs preserve graph function and do not increase gate count while decreasing conflicts. No checked L theorem supplies these repairs in the current clone.

No checked general theorem mentioning HasStarProfile has that property as its conclusion. Every match is a reduction or a theorem assuming the property.

## Global lower-bound route

- `L_meta_531.lean` proves the exact lower bound `|E(G)| + |T| <= formula.leaves` for a vertex cover T of a triangle-free, four-cycle-free graph. Its proof uses formula rectangles and a rank argument. This is a FORMULA result; a circuit may share intermediate gates. Unfolding a circuit into a formula can increase size exponentially, so the lemma cannot be applied at the circuit gate budget.
- `L_meta_2399.lean` proves an AND-gate lower bound by vertex-cover number only when that number is at most five; it is not a general full gate-count bound.
- `L_meta_3679.lean` is a checked counterexample to the claim that arbitrary bipartite graph functions have a least circuit with no AND gate in another AND gate cone. Its example has many four-cycles, so it does not refute this task, but rules out relying on an unrestricted Boolean homogeneous normalization theorem.
- A potential no-four-cycle argument would show that sharing noninput subcomputations cannot improve the monotone formula bound; no complete argument found. The analogy to union/intersection circuits computing set families whose rows intersect in at most one point is suggestive but does not establish the single-output graph circuit claim.
- GitHub-limited literature searches did not locate a primary theorem settling this normalization. No external claim was used in the partial Lean file.
