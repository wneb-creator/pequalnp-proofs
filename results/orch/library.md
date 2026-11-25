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

## Audit of L_meta_3760 one-junk proof

The theorem needs bipartiteness in addition to no four-cycle. Its endpoint is that a least AO circuit cannot have exactly one dirty AND; this is stronger than star profile for one gate and not yet the target for arbitrary triangle-free graphs.

Exact uses of `junk G C = {g}`:

1. Lines 6846–6889 (`junk_single_props`): uniqueness proves no AND ancestor of g, and also that every AND ancestor of every clean top is g. Selecting the earliest dirty gate generalizes the first part, via TopForm excluding clean-AND ancestors. It does not generalize the second part.
2. Lines 6932–6952 (`g_semantics`): g is a conjunction of two pure ORs. This local part extends to an earliest dirty gate. No global single-junk assumption is inherently needed once the ancestor-free condition is supplied.
3. Lines 4191–4205 (`M1528.P2.final`): global uniqueness of every top AND ancestor is proved and passed into the abstract cover-count theorem at lines 4242–4245. This is the first decisive nonlocal obstacle.
4. Lines 7163 onward (`ustar_edge_structure`): every residual edge fires g and has an endpoint in `wmax g`. This is a global attribution of all residual edges to the sole dirty gate.
5. Lines 7678–7708 (`replace_gate_by_wire`): for a clean top, an operand not reaching g has no AND ancestor and therefore is a pure OR. With a second dirty gate, that operand may reach the other gate, so deletion soundness fails.

Earliest/latest induction: earliest g gives pure input cones, while latest g rules out dirty descendants; neither eliminates other dirty ancestors of affected clean tops or disjoint dirty subsystems. A valid generalization needs a local residual-edge partition and disjoint accounting of shared OR/cone resources. Merely summing the one-gate counting argument would count shared gates multiple times. No valid iterative repair was obtained from this proof.

## Local coloring and newly checked combinatorics

The bipartition of a singleton-silent AND ownership graph does not replace all global coloring in `L_meta_3760`. At lines 9010–9017, the proof forbids an edge across the endpoints of a four-edge path; that requires excluding an odd five-cycle. On C5 with edges 01,12,23,34,40, choose P={0,2}, Q={1,4}. The ownership cross graph is bipartite, the two centers are p=0,q=1, and w=3 covers every missing P×Q pair. Nevertheless w is adjacent to both noncenters 2 and 4, defeating the global coloring step.

New checked artifacts (only Mathlib, no extra axioms):

- `/tmp/oec/pequalnp-pilot-75/library/DoubleStar.lean`, 73 lines, frozen: `doubleStar_guards` proves that for C4-free double-star sides P,Q each of cardinal at least three, a vertex covering all missing P×Q pairs must be one of the centers. `doubleStar_guard_adjacent` proves the directional version: if P has cardinal at least three, every guard other than its common neighbor q is adjacent to all Q vertices except q. Build exited 0.
- `/tmp/oec/pequalnp-pilot-75/library/TwoCenter.lean`, 35 lines, frozen: `twoCenter_guard_adjacent` allows the other center p to lie outside P, requiring only the center edge p–q. This fits an auxiliary center supplied by a shared pure OR block. Build exited 0.

Potential target-specific repair avoids proving one-junk impossibility: if all indispensable graph edges of AND g contain z and z OR-reaches one operand, replace that operand by z. The new g is old g AND z, requires no extra gate, preserves all graph edges, and its owned edges form a star. Earlier gate profiles stay fixed. For one-junk circuits, edges in starEdges have witnesses independent of g, so a residual Ustar star may provide the indispensable-edge condition. This is only a sufficient repair, not an established universal existence claim.

The finite agent disproved the unrestricted claim that indispensable edges of every minimum AND form a star: minimum P4 circuit AND01; OR13; OR(2,AND01); final AND has all three edges indispensable, but owns only the last two. Thus only nonstar ownership gates could satisfy any proposed additional existence theorem.

## Checked weaker accounting for one dirty AND

At 07:48 UTC, `OneJunkAll.lean` (1327 lines, 75,497 bytes; SHA256 `f1ece5b1a70acb180e3ab37905534addaa2e3e1dea06d7a6110ba19a7103ae9c`) compiled with exit 0. Its final helper `one_junk_cover_all` proves:

`NoFourCycle G` + triangle-freeness + `IsLeastAO G C` + `TopForm G C` + `junk G C = {g}` imply a vertex cover T with `G.edgeFinset.card + T.card <= C.size + 1`.

This removes both bipartiteness and singleton silence from the earlier 601-line `OneJunk.lean` prototype. All frozen scratch artifacts are in `/tmp/oec/pequalnp-pilot-75/library/`; the complete build log is `one-junk-all-build.log` and contains only two unused-hypothesis warnings. The prototype still imports `PEqualNP.Outside.L_meta_3760`, so it is not eligible for final submission without extracting allowed-import dependencies. Root is preserving and independently reviewing it.

The mathematical change is that a same-size star-cover circuit only needs one fewer unit than the original L3760 contradiction. For disjoint pure OR sides, the cone counts alone plus one mixing/centreless gate pay for one or two cover centers. If the sides intersect in at least two vertices, use only the residual common-neighbor leaf set in the cone count; no extra leaf selected by bipartite color is needed. If their intersection is one vertex, the relevant lambda block cannot contain adjacent vertices because it has a common center and G is triangle-free. This replaces the early color argument, and the later strict-improvement exchange is unnecessary.

This is a result for ONE dirty AND. It does not establish that an optimum with at most one dirty AND exists. A possible general accounting target is `E + K + |junk| + |mixing| + 2|centreless| + |unused OR| <= C.size + |Ustar| + 1`, together with a residual-cover bound `|Ustar| + |X\K| <= |junk| + |mixing| + 2|centreless| + |unused OR|`. These are only a roadmap: multiple dirty ancestors and shared OR cones remain unaccounted for.

`OneJunkTopFree.lean` adds `least_single_junk_cover`, removing the TopForm assumption by applying `thm_1501`, which preserves both minimum size and junk cardinality. It is frozen at 1347 lines, 76,404 bytes, SHA256 `3e52b5593b90cf015501d49aedbfc153edc88f3f0d4f577362404b4f07a233d7`; the complete `one-junk-topfree-build.log` reports exit 0 with the same two warnings.

`EarliestJunk.lean` is a separate checked local generalization, frozen at 130 lines, 6,355 bytes, SHA256 `81583b47c30731c317fd95887c32450ba3cdae1a64a5a798073d55cb519d7f2d`. For any IsAO2 circuit in TopForm, an earliest dirty AND has no AND ancestors, equals OR(P) AND OR(Q), and has the same Wmax guard characterization used by L3760. Neither circuit minimality nor uniqueness of junk is assumed. Build log `earliest-junk-build.log` is empty, exit 0.

The exact localization blocker is now downstream: a clean top may have two different dirty ancestors. Its operand opposite the selected g need not be pure OR, and there may be no vertex guard in Wmax(g). Thus preserving the region's boundary needs a rule for interactions between dirty signals, in addition to avoiding double-counting of shared OR cones.
