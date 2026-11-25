# Common-filter blocks

A common-filter block has a union of inner rectangles R, conjoined with the OR of point set A and line set B. Its accepted pair core is E = R restricted to pairs touching A or B.

Finite test: all 151,263 choices of nonempty P1,L1,P2,L2,W on 3+3 variables, and one million seeded random choices on 4+4 variables. 46,755 and 112,321 cases respectively passed semantic safety and C4-freeness. No counterexample. Minimum slack in |E|+tau(E)≤sumfivegroup sizes was 2. Script and exact output preserved in CommonFilterSearch.py and CommonFilterFinite.txt.

Checked stronger bound: a filtered rectangle Ei = (Pi×Li) restricted to touching A or B satisfies |Ei|+1≤|Pi|+|Li| if Pi and Li are nonempty and Ei is C4-free. Proof: if either side is singleton it is immediate; otherwise at most one selected row and one selected column exist, and the two stars overlap in their center edge when both exist. Exact cardinal inclusion-exclusion gives the inequality.

For a finite family T, union bound gives |E|+|T|≤sum_i(|Pi|+|Li|). The same A,B explicitly cover E. Hence |E|+|A|+|B|+|T|≤sumside sizes+|A|+|B|. This is the requested cost bound with a saving of |T| in the weighted-cover numerator. Geometry does not need the safety hypothesis.

Semantic binding is checked separately: the full block equals the graph function of E iff each inner rectangle pair together with each filter leaf contains an E edge. For a point filter leaf w, this means E(p,l) or E(w,l); for a line leaf w it means E(p,l) or E(p,w). `block_eq_graph_iff_safe` states this for any relation R; `core_two_rectangles`, `block_two_rectangles`, and `core_family` bind the concrete forms.

Files: CommonFilterGeometry.lean, CommonFilterSemantics.lean, and CommonFilterFamily.lean are complete frozen Lean-checked artifacts with Defs only. The final family file includes all earlier dependencies. Their suffix files isolate additions for integration. Full logs are common-filter-geometry, common-filter-semantics, and common-filter-family stdout/stderr under task scratch. Exit codes all 0; warnings are unused-variable/simp suggestions, stderr empty. Independent geometry audit passed.

Limitation: the comparison with circuit gates assumes independent OR trees for the groups. Arbitrary sharing of those OR computations still requires a sharper accounting lemma. Also, safety here is below the pair-core graph itself; being below some larger external graph alone does not imply safety.


Two-output OR sharing extension: a stronger candidate accounts for `max(|P1∩P2|-1,0)` shared point-OR gates and `max(|L1∩L2|-1,0)` shared line-OR gates. The sharper edge bound (even without safety) passed all 99,711 C4-free choices among exhaustive 3+3 cases and one million random choices each on 4+4 and 6+6 variables (433,724 and 138,481 C4-free cases). Exact output and a standalone script are CommonFilterSharingFinite.txt and CommonFilterEdgeSharingSearch.py.

The structural proof is now partly checked in CommonFilterSharing.lean and CommonFilterPruning.lean: common point variables have nested neighborhoods, so C4-freeness permits at most one common point of degree at least two. Delete all other common points, losing at most one edge each; both rectangle supports retain a common representative. Repeat on the line side by transposition, then apply the earlier independent-groups bound. Full strengthened cardinal accounting is being checked separately.


The full two-sided OR-sharing extension is now checked in `CommonFilterSharedBound.lean`: `shared_edges` proves

`|E| + 2 + (|P1∩P2|-1) + (|L1∩L2|-1) ≤ |P1|+|L1|+|P2|+|L2|`,

where subtraction is natural-number subtraction. `shared_cover` supplies the same explicit A,B cover and corresponding weighted bound. This accounts for the reusable common point-OR and line-OR subtrees while retaining a two-gate margin, but still treats W's OR computation separately. Independent audit passed at frozen SHA256 `44fcd155695ea7b14b17197daadfd06200598cf1c9a80e22921c3aebfe790e0c`. Lean exit 0, full warnings in `common-filter-shared-bound2.stdout`, empty stderr.


Latest finite-only refinement, completed before the lease pause: permit full optimal OR-DAG sharing among all three point targets P1,P2,A and all three line targets L1,L2,B, plus one mixed W OR when both A,B are nonempty and the four displayed outer AND/OR gates. For n≤4 the OR-DAG optimum is enumerated exactly over all possible intermediate supports and minimized over supersets of required targets. Exhaustive3 (151,263 total,46,755 safe C4-free) and one million random4 (112,808 safe C4-free) found no counterexample; minimum physical saving is one gate. These figures are computational only; no general theorem proves the full sharing variant. Script/output: CommonFilterOrDagSearch.py and CommonFilterOrDagFinite.txt.

Root requested a pause after the desk lease error at 15:06 UTC. No further searches or builds are running. Current theorem endpoint remains CommonFilterSharedBound.lean, compiled exit0 and independently audited.
