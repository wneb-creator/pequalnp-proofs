# L-meta-1477 orchestration notes

Lease acquired 2026-11-24 07:34:53 UTC. Root alone renews/submits.

Exact statement: /tmp/oec/pequalnp-pilot-29/statement.txt
Desk response: /tmp/oec/pequalnp-pilot-29/desk-response-8.json
Allowed project import: PEqualNP.Defs.
Final file: lean/PEqualNP/Outside/L_meta_1477.lean

Target: no monotone fan-in-two circuit of size at most 124 computes the 42-input, 105-edge incidence function of the order-4 projective plane. Standard star cover uses 125 gates.

Build environment: source /tmp/oec/pequalnp-pilot-29/lean-env.sh
Helpers must live in namespace PEqualNP.Outside.L_meta_1477 or _aux; final theorem last.

Agents append findings here with UTC timestamps. Own scratch files under results/orch/lemmas or task scratch; do not edit the final file unless root assigns it. No desk calls, commits, or pushes by agents.

2026-11-24 07:36:45 UTC Geometry: Lean-checked exact planeEdges list, length=105 and Nodup. File lemmas/Geometry.lean; success log /tmp/oec/pequalnp-pilot-29/geometry-initial.log. Next: bipartition, regularity, C4-free, matching.

## Existing lemma route — 2026-11-24T07:37:56.995354+00:00

- No lemma/theorem declarations occur in lean/PEqualNP/Defs; only definitions/instances. All substantive Outside results need in-file reconstruction.
- Open PR search found 5 reductions of L-meta-1477 (#4306, #4082, #4245, #4181, #4229), no open proof/refutation. Existing R_meta_1477_1 reduces to AND firing on a fixed 10-vertex independent set plus exclusion of that event under size 124.
- Best proven general conditional bound: L_meta_1602 (920 lines), helper pairCleanBound; every AND false on all singleton/nonedge pair inputs => cover T with |E|+|T| <= size+1 for C4-free graph. Final theorem ignores its initial hypothetical premise; inspect the actual helper.
- L_meta_1527 (324 lines) normalizes Monotone2 to IsAO2 at no cost. L_meta_1733 (4001 lines) additionally obtains least AO plus TopForm for girth>=5. L_meta_1491 counts edges+tops+2*centreless+junk+ORoutsideLambda against size+Ustar+1. L_meta_1528 (3495 lines) gives stronger single-junk bound. Main unresolved bridge: eliminate or charge dirty AND gates, not finite geometry.
- Independent GeometryInitial.lean audit PASS: exact ordered 105-edge list; kernel decide for length/Nodup; no forbidden code; SHA256 f18bac7c5fb77896aa5c870db410fb167f524a5f2bd0023cca996abbe719f2d7.

2026-11-24 07:38:38 UTC Geometry: Geometry.lean now compiles with planeEdges length105/Nodup/card105, bipartition bounds, both degree5 facts, diagonal perfect matching, and planeEdges_vertexCover_lower for arbitrary Finset Nat cover (card>=21). Full success log geometry-cover.log. Common-neighbor-card1 proof still compiling separately.

2026-11-24T07:38:54.952137+00:00 NormalForm: COMPILED lemmas/NormalForm.lean (319 lines), adapted checked L_meta_1527 into PEqualNP.Outside.L_meta_1477.NF. normalizeBinary: Monotone2 graph-function circuit -> IsAO2 circuit of no larger size, same function. Full log /tmp/oec/pequalnp-pilot-29/normal-form-build.log (warnings only). General star-cover normalization remains open: dirty AND products can contain nonedges which later gates filter; cannot assume pair-clean. Existing L_meta_1733 can additionally choose least circuit in TopForm, but leaves junk/Ustar.

### Library conditional bound compiled — 2026-11-24T07:39:01.925670+00:00

`results/orch/lemmas/Library.lean` (921 lines) contains copied/re-scoped pair-clean infrastructure from L_meta_1602, with helpers changed from theorem to lemma. New `PEqualNP.Outside.L_meta_1477.Library.clean_graph_lower_bound` drops only the unused initial hypothesis from L_meta_1602; retains C4-free, Monotone2, graphFun equality, and every AND false on nonedge pair inputs. Gives cover S with |E|+|S| <= size+1. `lake env lean ../results/orch/lemmas/Library.lean` exited 0; full log /tmp/oec/pequalnp-pilot-29/library-build.log empty. Root notified for push-early preservation. Main gap remains clean normalization.

2026-11-24T07:39:10.801326+00:00 Counterexample search: Circuit evaluator has no indexing/constant loophole. Exact SAT synthesis for C6 returned UNSAT at7 gates (2.55s) and SAT at8; extracted size8 witness independently evaluated correctly on all64 assignments. This is computational evidence only, not Lean checked. C6 with one private leaf per left vertex (9 inputs,9 edges) is now running at10 gates vs standard11. Search program lemmas/Search.py; full logs in task scratch search-c6*.log.

2026-11-24T07:39:48.263507+00:00 Counterexample agent independent review: NormalForm.lean PASS as partial, SHA256915b7fbdbe9e2a93e55c78c19eb4f4f3411b5040fd05bc3b4f455f67210cdd3d,319lines. Exact L_meta_1527 main_aux modulo namespace/helper renaming and removed wrapper; no forbidden mechanisms. It proves normalization, not the124 lowerbound; change helper theorem keyword to lemma when integrating final file.

2026-11-24T07:40:03.832999+00:00 NormalForm independent review: GeometryCover.lean PASS, SHA256 681d8c2b92225cc6cded47e0e78211e03d4ca128ec00f93529956cfecca521bd. Posted edge-list equality independently parsed; 105 distinct edges; 21 disjoint diagonal edges imply vertex-cover>=21 by injective endpoint selection. Source conforms for partial storage.

### Count bounds and incidence specialization — 2026-11-24T07:41:36.285874+00:00

- L_meta_217 proves ANDcount>=t for C4-free graph only when t<=5. L_meta_634 proves 7 ANDs for Fano incidence; L_meta_910 proves same from boundary tests. L_meta_1006 refutes universal C4-free AND>=cover in the weaker maximal-independent-set boundary-test model (11 vertices, cover>=7,6 ANDs); it is not a refutation for exact graph computation.
- L_meta_910 Fano proof obtains >=4 gates omitting a point using 9 distinct MIS containing it, then <=6 total ANDs implies at most2 operand-literals per point. Its generic no_cover_gt works with this2-literal limit. For our plane, exact Python neighborhood-union enumeration gives25,237 MIS and6,296 through each left point; entropy argument only yields13 omitted gates, hence at most7 literals if<=20 AND. These counts are UNVERIFIED by Lean; full computation log /tmp/oec/pequalnp-pilot-29/plane-mis-count.log.
- No existing generic OR>=|E|-1 result found. L_meta_724 proves8 ORs for a9-edge pair-of-pentagons graph using a generic free-AND/paid-OR program and graph-specific recurrence/probes. Arithmetic separated-polynomial searches found no transferable library lower-bound result.

- 2026-11-24T07:41:54.696416+00:00 gate_invariants: GateInvariant.lean now compiles, build004. first_mixing_gate gives a genuine binary AND with crossed operands whenever a Monotone2 circuit violates join preservation on three inputs z≤x∨y. Handles nullary/unary gates and missing/forward reads without normalization. Main snapshot frozen for root review. The remaining counting obstacle is that a gate may create a rectangle including nonedges later filtered by ANDs.

2026-11-24 07:44:18 UTC Geometry: frozen GeometryC4.lean compiled with no-rectangle and exact common-neighbor-card1; independent normal_form review PASS. Frozen GeometryGraphCounts.lean also compiled: planeGraph symmetrizes exact ordered edges on Fin42; planeGraph_card=105 via explicit edgeSet bijection; planeGraph_cover_lower>=21. Complete logs geometry-full.log (empty) and geometry-graph.log (one concrete-instance lint warning). Combined graph C4/fun equivalence build running.

### Quantitative dirty-gate compensation — 2026-11-24T07:44:43.743075+00:00

For a least TopForm circuit define U=|Ustar|, t=|tops\centreless|, c=|centreless|, j=|junk|, o=|orN\lam|. L_meta_1491 yields 105+t+2c+j+o <= size+U+1. The exact sufficient missing bound is U+21 <= t+2c+j+o. This permits arbitrary dirty gates; pair-clean is only the U=0 endpoint.
If K is a minimum cover of G\Ustar, k<=t and5-regularity gives105<=5*k+U<=5*t+U. Therefore the stronger incidence-specific charging target6*U <=5*(2*c+j+o) suffices to close size>=125 by arithmetic. No proof of this charging inequality is currently known. Expansion alone points in the wrong direction: it lower-bounds U for a small cover and does not pay for U.
For one junk gate, L_meta_1528 supplies K and overhead B=|pen|+1+|mixing|+2c+|coneGates|, with105+|K|+B<=size+U+1. Sufficient target is U+21<=|K|+B, or more concretely a set V covering the U edges left uncovered by K with U+|V\K|<=B.
Independent review GateInvariant.lean PASS (170lines, SHA25600a752cb31ec54e8f632db1957c448106e6b65362e2969eaa4a0608c759b368f); first_mixing_gate valid including forward/missing-wire handling. Build004 only2 unused simp-argument warnings.

## Structural route 2026-11-24T07:45:27.378370+00:00

- Arbitrary dirty AND gates can create nonedge pairs then have them filtered; raw biclique counting is insufficient. Existing pairCleanBound covers exactly the no-dirty-pair case.
- One-junk approach: g=(OR A) AND (OR B). An effective clean mask center in A requires B inside its neighborhood, and vice versa. If both sets have size at least 2, C4-free gives at most two effective centers. Opposite-orientation centers are adjacent; in a bipartite graph they have disjoint neighborhoods, so an OR context with bare variables cannot be shared between both masks.
- Lean-checked graph-side lemmas are in results/orch/lemmas/Structural.lean (build-002 exit0, log in task scratch). These do not yet normalize arbitrary circuits.
- A Python finite count gives 25,237 maximal independent sets of the plane incidence graph (not Lean-checked). Thus a generic maxterm-count AND lower bound only gives 15 ANDs, below the needed 21.

2026-11-24 07:46:34 UTC Geometry COMPLETE: frozen GeometryGraph.lean (also current Geometry.lean) compiled, containing planeGraph cardinal105, all covers>=21, no four-cycle, and graph edge predicate iff posted edge list. Only concrete-instance lint warning. Frozen Hyperoval.lean compiled with empty log: points[0,1,2,3,10,19],15 pairlines, induced K6 incidence, no other incident lines, each line hits0or2 points. Exact maps and kernel proofs available for local counterexample transport; computational search data scratch hyperoval.json. Independent reviews requested.

2026-11-24T07:47:03.479890+00:00 Counterexample route update: no evaluator loopholes. Local C6 exact7-gate search UNSAT, 8-gate SAT witness checked on64inputs; concurrent3-star core exact7-gate search UNSAT. These are computational and exact-size statements only. Private-leaf C6 exact10-gate runs did not finish; pruned run timed out120s, older redundant encodings deliberately stopped. HIGH PRIORITY K6-hyperoval core at34gates now running with88extremal tests,17,544vars/769,300clauses,1800s cap; K4-incidence core at14gates running600s. Script Search.py has topological ordering, first-gate S_k orbits, and irredundancy pruning; UNSAT would not automatically exclude smaller irredundant circuits. Only2SAT processes retained because host has5CPUs.

### Named module substantive partial — 2026-11-24T07:47:56.124289+00:00

`lean/PEqualNP/Outside/L_meta_1477.lean` now combines frozen GeometryGraph and Library helpers plus `short_plane_circuit_has_dirty_pair`: a Monotone2 circuit of size<=124 computing the exactposted42-input105-edge function must have an internal AND true on a nonedge pair. Proof contraposes Library.clean_graph_lower_bound and uses105edges+cover lower21. `lake build PEqualNP.Outside.L_meta_1477` exited0; full log /tmp/oec/pequalnp-pilot-29/named-partial-build-001.log.1165lines,55,524bytes,SHA2568b0efa64971d4b3827fae8acb1200e2c957949b15d1b7b90b693ce956d5c2cbf. Final theorem name remains undeclared, so this is partial only. Root notified immediately; named file frozen for independentreview+push.
