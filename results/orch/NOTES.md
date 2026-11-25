# L-meta-1772 orchestration notes

Root holds the sole job lease. Acquired 2026-11-25 08:37:54 UTC, initial expiry 08:57:54 UTC. Root alone renews, commits, pushes, and submits.

Statement and lease source: /tmp/oec/pequalnp-pilot-77/desk-answer-6.json. Do not copy lease identifiers into repository artifacts.

Goal: there exists a minimal monotone fan-in-two circuit computing the graph edge function such that each AND gate owns an edge, assuming triangle-free and no-four-cycle. Only project import permitted: PEqualNP.Defs.

Proof environment: source /tmp/oec/pequalnp-pilot-77/lean-env.sh. Mathlib cache, checker executable, and PEqualNP.Defs are prebuilt. Never lake update or compile Mathlib from source.

Use strategy-specific files in results/orch/lemmas, with no conflicting edits. Append findings here with UTC time and agent name. Notify root immediately when any new Lean component compiles so it can be independently reviewed and pushed early. Never use sorry, axioms, or native_decide.

Final PR must add only lean/PEqualNP/Outside/L_meta_1772.lean, helpers scoped to its matching namespace and the fully qualified theorem last. Artifacts will remain accessible in branch history.


2026-11-25T08:40:44.058277+00:00 status_review

## Strategy review: existing checked routes

- L_meta_5355 (about 400 lines) proves exactly the star-builder hypothesis of R_meta_1772_642: for any vertex cover T, a circuit of size at most |E|+|T|-1 computes the graph function and every AND owns an edge. This supplies constructive feasible good circuits, but not minimality.
- L_meta_1906 (946 lines) transforms any monotone fan-in-two graph circuit whose every AND function is below the output into a circuit no larger in which every AND owns an edge. Its final proof ignores triangle-free, no-C4 and minimality assumptions. The hard missing piece is safe-AND normalization without growing an arbitrary minimum circuit; R_meta_1904_* expose this same difficulty.
- R_meta_1772_773 is lexicographic minimization over count of unowned ANDs. Its pivotal premise is essentially proved by L_meta_7141 / L_meta_8363; extra profile/first-bad premises look unused in the core proof. Repair remains the key hard part.
- R_meta_1772_418 leaf peeling uses core (no degree-one vertices) and restore-a-leaf hypotheses, neither obviously easier enough to finish directly.
- Latest CONTRIBUTING requires helper declarations inside namespace PEqualNP.Outside.L_meta_1772 (or _aux), fully qualified final theorem last; named namespace/section/end commands begin column zero. No global helper instances or simp lemmas.
- L_meta_1036 is in upstream at commit f463ca8 and states an at-most-seven-input monotone multi-output family has a one-NOT circuit strictly smaller than every NOT-free circuit. L-meta-1035 PR bot says stood down.

## 2026-11-25T08:41:08.290034+00:00 minimal-route

Upstream L_meta_2666 already proves minimal monotone graph-circuit existence via an explicit binary DNF circuit and Nat.find. Adapted to results/orch/lemmas/minimal_route.lean, namespace PEqualNP.Outside.L_meta_1772_aux.minimal; lake env lean passes, log /tmp/oec/pequalnp-pilot-77/minimal-route-build-2.log.

Upstream L_meta_2668 provides full eraseGate/bypass semantics, monotonicity, and pivotality: every gate of a minimal monotone graph circuit loses an edge when erased to false. Adapting separately into bypass_route.lean. Thus existence and pivotality from R_meta_1772_773 are solved; ownership repair remains the difficult hypothesis.

- 2026-11-25T08:41:20.760013+00:00 counterexample: `edgeless_case` compiled in lemmas/counterexample_route.lean; full desired conclusion holds for all edgeless graphs, including n=0, using zero gates and missing output n. No finite counterexample found yet. Main semantic risk: Owns forbids any true AND in the strict structural cone, even if on an inactive path.

## 2026-11-25T08:41:48.829396+00:00 minimal-route update

bypass_route.lean now compiles (exit 0); adapted L_meta_2668, namespace PEqualNP.Outside.L_meta_1772_aux.bypass. Complete log /tmp/oec/pequalnp-pilot-77/bypass-route-build-1.log. Available: erase_eq_bypass; bypass_eval_eq; bypass_eval_rel for arbitrary reflexive operator-preserved Boolean relations; bypass_mono; wire_monotone; lost_edge; main (pivotal edge witness). File stable for review/push.

2026-11-25T08:43:06.238602+00:00 status_review

Independent red-team review PASS for partial preservation only (not full L-meta-1772). Reviewed explicit diff-to-empty, complete minimal constructor, edgeless witness, and bypass helper source against checked L_meta_7141 (identical except namespace/comment/wrapper). No prohibited commands, axioms, unsafe evaluation, quotes, reserved name text, attributes, or options; allowed imports; matching helper namespaces; regular nonexecutables. Build logs show warnings only. Actual reviewed lines: counterexample_route 19; minimal_route 142; bypass_route 456. SHA256 respectively: 1d7d1464af1c47fe0c806c38530fa6d6d6f5091dcd9dfa5135fd1cb6464a13ee; ba9726cb168194578ed36e48e736b772ce6e23fba308577de5a3893c346c4995; 069c4cf89c1a7bd1302647ab08a17745833676ac36988e21f593e82fe758107f. The components establish edgeless target, existence of a minimal graph circuit, and edge pivotality under erasing a gate. They do not establish repair/ownership for a general minimal circuit. Full target checker not yet run/accepted.

## 2026-11-25T08:43:10.179369+00:00 ownership_route

Compiled results/orch/lemmas/ownership_route.lean with only Mathlib and PEqualNP.Defs. Cone recurrence and strictness adapted from checked L_meta_1906; new lemmas prove cone transitivity, that any pair-true AND has an owning AND at itself or in its strict cone, and that a non-owning pair-true AND has a strictly earlier owning ancestor. This requires no graph/monotonicity assumptions. Log /tmp/oec/pequalnp-pilot-77/ownership-route-build.log is empty; Lean exit 0. Root notified for early push.
Existing L_meta_1906 transforms an all-AND-BelowF minimal graph circuit to one with every AND owning an edge; its strong BelowF premise is not established by that proof. L_meta_7141 has generic gate essentiality on edge minterms; minimal_route is adapting equivalent bypass toolkit from L_meta_2668.

## 2026-11-25T08:43:34.672774+00:00 minimal-route irredundancy

irredundancy_route.lean compiles (exit 0), log /tmp/oec/pequalnp-pilot-77/irredundancy-route-build-1.log. It includes bypass_route as a prefix plus 3 new lemmas: minimal_no_alias, minimal_gate_true_somewhere, minimal_gate_not_input. Same ...aux.bypass namespace: choose irredundancy_route instead of bypass_route when assembling, do not include both.

L_meta_4181 and L_meta_7860 establish least TopForm circuits, but TopForm permits junk AND gates not BelowF; all-AND-BelowF is not furnished by that normalization. Ownership still needs repair for such junk gates.

## 2026-11-25T08:43:46.592138+00:00 graph_normal_form

Compiled results/orch/lemmas/normal_form_route.lean (49 lines, empty full log normal-form-build-4.log, Lean exit 0). New lemmas: NoFourCycle forces either side of a complete bipartite pair of vertex finsets to have cardinality at most one; graphFun on pairInput equals adjacency; consequently an AND of two input-OR sets below the graph function has a singleton-or-empty side. Root and reviewer notified for push-early.

Conceptual normal form: lifting a below-F AND out of later AND cones can lower AND-cone pairs without increasing size. This is essentially the already solved all-safe-AND case in L_meta_1906. The real obstruction is removing or making safe the dirty AND gates; NoFourCycle alone only bounds already-safe biclique products. EdgeFnFinal lower bound handles the much stronger T7 graph class and does not resolve arbitrary girth at least five.

2026-11-25T08:45:26.896130+00:00 status_review

Independent second partial review PASS. Files reviewed against empty and approved prefixes: ownership_route.lean 147 lines SHA256 d5b2b261160e1f1d4e280f3a9780de6cfd488cb06b6ecaa4464875e5f712a146; normal_form_route.lean 48 lines SHA256 ba0ccb662aa89eca0e5f01ca60c980725fb581f038d9dc3d126279fbff25568e; irredundancy_route.lean 487 lines SHA256 95eac55a7382c9ea5ed8010e01845a15b1f2d70004a4b738ff61a3b28368aed8. No prohibited syntax/axioms/evaluation/quotes/attributes/options; regular nonexecutables, correct namespace scopes. Logs contain no errors. The owning-ancestor result uses valid well-founded descent and cone transitivity; it does NOT promote ancestor ownership to the original gate. Biclique-thin and pair evaluation arguments checked. Irredundancy is the exact approved bypass prefix plus three consequences of minimum size. Do not concatenate full bypass and irredundancy files into one final source: they redeclare the same helper names.

2026-11-25T08:46:47.719782+00:00 repair_exchange

A non-owning AND can be pivotal in a nonminimal girth-valid graph circuit: g=(a OR c) AND (b OR d), j=g AND (a OR d) computes path edges ab, ad, cd, but j owns no edge because g is a true AND ancestor on all edge pairs. Replacing j by either operand is unsound. The distributive exchange ((a OR c) AND (b OR d)) AND (a OR d) = (a AND (b OR d)) OR (c AND d) turns 5 gates into 4 if the relevant intermediates are unshared. Arbitrary fan-out is the central obstacle to promoting this to the repair hypothesis. A concrete Lean certificate is being checked in lemmas/repair_route.lean.
Read project paper https://pequalnp.com/papers/note-1 on 2026-11-25: prior-work section explicitly distinguishes formula/single-level girth bounds from unrestricted monotone circuits; exact cover-number bound is checked only on restricted sparse graph classes there. No general lower-bound shortcut is established by that source.

## 2026-11-25T08:47:22.007554+00:00 minimal-route cleaning (frozen)

clean_route.lean compiles, exit 0, complete log /tmp/oec/pequalnp-pilot-77/clean-route-build-3.log. Frozen pending independent review/push. Namespace PEqualNP.Outside.L_meta_1772_aux.clean. Contains bypass infrastructure plus NEW cleaning theorem: minimal Monotone2 circuits false on all-false input have exactly two distinct earlier wires at every gate (no constants/unary/repeated/forward-read gates). Main bridges: minimal_isAO2; minimal_graph_isLeastAO; leastAO_graph_isMinimal. Thus IsLeastAO and Monotone2 minimality agree on graph functions.

2026-11-25T08:47:58.329814+00:00 status_review

Third independent partial review PASS. counterexample_route.lean 44 lines SHA256 64f21838c6c088ed55ae826edd2328092bf72246a3640d35b4564ffe0c56f154; repair_route.lean 64 lines SHA256 57b2900da0c4b1d85b6806d064dadb4b42055a6208991746bbe363367aa44f48; clean_route.lean 670 lines SHA256 79b28312544f6230432014b0c9102fad69628d49bad5926542713476c1c404ea. C5 witness computes five-cycle in seven gates with every AND owning an edge, but has no minimum-size proof. P4 local exchange is a valid Boolean absorption identity and decreases five gates to four; all circuit facts kernel-decided. Clean route exactly reuses the approved bypass prefix (namespace renamed); all 214 added lines reviewed, including no aliases, no constant true for zero-preserving functions, exact fan-in two with distinct earlier operands, and minimum-monotone/least-AO equivalence. Verified actual model permits arbitrary output index, so empty graph/zero-gate output n remains covered. Logs no errors; source forbidden/format scan clean. These are partial components only.

## 2026-11-25T08:48:46.388802+00:00 graph_normal_form update

Compiled results/orch/lemmas/dirty_repair_route.lean (301 lines, empty log dirty-repair-build-2.log, exit 0). Adapts checked L_meta_8305 unique-lost-edge dirty-gate repair, adds two_pivots: among no-larger monotone circuits for the same graph, a junk-count-minimal circuit has each dirty AND pivotal for an edge distinct from every given edge. This forces at least two distinct pivotal edge assignments when the graph has an edge. Root/reviewer notified for push.

Read Jukna primary paper via built-in read-only web on 2026-11-25: https://web.vu.lt/mif/s.jukna/ftp/single1.pdf (Disproving the single level conjecture), pp.3,10. Its separation uses saturated extensions with two cliques; these contain triangles and four-cycles, so this is not a counterexample to L-meta-1772. It does confirm the single-level lower bound |E| for K2,2-free graphs. Any claim that this refutes girth-five safe normalization is unsupported.

## 2026-11-25T08:49:16.483727+00:00 minimal-route TopForm normalization (frozen)

topform_route.lean compiles, exit 0, complete log /tmp/oec/pequalnp-pilot-77/topform-route-build-1.log. Frozen pending independent review/push. Includes clean_route as prefix, then adapted L_meta_5779 exchange machinery (Defs only source), then new bridge PEqualNP.Outside.L_meta_1772_aux.topform.minimal_has_topform. This gives an equal-size minimal Monotone2 TopForm circuit for every minimal graph circuit, even empty graphs, with no girth assumption. Choose topform_route instead of clean_route in final assembly.

2026-11-25T08:51:50.881250+00:00 status_review

Fourth independent partial review PASS. topform_route.lean 1543 lines SHA256 aa2c43baec244382a29e62226d21aa96fe3042a4676e8f5e4c231c80436ac80b contains exact approved clean prefix, exact L_meta_5779 helper block under renamed namespace, and a valid minimum-monotone-to-TopForm wrapper (empty case separately forces zero gates). dirty_repair_route.lean 297 lines SHA256 82fcf98ff53e2955822da6d4e612bcdc3de69d61d64824ff7ba33a2724ea4bdc contains exact L_meta_8305 helper block and a valid contradiction proof that a least-junk dirty gate has a pivotal pair distinct from any specified graph edge. No prohibited source syntax or format violations; logs no errors.

Finite artifact review PASS as computational evidence only. Independently reran both README commands, exit zero and empty stderr; all JSON rows matched stored n4/n5 logs after removing elapsed time. Four vertices: 38/38 eligible graphs; five vertices: 291/303 found by five gates, 958669 depth-five states, and no six-gate five-cycle witness. All recorded minimum witnesses have ownership. Reviewed semantic-state deduplication, omission of duplicate signals, free false via missing wire, constant true handling, and strict AND-cone tracking. None of these finite lower bounds is Lean-certified. Program SHA256 f8ff1c914bb63a4d2ea0092584f005cfae19be94c11c568d49b0ee0b7c7e6316.

## 2026-11-25T08:52:49.252061+00:00 minimal-route junk-preserving TopForm (frozen)

Added minimal_has_topform_junk to topform_route.lean; exit 0, log /tmp/oec/pequalnp-pilot-77/topform-route-build-2.log. Witness D preserves minimum size and junk cardinality and satisfies TopForm. Original bridge retained. Graph-normal-form agent owns minimum-junk selection and canonical witness assembly with two-pivot dirty repair.

## 2026-11-25T08:52:52.477673+00:00 ownership_route singleton phase (frozen)

singleton_route.lean compiles, 258 lines, empty full log singleton-route-build-2.log, exit 0. Includes the original 147-line ownership_route prefix unchanged; use singleton_route instead of ownership_route in final assembly. New gate_mono, own_ancestor_singleton_false, and topform_bad_has_dirty_owner. The last proves: in TopForm, a non-owning AND true on a pair has a strictly earlier dirty AND in its cone owning that same pair. Hence every pivotal edge of a bad AND is blocked by a dirty owning ancestor, not merely any AND ancestor. No graph-girth assumption needed for this lemma. Root notified for independent review/push.
Singleton-false normal-form claim remains unproved: saved finite minimum witnesses (eligible n4 and n5 forests) satisfy it; no claim of exhaustive circuit-structure verification.
