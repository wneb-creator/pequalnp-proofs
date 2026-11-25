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

2026-11-25T08:53:24.896510+00:00 status_review

Independent review PASS for latest frozen partials: repair_route.lean 83 lines SHA256 15444dbc7a2e01c9d2e76a5e4eb81f8d0441d9fdf35ad59b92efd9f1b49e8ad9; lex_selection_route.lean 43 lines SHA256 c272f479a9102cf354444a6ca35868f62ec8d10ff02f2bb58baa68322d919d59; topform_route.lean 1571 lines SHA256 c639c94f815369781987e89c752d22ffe2b3bb05098c604c0a534fd03b115bfe; singleton_route.lean 258 lines SHA256 78989bc31447d141e3a51b9ed889bc82dde820397cb1e3ff89d7a80cb24737be. Reviewed new content against approved prefixes. P4 is explicitly nonminimal, its final AND is pivotal, and both naive operand bypasses fail. Lexicographic Nat.find selection correctly quantifies over every no-larger correct monotone circuit. TopForm wrapper preserves junk count. Singleton lemmas correctly use gate monotonicity and derive a dirty owning ancestor (pair need not be a graph edge unless adjacency is separately supplied). Logs no errors; source scans clean.

Structural challenge: in TopForm a globally earliest dirty AND indeed has no AND ancestors, since every earlier AND would be safe and hence forbidden by TopForm. Clean exact-two-earlier-operand model then makes both operands ORs of nonempty input sets. Their supports may overlap; dirty rectangles need not be graph bicliques, so the no-four-cycle thin-biclique lemma cannot apply without an additional safety hypothesis. The earliest dirty AND itself owns every graph pair where it is true; an unowned AND must occur later and filter a dirty ancestor.

## 2026-11-25T08:53:55.845365+00:00 graph_normal_form canonical witness

Compiled standalone canonical_route.lean, only Mathlib and PEqualNP.Defs, exit 0; full log canonical-route-build-1.log (inherited warnings only). It combines minimal_route, strengthened topform_route, dirty_repair_route, new lex_selection_route (least-measure optimization by Nat.find), and new canonical glue. `PEqualNP.Outside.L_meta_1772_aux.canonical.witness n G` works for every graph, including edgeless: there is a minimum-size correct monotone circuit in TopForm, with minimum junk count among all no-larger correct monotone circuits, and every dirty AND gate loses at least two distinct edge assignments when forced false. Distinctness is equality of pairInput functions, so unordered-edge orientation cannot fake two edges.

This is the strongest established frontier; it does not prove every AND owns an edge. Source frozen and root/reviewer notified for push.

2026-11-25T08:54:19.731645+00:00 status_review

Independent canonical assembly review PASS: canonical_route.lean 2110 lines SHA256 19928c58c0502b1955d8a0520eca31317bcc3a84df345462d0609266d3af5d11. Verified exact unchanged bodies of minimal_route, strengthened topform_route, dirty_repair_route, and lex_selection_route, each present once with shared imports. Reviewed 56-line glue: a dirty gate in a minimum graph circuit forces at least one graph edge; least-junk optimization survives size/junk-preserving TopForm normalization; applying two_pivots twice gives two distinct pivotal pairInputs for every junk gate. No girth assumption required for this partial canonical witness. Source scan clean, build log no errors. Does not establish every AND owns an edge.

## 2026-11-25T08:54:50.431019+00:00 minimal-route local AND absorption (frozen)

and_absorption_route.lean compiles exit 0; log /tmp/oec/pequalnp-pilot-77/and-absorption-route-build-1.log. Contains clean_route prefix plus 2 new lemmas: minimal_and_no_below_output and minimal_graph_and_operand_not_below. If an AND input lies below output, deleting that AND and redirecting its readers to the safe input preserves output (true inputs by monotonicity, false inputs by equality). Minimality forbids this. The graph wrapper discharges the common Core-style assumption that no AND operand is below graphFun. Extract final 2 lemmas when combining with topform_route.

2026-11-25T08:56:15.762752+00:00 repair_exchange update

repair_route.lean is compiled and frozen. Besides the path exchange, it proves the filtered circuit is not minimal, its final AND is pivotal on every graph edge, and both direct operand bypasses fail. Full latest log: /tmp/oec/pequalnp-pilot-77/repair-route-build.log (empty, exit 0).
Global-sharing obstruction refined: OR(a,c) in the path example cannot feed a safe star at a second center e without a 4-cycle a-d-c-e-a; OR(a,d) cannot feed any safe star at a distinct center without a triangle because ad is already an edge. Thus reuse that blocks the local exchange must go through dirty/nonlinear readers. TopForm ensures safe AND readers have no later AND descendants. A charging argument for dirty reuse is not proved.
TopForm plus an unowned pair-true AND yields a strict dirty owning ancestor (ownership agent has now proved this in singleton_route.lean). The earliest dirty gate in a cone has no AND ancestors under TopForm, hence pure OR sides under clean exact fan-in-two semantics. However it need not be true on the originally chosen pivotal edge; first-bad ownership only supplies some edge it owns. This edge-alignment gap must not be skipped.

- 2026-11-25T08:56:23.551699+00:00 counterexample: finite semantic BFS supports all 38 girth>=5 graphs on n=4, all 291 forests on n=5; five-cycle requires at least 7 gates computationally (958669 five-gate states, no possible sixth gate). Explicit 7-gate C5 function and ownership now Lean-checked in counterexample_route.lean (not its minimum). Reproducible programs/logs in finite/. General all64 n=4 graph BFS also found only ownership-good minimum witnesses (not exhaustive all structural minima).
- 2026-11-25T08:56:23.551716+00:00 counterexample: Z3 5.3.3 downloaded from public GitHub release to scratch; solver matches BFS for P4 min4 and C5 min7. C5=7 with a non-owning AND is UNSAT (15.4s); C6<=7 UNSAT (7.6s); C6=8 non-owning AND query timed out90s. Larger theta/Petersen/Fano queries underway; no Lean certification of SAT/UNSAT claims.

## 2026-11-25T08:56:48.523607+00:00 ownership_route singleton pivotal phase (frozen)

singleton_pivotal_route.lean compiles, 770 lines; full log singleton-pivotal-build-2.log, exit 0, clean-prefix deprecation warnings only. Contains unchanged clean_route prefix plus new namespace ...aux.singletonPivotal; in assembly reuse existing clean/topform prefix and append only singletonPivotal suffix. General underapprox_lost_edge shows every valid pointwise-weaker replacement wire loses an edge in a minimum graph circuit. singleton_true_has_disjoint_pivotal then proves any gate true on singleton z is pivotal under redirect-to-z for some graph edge uv with both endpoints different from z. This gives a checked necessary hybrid-support condition, not a singleton-false normal form. Root notified for review/push.

## 2026-11-25T08:57:44.337706+00:00 root replanning

Infrastructure is complete and compiled; avoid new generic lemmas without direct use in ownership repair. Preserve exact existential target: bad optimal circuits would not alone refute existence of a good optimum. Three live reductions already fill this step's reduction cap. Main combinatorial bottleneck is arbitrary fan-out among dirty OR-rectangles and later filters. No proof/refutation or full checker verdict yet.

## 2026-11-25T08:58:08.556108+00:00 minimal-route singleton filtering (frozen)

singleton_filter_route.lean compiles exit 0; log /tmp/oec/pequalnp-pilot-77/singleton-filter-route-build-2.log. Clean prefix plus 4 lemmas: graph_pair_true_iff; belowF_and_singletons_adj (true singletons across safe AND operands give an edge); triangle_filter_no_two_singletons (opposite operand cannot contain both endpoints of an edge if one operand contains a fixed singleton); noFour_safe_and_singleton_star (one operand singleton-support is subsingleton). These are local graph constraints. Missing: expose a safe downstream filter through dirty intermediate ANDs, then use ownership agent singleton-disjoint-pivot witness for a cost-preserving repair.

2026-11-25T08:58:40.202307+00:00 status_review

Independent review PASS: and_absorption_route.lean 721 lines SHA256 b0f26b72b11e68a5a7639d784797b189182e3444de535127fb8a0534c9e6af4f; singleton_pivotal_route.lean 770 lines SHA256 bd03fc82e4ece6312d3752d41400f05d4c131258289071ea10dd064a8d1fdadc. Approved clean prefixes unchanged. Reviewed AND-bypass absorption argument (safe operand implies removable AND), generic underapproximation lost-edge lemma, and singleton-true gate forcing a disjoint pivotal edge when redirected to that input. All equality directions and monotonicity uses correct; source scans clean, logs no errors.

GitHub read-only PR census: complete canonical open-goat search returned 15 results with incomplete_results=false, all closed. No open L-meta-1772 PR found. Merged PR7293 titled L-meta-1772 adds R_meta_1772_642 only. Latest PR12371 was an accepted reduction closed unrecorded because the contributor already had five live reductions. No unnoticed full completion found.

Scope check: repository note notes/note-1-edge-function-exact-size.md distinguishes its checked long-thread/forest/cycle bounds from the nearest quoted single-level monotone result on K2,2-free graphs. Literature statements in that note were not independently rechecked against papers here. L1772 alone does not assert star profile, global safety, single-level form, or a gate-count lower bound; no direct implication of a known major open bound was established. The remaining exchange is a global mathematical step rather than just missing elementary Lean infrastructure.

2026-11-25T09:01:30.013409+00:00 status_review

Independent review PASS: singleton_filter_route.lean 755 lines SHA256 f191a9e6dc2534c58ddcacbd49c6049d3c3bdc24766c25b7a182130c8c08d0ef; sharing_route.lean 62 lines SHA256 1619062547fc4234fd24b15a89ed59fc2747a5bed96c29d260371a381f4cbdd5. Singleton filter lemmas correctly require explicit safe AND and constrain singleton supports only. Mixed-reader safety is tested at support {d,e,p}; this forces de/dp/ep adjacency. Triangle-free eliminates de, and no-four-cycle common-neighbor uniqueness gives p=a or f=d or f=e. Repeated vertex cases are covered without hidden distinctness assumptions. Source scans clean, build logs no errors.

2026-11-25T09:05:13.861030+00:00 status_review

Independent SAT audit PASS for computational evidence only. Reviewed baseline, ordered, and normalized encodings; complete edge and maximal-independent samples; exact strict-cone ownership expressions; active-prefix copies; distinct sampled signatures; canonical topological ordering by (maximum operand, minimum operand, operation); and combined graph-automorphism first-pair representatives. The minimum-circuit scope in SAT_README is necessary and correctly stated. Properties are existential and invariant under the permitted renamings. No implication from a nonminimal bad witness to refutation is claimed.

Independently reran baseline P4 with three gates (UNSAT) and four gates (SAT, full truth table verified), plus normalized ordered/distinct-prefix/pair-orbit C5 with six gates (UNSAT), C5 with seven gates and a non-owning AND (UNSAT), and P4 with five gates and a non-owning AND (SAT, full truth table and ownership verified). All matched, with empty stderr. Verified installed Z3 version 5.3.3 and wheel SHA256 0431023a82278dab706c02a320f63178ee0755fb8f10a5c980f0bfe3c84f6f96 against recorded metadata. Parsed all 17 completed logs; timeouts stay unknown. Reviewed 22-file hash manifest saved in scratch as review-sat-manifest.json. Program SHA256 prefixes: baseline 0442105ca992edce; ordered b38a057c3eb233ed; normalized 6a51d08f12615a6c. README f73c45c03cae4bd3. No Lean or LRAT certificate was generated, and no theorem refutation was found.

### 2026-11-25 09:05:46 UTC — source mining / factor fan-out exchange (lean_setup)

Adapted upstream L3297 to `lemmas/factor_substitution_route.lean` (689 lines), namespace `...aux.factorSubstitution`, theorem `.exchange`. Compiles exit 0, frozen for independent review/push. The frontier absorption, OR-merge consistency, output-exclusion, and liveness assumptions are preserved exactly. Sent interface to repair_exchange and graph_normal_form. See `SOURCE_MINING.md` for source blocks, applicability limits, and exact line references. No SharedOr/ReadKJoin proof predicates currently appear in the L_ proof corpus; its three CarriedProduct L_ proofs give singleton-false carrier and live-pruning results. Three R_ reduction files also reference CarriedProduct. SOURCE_MINING.md records additional assumptions and the output-exclusion caveat for L3710.

2026-11-25T09:06:55.737302+00:00 repair_exchange sharing progress

Compiled and frozen sharing_route.lean and standalone sharing_linear_route.lean (the latter includes the former prefix). The linear extension proves: for dirty piece k=e AND (a OR d), graph edges ad,ae, a finite linear side T containing a, and f distinct d,e, pointwise safety of (k OR f) AND OR(T) under triangle-free/noC4 forces T={a}; the reader equals a AND (e OR f). This is a conditional local sharing rewrite, not the global repair theorem. Both full build logs are empty with exit 0.
Stronger simplifying observation (proof strategy, not yet a Lean theorem here): since ad and ae forbid de, k=e AND (a OR d) can itself be weakened to ea in the same gate slot. It preserves all graph-edge-pair evaluations and decreases pointwise, hence preserves any surrounding monotone graph circuit, regardless fan-out. Existing L3720 same_off/mono_off supply transport infrastructure. More generally any dirty AND true on exactly one graph edge can be replaced by the primitive AND for that edge, reducing dirty-AND count at equal total size. Therefore a minimum-junk normal form should force each dirty AND to accept at least two distinct graph edges.
Remaining hard reuse involves AND readers with multi-input/dirty opposite sides. Safe sharing alone is not globally excluded: the centerless matching cluster (A OR C)(B OR D) AND (A OR D)(B OR C) can have all four OR supports shared with safe stars in a girth-five subdivided-K4 graph. However that three-AND cluster has a same-cost two-edge-plus-OR replacement preserving the shared OR supports. Dirty sharing of intermediate rectangles still blocks this replacement.

2026-11-25T09:08:26.966228+00:00 status_review

Independent component review PASS for archival preservation: factor_substitution_route.lean 689 lines SHA256 8079c7a5c7da6d624df5e81eb12097451eb34c458fa145e47da627b2abba15bc is exactly L_meta_3297 with namespace/theorem renaming; its reader-consistency, absorption, output-exclusion, and liveness hypotheses are retained. Final-PR integration must move its currently top-level exchange theorem inside the helper namespace as a lemma. sharing_linear_route.lean 138 lines SHA256 69c440162d746e23a8c81235aeeac38eecd828f4159e3c9b52580b726cad241e extends the reviewed sharing prefix: safety forces adjacency f-p for each p in T, then a in T and f distinct from d,e collapse T to {a}; the Boolean rewrite follows. Build logs no errors and forbidden-source scans clean.

SOURCE_MINING narrative review requested corrections: three L_ proof files reference CarriedProduct, but three R_ files also do; L3710 leaves the output index unchanged, so making g unused requires output exclusion or an extra argument; L3700 additionally needs leastAO/lift-fixedpoint/no safe AND operand/all-live conditions; L3017 needs bipartiteness; L8415 states n>0. Other inspected scopes match.

### Independent review: single-edge signature repair
- UTC: 2026-11-25T09:16:23.219097+00:00
- `single_edge_route.lean`: PASS archival partial, 376 lines, SHA256 `5c5f6c67cfa905ed99d98166bc8898c8e6af07a5a75a8723879a332ca787ad38`.
- `single_edge_repair_route.lean`: PASS archival partial, 591 lines, SHA256 `ca9542102f5299ccef00363ec1fbd2227d92e14d81dd746256ea595c5ac19694`. Both full build logs empty, reported exit 0. No prohibited constructs found; namespace/imports permitted.
- Replacing j by the primitive uv AND keeps size and graph function, underapproximates every gate on every input, and makes j safe. Cone inclusion plus exact equality at every graph-edge pair preserves all old owned edges; j now owns uv, yielding strict finite bad-set inclusion and the exact R773 cost decrease.
- Scope: hpairs identifies j's values on ALL graph-edge pairs with the single uv monomial. This is a single-edge signature result, not a result from one pivotal edge alone. No triangle/C4/minimality assumptions needed for this conditional patch. General multi-edge repair remains open.

### Independent follow-up review: factor adapter and augmented checkpoint
- UTC: 2026-11-25T09:17:29.590668+00:00
- Corrected `factor_substitution_route.lean`: PASS, 688 lines, SHA256 `3fdd7115f1f54e662141fab87116bdfcf6278b5fa8df2fe751ba5c3c29984863`. Exact upstream L3297 body; namespace rename and theorem-to-helper relocation only. Build3 has eight existing deprecation warnings, no errors.
- SOURCE_MINING.md corrects all flagged scope statements (CarriedProduct L_ versus R_ census; L3710 output caveat; L3700 extra premises; L3017 bipartite; L8415 n>0). Its build-2 reference is an older successful run; current adapter log is build-3.
- `augmented_prefix.lean`: PASS archival partial, 41 lines, SHA256 `0c91ba0d17d14bf0505f40d2d2a043f0c3aac921b3e30c9b8f83b7ed60d22ac8`; byte-identical scratch source. Only graph/circuit data, hybrid size19, equal repaired size and Monotone2 for both. No graph correctness, minimality, girth or ownership theorem in this checkpoint. Log contains profiling output only, reported exit0.

[2026-11-25 09:18:07 UTC] graph_normal_form: rectangle_cluster_route.lean green/frozen; rectangle-cluster-build-2.log empty exit0. For four distinct corners, safe ((a+c)(b+d))((a+d)(b+c)) equals ab+cd, hence ab and cd must be graph edges. Triangle and four-cycle exclusions permit at most one cross edge among ac,ad,bc,bd. All graph edges recognized by either rectangle therefore form matching/P4, patchable in three operations using an existing two-input OR source. Cost warning: inject patch at existing safe intersection S, reusing its OR-only output path; adding a fresh OR with old output would cost four. Classification and Boolean identities formalized; circuit exchange remains pending.

### 2026-11-25 09:18:35 UTC — two protected-edge conditional aliases (lean_setup)

GREEN/FROZEN `lemmas/protected_edge_patch_route.lean`; main `...aux.protectedPatch.two_conditional_alias_repair`. Monotone graph circuit C, two dirty ANDs j<k, aliases p<n+j/q<n+k, graph edge uv, and exact gatej=p/gatek=q whenever xu&&xv=false imply existence of no-larger correct monotone D with strictly fewer dirty ANDs. Delete high then low; conditional equality preserves all negative-input gate values, injective skipIndex tracks junk, append ANDuv and OR restores the protected edge. No global pointwise decrease assumed. Output validity is derived from the graph edge and preserved through both deletions. Complete log `/tmp/oec/pequalnp-pilot-77/protected-edge-patch-route-build-4.log`, exit 0. Green file frozen for review/push.

### 2026-11-25 09:20:30 UTC — protected earlier-wire product patch (lean_setup)

GREEN/FROZEN `lemmas/protected_product_patch_route.lean`; unchanged protected-edge prefix plus namespace `...aux.protectedProduct`, main `.two_conditional_alias_repair`. Protect P(x)=original wire b(x)&&wire c(x), with b,c<n+j and P<=graphF. Explicit valid original output hypothesis. Two dirty gates j<k have earlier aliases p/q whenever P=false. Both b,c survive high-then-low deletions unconditionally; appended product+OR gives correct no-larger monotone circuit with strictly less junk. Arbitrary fan-out, no pointwise-decrease assumption. Full log `/tmp/oec/pequalnp-pilot-77/protected-product-patch-route-build-1.log`, exit 0 first compile. Frozen for review/push.

### Independent review: protected-edge two-alias repair and rectangle clusters
- UTC: 2026-11-25T09:20:49.602870+00:00
- `protected_edge_patch_route.lean`: PASS archival partial, 917 lines, SHA256 `37fb9782b5ef55d6f3d686fdf931164a6de73358d8f8b9cb6365a235b42062a4`; exact approved clean prefix plus new component. Build4 warning-only, reported exit0.
- Higher k deletion preserves j and earlier alias p. Both conditional equalities hold on ALL inputs where uv is false, which transports circuit equality despite arbitrary fan-out; on uv=true the protected graph edge makes output true after appending primitive AND plus OR. Original output validity follows from graph correctness and nonempty edge, and is retained through both bypasses.
- skipIndex injects new junk into old junk minus removed gate; j stays dirty after deleting k, giving two decreases. Two deletions fund exactly two appended gates, and appended gates add no junk. This is a strict JUNK-count reduction, not a claimed ownership-count reduction, and assumes two specific earlier conditional aliases rather than proving their existence.
- `rectangle_cluster_route.lean`: PASS archival partial, 92 lines, SHA256 `f7c53d435c1b583cceefacd310c4925463de61b373cea8bde8a33d7681eec51f`; empty build2 log. Matching plus cross-distinct hypotheses give four distinct corners; girth assumptions permit at most one cross edge. Boolean identities are kernel finite cases. No circuit/fan-out/minimality theorem here; a P4 patch uses three new operations only when its OR factor is already available.

[2026-11-25 09:21:23 UTC] graph_normal_form: rectangle_patch_route.lean green/frozen, rectangle-patch-build-2.log empty exit0. Contains unchanged rectangleCluster prefix and new rectanglePatch.safe_cluster_patch: safe opposite four-literal rectangle intersection plus girth yields one of five explicit matching/P4 formulas, pointwise below graph function and covering every graph pair activating either rectangle. This certifies arbitrary-fanout semantic loss repair; circuit slot/reindexing cost and injection at existing safe intersection remain unformalized. Larger OR-support cells cannot use constant-size loss repair blindly: two stars with matched leaf edges form girth-six theta graphs, and deleting shared rectangles can lose arbitrarily many leaf matching edges. General exchange must reclaim OR source costs as well.

### Independent review: protected earlier-wire product
- UTC: 2026-11-25T09:21:31.157503+00:00
- `protected_product_patch_route.lean`: PASS archival partial, 1091 lines, SHA256 `fed46c2f8fed1dc079f8eba9edaa6182fc1c48609837fd9b999d891ccd42f9ad`; exact reviewed edge prefix plus174lines. Build1 has48 warning entries and no errors, reported exit0.
- Protected b,c<n+j survive both higher-first bypasses with exactly equal values; this transports product safety and conditional alias domain. Explicit valid output is preserved. Both deleted gates are dirty, the new product is safe, and appended OR adds no junk; same size budget and strict junk decrease follow. This proves a conditional repair, not existence of suitable aliases/product and not ownership-count decrease.

### Independent review: safe rectangle-cluster Boolean patch
- UTC: 2026-11-25T09:22:11.288188+00:00
- `rectangle_patch_route.lean`: PASS archival partial, 233 lines, SHA256 `f0cf58ddf9fcf9eddf4b96bebe77c3b89f0b1ab1e549da6c82e3617a0b1734ce`; exact cluster prefix. Build2 log empty, reported exit0.
- Safe intersection implies matching edges ab,cd. The induced graph function on the four corners is globally safe and covers every graph-edge pair activating EITHER rectangle; graph exclusions express it as one of five small formulas. Coverage need not be equality with either rectangle. No circuit ordering, fan-out, gate-count or minimality theorem is claimed. P4 alternatives use three new operations when their one OR factor is already available.

2026-11-25T09:22:25.061636+00:00 repair_exchange merge map

- repair_route.lean: 83 lines, compiled snapshot.
- sharing_route.lean: 62 lines, compiled snapshot.
- sharing_linear_route.lean: 138 lines, compiled snapshot.
- single_edge_route.lean: 376 lines, compiled snapshot.
- single_edge_repair_route.lean: 591 lines, compiled snapshot.
For final assembly choose sharing_linear_route over sharing_route (the former contains the latter), and single_edge_repair_route over single_edge_route. Their namespaces are PEqualNP.Outside.L_meta_1772.Sharing and .SingleEdge, respectively. SingleEdge helper infrastructure adapted from L3720 is independent of the root clean namespace. The single-edge repair theorem proves full strict bad-AND-count drop for an exact single-edge graph-pair signature, preserving all old ownership witnesses via concrete cone inclusion.
Protected-product geometry: g1=(a1 OR b) AND (a1 OR c), g2=(a2 OR b) AND (a2 OR c), S=g1 AND g2 safe. P=b AND c is safe because P implies S, and each g_i=a_i OR P is a conditional alias off P. With b,c earlier than the lower gate, the new protectedProduct theorem applies even with arbitrary fanout. This establishes a full local shared-product cluster normalization once its syntactic/semantic shape is supplied; extraction from an arbitrary bad gate is still missing.

### Independent review: CaDiCaL pipeline
- UTC: 2026-11-25T09:24:11.526067+00:00
- PASS for eight artifacts in scratch `review-cadical-manifest.json`: sat_cadical.py, sat_external.py, SAT_README.md, cadical_solver.json, two P4 solver logs, P4 recovered model, theta233-10 UNKNOWN log.
- Reviewed normalized constraints unchanged. CNF transformation retains model converter; recovery requires exact regenerated bytes, verifies every clause, maps actual Boolean declarations, converts model, checks every original assertion, then evaluates full circuit semantics/ownership.
- Independently reran P4<=3 UNSAT (exit20), P4=4 SAT (exit10), identical fresh CNF export and successful model recovery with full truth table/ownership true. Source archive and four recorded CNF digests match metadata. Complete independent logs retained in scratch.
- These are computational results only. Theta<=10 timed out UNKNOWN. Augmented run was pending and is not included in this eight-file review manifest.

- 2026-11-25T09:25:30.802499+00:00 counterexample finite search concluded this batch: no counterexample to L-meta-1772 found. Edgeless case and explicit C5 size7/function/ownership are Lean-checked in counterexample_route.lean. Exhaustive semantic BFS supports all eligible n<=5 cases; general n4 retained minima also have ownership and singleton-false ANDs. Z3 computationally excludes bad-AND optimum for C5/C6 and singleton-true-AND optimum for C5; larger theta/sharedfilter/Petersen/Fano/augmented12 queries timed out. CaDiCaL alternate engine also UNKNOWN300s on theta<=10 and augmented12<=18. Thus augmented hybrid19 minimum remains UNVERIFIED. All programs, metadata and complete finished logs are preserved in finite/; no kernel certificate for search lower bounds.


2026-11-25T09:26:23.175921+00:00 repair_exchange shared hybrid repair

GREEN/FROZEN shared_hybrid_route.lean, unchanged protected_product_patch_route prefix plus sharedHybrid namespace. shared_hybrid_repair applies reviewed protectedProduct repair to exact semantic shapes gj=(a1 OR b) AND (a1 OR c), gk=(a2 OR b) AND (a2 OR c), and safe intersection S=gj AND gk. Earlier b,c product is safe because it implies S; off the product each hybrid aliases its center. Both gates must be dirty; TopForm plus genuine AND ancestry derives this via topform_ancestor_mem_junk. canonical_excludes_shared_hybrid rules out this pattern in a witness minimizing junk among all no-larger correct monotone circuits. Full build2 log contains inherited warnings only, exit 0. No girth assumption is needed for this conditional circuit exchange; extracting the shape from arbitrary bad gates remains open.

### Independent review: assignment snapshot and completed finite census
- UTC: 2026-11-25T09:26:41.836738+00:00
- `assignment.json` equals the public `gap` object in desk answer6 exactly; `statement.txt` is exact posted statement plus terminal newline. Only public gap keys copied; no lease/credential fields or long private-value overlap. SHA256 assignment `59e61fb924078b2bccd4fa96ad50a6598b0596f874c31ef2bd17ebedfa072de3`, statement `60926ce13575e9c3a5bbb4d3a18440a186117f61fc59c46c07ad5cbda32b490c`.
- Fourteen reviewed artifacts with repo-relative paths listed in scratch `review-assignment-finite-manifest.json`; only actually inspected files included.
- All-n4 search independently reproduced all counts excluding timing, exit0 and empty stderr. All64 labelled graph functions found; stored minimum witnesses are good. README now explicitly distinguishes representative-history diagnostics from an exhaustive structural census of all minima.
- Augmented candidate JSON independently re-evaluated on all4096inputs, full AND-ancestor ownership, singleton support, triangle/C4 checks and exhaustive minimum vertex cover6; every recorded field checked agrees. Minimum circuit19 remains UNVERIFIED.
- Three additional normalized runs are UNKNOWN/timeouts. CaDiCaL augmented18 full log is UNKNOWN after300seconds, exit0; no SAT/UNSAT/lower-bound claim. CNF export logs agree with previously verified digests.

### Independent review: shared hybrids and augmented girth
- UTC: 2026-11-25T09:27:36.274106+00:00
- `shared_hybrid_route.lean`: PASS archival partial, 1164lines, SHA256 `61cd2bc9c04216ca77797645f0a729ba1e0962edaf14c5b4935305b3caeae94f`. Exact product prefix; Boolean distributivity proves both aliases off protected product, and the safe intersection protects it. Least-junk canonicality then excludes this conditional pattern. TopForm AND ancestor is dirty by negating BelowF. Shape hypotheses are global equalities on ALL inputs. No existence-of-pattern result. Build2 warning-only, reported exit0.
- `augmented_girth.lean`: PASS archival partial, 68lines, SHA256 `0d797cf2e3fb36a96ee3e16f017f767ebf90daf8219bdc23cbfc45de77e91211`. Exact prior data prefix; triangle-free, exact neighbor table and NoFourCycle proved by bounded kernel cases. Only allowed limit options; decide +kernel is used, no native_decide. Byte-identical green scratch; build4 profiling only. No circuit correctness/ownership/minimum19 assertion in this checkpoint.


2026-11-25T09:27:43.187937+00:00 repair_exchange TopForm shared-hybrid corollary

GREEN/FROZEN shared_hybrid_topform_route.lean, 1254 lines, includes shared_hybrid_route unchanged. New namespace sharedHybridTopform proves actual binary AND/OR evaluation, a three-gate hybrid shape lemma, full topform_shared_hybrid_repair, and canonical_topform_excludes_shared_hybrid. TopForm plus genuine AND ancestry supplies both deleted gates being dirty, avoiding an unproved assumption. Exact source OR shapes still must be supplied/extracted; no claim that every bad gate yields this pattern. Full build1 exit0, inherited warnings only. Prefer this superset over shared_hybrid_route in assembly.

### 2026-11-25 09:28:59 UTC — arbitrary fan-out prefix replacement (lean_setup)

GREEN/FROZEN `lemmas/prefix_patch_route.lean`; main `...aux.prefixPatch.prefix_replacement`. Given monotone prefix B, correct monotone ReadsBack C, finite selected gate set S and prefix aliases, B.size<=S.card, all prefix ANDs below graphF, selected-to-alias domination on graph-edge pairs and reverse domination on graph-negative inputs, and at least one selected dirty gate, obtains correct no-larger monotone circuit with fewer junk gates. Builds prefix+shifted old circuit, overwrites selected gates as unary OR copies, proves simultaneous per-wire relation against ORIGINAL C, then deletes exact copies by maximum-index induction. This avoids the invalid inference that domination by original values alone survives successive increasing bypasses. No output validity, selected ordering, fan-out, OR-tail, or liveness assumption. `delete_aliases` proves size saving by selected cardinality and no junk increase; `extend_junk_le` injects remaining junk into old junk minus S. Full log `/tmp/oec/pequalnp-pilot-77/prefix-patch-route-build-3.log`, exit 0. Root and graph_normal_form notified; file frozen for review/push.

### Independent review: simultaneous prefix replacement and adapters
- UTC: 2026-11-25T09:31:29.931662+00:00
- `prefix_patch_route.lean`: PASS archival partial, 1217 lines, SHA256 `920b34eebe115129e98cc37f9570fc523cea1ec0530bf7adde73da558f3b07bd`. Exact edge prefix. A simultaneous original-to-transformed wire induction handles selected replacements directly, not by assuming sequential dominance. It covers arbitrary outputs, including out-of-range ones. Copies are deleted in descending index order, preserving earlier aliases; prefix size budget pays exactly for selected copies. Prefix safe ANDs plus negative implication inject new junk into old junk minus S, so one selected dirty gate ensures strict drop.
- `rectangle_prefix_route.lean`: PASS archival partial, 353 lines, SHA256 `fdd0997279cd006a87d5df720e2191107d1968a0d3b04b17fcd9a4e0b11f5aad`. Exact rectanglePatch prefix; concrete matching3/star4 circuits, full evaluations, safe ANDs and nonedge witnesses for both dirty rectangles.
- `shared_hybrid_topform_route.lean`: PASS archival partial, 1254 lines, SHA256 `f0529be2698088c80105f555943cef8b20cf97f5306d3cd143c5c89f42317d2b`. Exact sharedHybrid prefix; binary-gate adapters require earlier operands. Actual AND ancestry in TopForm supplies dirt, then existing conditional repair and canonical contradiction apply. No claim every unresolved circuit contains such a pattern.
- All three files pass syntax/import/namespace review; full build logs warning-only and reported exit0.

2026-11-25T09:31:31.827469+00:00 ownership_route
Frozen augmented_girth.lean verifies the explicit 12-vertex, 14-edge graph is triangle-free and has no four-cycle; both displayed circuits have 19 gates and Monotone2. Independent review passed. The hybrid has singleton-true ANDs and a non-owning AND; the repaired core replaces (z∨ab),(w∨ab),AND by zw,ab,OR. Complete semantic and ownership certificate is being finalized. Minimum19 remains UNVERIFIED; this is a local-repair benchmark and not a refutation of L-meta-1772.


2026-11-25T09:31:37.711179+00:00 repair_exchange canonical objective integration

GREEN/FROZEN single_edge_topform_route.lean, 689 lines, unchanged single_edge_repair_route prefix. New SingleEdgeTopform.edgePatch_junk_subset uses global underapproximation and unchanged operation labels; global minjunk then forces literal finite junk equality. BelowF iff nonmembership for valid AND gates transfers safe status, so cone inclusion proves edgePatch_preserves_topform. single_edge_topform_repair retains junk exactly and TopForm while strictly reducing bad-AND count. canonical_excludes_single_edge_bad therefore excludes exact one-edge graph-pair signatures in the nested minimum-size/minimum-junk/TopForm/minimum-bad witness, with interface coordinated with lean_setup canonicalBad.badCount (definitionally the same set). Full build1 log empty, exit0. No unproved compatibility between the two objectives is assumed.

- 2026-11-25T09:31:38.676035+00:00 counterexample/forest subtask: forest_route.lean compiled first try, exit0;2173lines,98073bytes,SHA256 c8ecc60c1ba8d32e6683cd2f9ad635f2bc8b067645047c8b03092cc29b3994e3. Full L1772 conclusion under G.IsAcyclic proved by Forest.forest_case, including edgeless/disconnected forests. L3525 forest lower bound and L5355 owned-star builder copied with namespace/declaration renaming only; Nat.find selects minimum cover, and upper/lower arithmetic gives minimality. Only Mathlib+Defs; no external proof imports, forbidden tokens, extra axioms or placeholders. Entire file frozen for independent review/push. Complete build output copied to validation/forest-route-build-1.log; warnings only.

### Independent review: complete forest subcase
- UTC: 2026-11-25T09:32:28.377199+00:00
- `forest_route.lean`: PASS archival partial, 2173 lines /98073bytes, SHA256 `c8ecc60c1ba8d32e6683cd2f9ad635f2bc8b067645047c8b03092cc29b3994e3`. Source sections mechanically equal upstream L3525 and L5355 modulo namespace rename, theorem-to-helper, duplicate-import removal and final wrapper relocation. No source hypotheses or proofs changed.
- New minimum-cover Nat.find construction yields tau; star builder gives size<=|E|+tau-1 and every AND owns; forest lower bound gives |E|+tau<=D.size+1 for every equivalent monotone D. Natural arithmetic proves minimum, including empty graph and n=0.
- This establishes the FULL target conclusion under `G.IsAcyclic`, a complete forest subcase. It does not cover the requested general triangle/C4-free cyclic graphs. No new unsafe/prohibited constructs found.
- Build1 reported exit0; full log has25 warnings/noerrors and is byte-identical in scratch/repository, SHA256 `29d5f1770aaf03798526227ad825a655958f85e1875edd4e6f1081ca75fbe970`.

### 2026-11-25 09:32:31 UTC — canonical minimum bad-AND count (lean_setup)

GREEN/FROZEN `lemmas/canonical_bad_route.lean`; unchanged canonical_route prefix plus `...aux.canonicalBad`. `least_top_measure` uses Nat.find to minimize any natural measure among correct no-larger TopForm circuits with junk cardinality no greater than a starting globally minjunk witness; preserves minimum size and global minimum junk. `.witness` specializes to badCount (definitionally SingleEdge.badGateSet.ncard), retaining TopForm and two distinct pivotal graph edges for every dirty AND. Its bad-minimum domain exactly matches repair_exchange single-edge TopForm repair. Complete log `/tmp/oec/pequalnp-pilot-77/canonical-bad-route-build-2.log`, exit 0. Frozen for review/push.

2026-11-25T09:32:34.207676+00:00 ownership_route
FROZEN GREEN augmented_exchange_route.lean,163 lines. Full log augmented-exchange-build-7.log exit0. Both 19-gate Monotone2 circuits compute the exact 12-vertex14-edge graph function; graph triangle-free and NoFourCycle; hybrid ANDs4,5 true on singleton0,1 respectively; hybrid AND6 owns no graph edge; every repaired AND owns an edge. Initial build7 used bv_decide and was subsequently held because it generated native axioms; see corrected build8 below. Minimum19 remains UNVERIFIED, so this is a same-cost exchange benchmark rather than L1772 proof/refutation. Source frozen and reviewer/root notified.


2026-11-25T09:32:38.085387+00:00 repair_exchange second-edge residual

GREEN/FROZEN single_edge_signature_route.lean, 759 lines, includes single_edge_topform_route unchanged. signature_or_second_edge gives exact single-edge graph-pair signature or a second accepted unordered edge. canonical_bad_has_second_edge uses nested minjunk/TopForm/minbad canonicality to force the latter for every bad AND, including safe filters (distinct from earlier dirty-only two-pivots). The accepted uv edge is an explicit hypothesis, supplied by pivotal/minimality when integrated. Full build1 log empty, exit0. No girth premise needed for this necessary condition.

[2026-11-25 09:33:48 UTC] graph_normal_form: FULL local opposite-rectangle circuit exchange GREEN/FROZEN in rectangle_exchange_route.lean; rectangle-exchange-build-3.log exit0, warnings only. Main rectangleExchange.opposite_rectangle_repair consumes correct Mono+ReadsBack C, three distinct valid ANDs with opposite four-literal rectangle/intersection semantic signatures, safe intersection, and four available input-OR signatures. It produces correct Mono D with size no larger and strictly fewer junk ANDs, arbitrary fanout and no relative-index assumptions. Uses lean_setup prefix_replacement; matching prefix3 deletes3AND, P4 prefix4 deletes3AND plus selected copied OR. This genuinely excludes the cluster from canonical minjunk circuits, but does not show every bad AND exposes such a cluster. Prefixes from prefix_patch and rectangle_prefix copied unchanged.

### Independent review: opposite-rectangle circuit exchange and shared-side exclusion
- UTC: 2026-11-25T09:34:43.450933+00:00
- `rectangle_exchange_route.lean`: PASS archival partial, 1766 lines, SHA256 `e8a9ba2967cc7c720c1e7cb9c5e0bdc7779ef26502bdbb11740b8f97817ec5bf`. Exact approved prefixPatch and rectanglePrefix bodies. Real simultaneous circuit replacement, correct under arbitrary fan-out: matching uses three selected ANDs; star uses those plus an existing globally equivalent OR, whose distinctness follows from operation type. Prefix insertion avoids forward-reference placement assumptions; copied OR exactness pays fourth gate. Correct graph function, no larger size, strict junk decrease. Global four-literal shapes, safe intersection and required OR existence remain explicit premises. Build3 warning-only.
- `shared_side_route.lean`: PASS archival partial, 153 lines, SHA256 `1e76631b0dd677476e52fd5c2b81e418aaceb0124525ac60feb0d356fd592f19`. Exact cluster prefix; triangle/C4/safety prove four cross-edge exclusions without assuming all five vertices distinct. Boolean/graph result only. Empty successful build1 log.
- HOLD: augmented_exchange_route initially used bv_decide. Installed Lean4.36 Bitblast.lean40 invokes nativeEqTrue; Native.lean76 creates Declaration.axiomDecl. Compilation alone therefore did not satisfy the no-new-axiom rule. Root/ownership agent notified before approval; replacement with pure Boolean proof in progress. Earlier reviewed archive scanned: no other bv_decide/bv_check/native_decide occurrence.

2026-11-25T09:35:26.562478+00:00 ownership_route
CORRECTION AND NEW GREEN: reviewer found this Lean version implements bv_decide using nativeEqTrue, so earlier build7 benchmark was held and never approved. Both uses replaced: graph_formula uses pure Boolean distributivity/commutative simp; hybrid_computes splits only4core bits (16cases) then simp. New full build8 exit0,no warnings/errors. Source163lines SHA2568645259980f664bc438d98554766e851c6fec63ec34c48d3de4dad87885c18c5, frozen for independent re-review and axiom-closure check. Earlier approved augmented_prefix and augmented_girth unchanged. Minimum19 still UNVERIFIED.

### Independent review: shared-side Boolean patch and repaired augmented benchmark
- UTC: 2026-11-25T09:37:17.825286+00:00
- `shared_side_patch_route.lean`: PASS archival partial, 567 lines, SHA256 `4758c9b91e2a4a6084ee067589d24cf4a70ee91c7327b27e3d8a4c426268d8ef`. Exact approved prefixes; exhaustive seven matching cases, safe six-edge function/pair coverage with explicit side-disjointness, concrete five-gate double-star evaluations and safe ANDs, and dirty rectangle witnesses. No circuit-exchange claim yet. Build1 has2 inherited warnings.
- HOLD CLEARED for `augmented_exchange_route.lean`: PASS frozen163line source SHA256 `8645259980f664bc438d98554766e851c6fec63ec34c48d3de4dad87885c18c5`. Native-certifying bv_decide calls replaced by pure Bool distributivity/AC simplification and16 Boolean cases. Source has no native proof tactic.
- Independent scratch compilation exit0 with #print axioms for triangle_free, no_four, graph_formula, hybrid_computes, repaired_computes, hybrid_unowned, repaired_ownership: all closures contain exactly propext, Classical.choice, Quot.sound; no new axioms. Full audit log scratch `review-augmented-axioms.log`, SHA256 `6ccb5f09eaa3675431d709520cae4743f3be06bf4db423ffec02860e69410ffc`.
- Benchmark now proves both19-gate circuits compute the exact12-vertex graph function, original singleton-true and unowned AND behavior, and every repaired AND owns. This is a kernel-checked finite repair, NOT a minimum19 proof or refutation.

### Independent review: optimization domains and copy adapter
- UTC: 2026-11-25T09:39:00.797679+00:00
- PASS `canonical_bad_route.lean` 2185lines SHA256 `33d3e8d74dcac2219c983988ec3bc873777a83b9ae34e1f9fa2e4505edfd0f8f`; `single_edge_topform_route.lean` 689lines `2487b61cc725c8f9b55613919add4589f8c2b929384a20dc61ca83e0d40b63f4`; `single_edge_signature_route.lean` 759lines `b28c0b8811ce19793bff4ace57636210dc197677561085f9c4eaf7da4ef2a428`; `shared_copy_route.lean` 2047lines `a8e311412a73b934a40b0edf1fab95bbd32b7cb74da72f5edf4b742d6ae659ff`. Inherited bodies exact; scans clean; successful logs consistent.
- canonicalBad retains minimum size and global minimum junk among no-larger correct circuits, then minimizes badCount within TopForm/no-more-junk domain. Single-edge patch gives junk subset; global least-junk forces exact Finset equality, which transfers safe status and preserves TopForm using cone inclusion. Thus strict BAD-count decrease lies inside precisely the chosen optimization domain. The two bad-count definitions are the same set ncard.
- Signature consequence: a canonical unowned gate true on one graph edge is true on another distinct UNORDERED edge. The second edge is not asserted pivotal.
- Shared-copy adapter uses five pairwise-distinct selected indices, exact global equalities for two copied wires, safe prefix, pair coverage for the other three, and one selected dirty gate. Budget and strict junk decrease follow from the approved simultaneous prefix theorem.

### Independent review: full shared-side circuit exchange
- UTC: 2026-11-25T09:42:45.458136+00:00
- `shared_side_exchange_route.lean`: PASS archival partial, 2196 lines, SHA256 `c5d1d6927c0eae665b4c16a01a3f99ed95d883ea692c19da8ac906e505f85e52`. Exact shared_copy plus149lines; no axiom/native proof tactics or native escape patterns. Build3 has58 warnings/noerrors, reported exit0.
- Seven matching configurations use3/4/5-gate safe prefixes and delete three distinct ANDs plus0/1/2 globally equivalent ORs. Two source ORs are distinct because their values differ at singleton d, using c!=d and d!=e. Global shape equalities, safe intersection, two OR-source signatures, distinctness, girth and ReadsBack remain explicit. Arbitrary fan-out follows from the approved simultaneous prefix theorem. No general pattern-existence or full L1772 conclusion.
- NOTES private-value/credential-pattern scan passed. Historical build7 bv_decide claim is superseded by explicit correction and independent axiom closure below it; author asked to mark the old sentence as rejected to avoid ambiguity.

[2026-11-25 09:45:12 UTC] graph_normal_form: shared_side_exchange_route.lean GREEN/FROZEN; shared-side-exchange-build-3.log exit0, warnings only. Main sharedExchange.shared_side_repair eliminates arbitrary-fanout three-AND common-side five-literal cluster, using seven cross-matching cases and 3/4/5-gate prefixes with 0/1/2 exact OR-source copies; no larger circuit and strict junk decrease. Separately archived finite literal-cluster census in results/orch/finite: all canonical eight leaf-position partitions on at most six vertices, with singleton output/duplicate factors/absorbed output excluded, at least two output pair minterms, and mandatory valid hybrid exception edges. Twelve eligible shapes, two impossible safe girth graphs, ten remaining (five on four vertices, four on five, one on six). This is Python exploration only, not a Lean certificate or a minimal-circuit result; optional graph edges outside first returned witness matter for exchange budgets.

2026-11-25T09:49:14.005128+00:00 root: Read https://pequalnp.com/papers/note-1 (published 2026-11-24) on 2026-11-25. Its statement, "The bounds of this note are linear", describes its checked sparse graph classes. The page distinguishes restricted monotone circuit bounds from general ones. This does not prove the current ownership statement false, nor establish its status in the literature. No literature-based closure claim is made.

[2026-11-25T09:52:34.172367+00:00] counterexample: Six-literal local repair budget obstruction saved in finite/literal_six_local_budget.py, .log, and LITERAL_BUDGET_README.md. For g=(z+p)(z+q), qgate=(z+r)(a+b), j=g*qgate and forest edges za,zb,pq,ra, a single safe protector covering all graph pairs lost by deleting all3ANDs needs exactly5 new binary gates even with raw6,constants0/1,and all4OR sources free. Exhaustive semantic BFS:64 depth1,2682 depth2,94747 depth3 states; no fourth final gate; explicit5gate formula verified on all64 inputs. Computational only; does not rule out individual redirects/source reclamation/other-circuit reuse and does not refute forest theorem. Enumerated all76 girth-valid extensions of forced za,zb,pq:42 neitherra/rb,17ra,17rb. Independently checked literal census cutoff≤6 follows pair-cover dichotomy plus singleton-false safety; hybrid-edge pruning additionally requires minimum-circuit singleton-pivot premise.


2026-11-25T09:53:04.025908+00:00 repair_exchange global component analysis

No universal exchange proved. L3297 factorSubstitution handles globally orientable reader classes: a frontier opposite side implying A permits alias B for R=A AND B, and vice versa. It cannot close the local one-AND-ancestor case alone: the selected safe double-star third clause meets both A and B and implies neither; other readers can enter independent dirty chains, so global absorption and OR-merge consistency do not follow from local classification.
A shared third clause containing a graph edge ab cannot feed a safe AND with a singleton-true opposite operand, by triangle-freeness. Every blocking reuse therefore enters another nonlinear/dirty branch. Long dependencies can follow graph paths or cycles of length at least five, so graph girth does not by itself make the dependency graph acyclic. Minimum TopForm supplies a private accepted graph edge for each safe top AND, via pivotality and its OR-only output tail; overlapping top contributions and same-center star merges are possible sources of exchange budget.
Sharper geometric target: the induced graph on the two endpoints of ab and their neighborhoods is exactly a double star (private neighbor sets disjoint, independent, and without cross edges). Every lost graph edge whose influence traverses OR(a,b) is incident to a or b. A terminal sharing component could therefore be normalized by extracting two linear neighbor functions with disjoint supports. The missing theorem is a no-cost extraction/charging result preserving external OR-source fanout; arbitrary dirty-ancestor deletion does not provide this budget. A singleton hybrid z OR uv already witnesses why deleting one dirty AND can lose arbitrarily many incident-z graph edges unless alias z is retained.

### 2026-11-25 09:55:46 UTC — anchored prefix replacement (lean_setup)

GREEN/FROZEN `lemmas/prefix_anchor_route.lean`; main `...aux.prefixAnchor.prefix_replacement_anchored`. The existing prefix replacement now needs selected-to-alias domination only on graph-edge pairs where the designated selected anchor alias is false. If that prefix wire is true, a proved evaluation induction propagates it from the selected anchor through an unchanged OR-only path to the output. Explicit conditions: anchor l in selected set, all selected indices <= l, OrReaches n C C.output l. Negative-input domination, safe prefix ANDs, budget and dirty-selected premises are unchanged. Exact selected copies are still deleted by descending-index induction. This handles hybrid input aliases without requiring the prefix to cover every edge of each selected gate. Complete log `/tmp/oec/pequalnp-pilot-77/prefix-anchor-route-build-3.log`, exit 0. Frozen; separate dependent safe-anchor path derivation compiling.

### 2026-11-25 09:56:41 UTC — safe anchor has OR path to output (lean_setup)

GREEN/FROZEN `lemmas/prefix_anchor_path_route.lean`; unchanged anchored-prefix file plus `...aux.anchorPath.safe_anchor_or_path`. Every valid safe AND in a minimum Monotone2 TopForm circuit has `OrReaches n C C.output l`. A maximal OR-reachable gate is either output or has a later reader by minimality; TopForm forces that reader to be OR, contradicting maximality. This discharges the anchored-prefix path premise directly from the canonical witness. Full log `/tmp/oec/pequalnp-pilot-77/prefix-anchor-path-route-build-2.log`, exit 0. Root and geometry agent notified; frozen for review/push.


### Independent review: anchored prefix replacement

UTC: 2026-11-25T09:56:49.733755+00:00; reviewer repair_exchange. PASS archival partial. prefix_anchor_route.lean: 1707 lines, 76784 bytes, SHA256 c28ad74c6977143fe52705392a1ebf2ecbffe82448e72ba1c428ee77e02693e1. Exact approved prefix_patch_route prefix (1217 lines) and exact first342line factorSubstitution namespace prefix; new anchor code reviewed in full. Independent rebuild review-prefix-anchor-build.log exit0, inherited warnings only. Axiom-check scratch copy rebuild exit0, main depends only on propext, Classical.choice, Quot.sound (full review-prefix-anchor-axioms.log retained). Source has only Mathlib/PEqualNP.Defs imports, matching auxiliary namespaces, no prohibited source constructs/quotes/attributes/options, no sorry or native evaluation.
Scope: selected gates S are replaced by earlier prefix-wire aliases; anchor l belongs S and bounds every selected index above, so every later OR-path gate from l to original output remains unmodified. On graph-edge pairs where the anchor patch is true, unchanged OR propagation restores output independently of arbitrary fanout or other replacements. On anchor-false graph pairs, every selected replacement must preserve old true values. On all negative graph inputs, every selected replacement must imply its old value. These exact quantified premises, original ReadsBack, prefix Monotone2, and safe prefix ANDs suffice for correctness and junk control; no hidden all-input pair equality or cone isolation assumed. Deleting all alias slots pays S.card gates; B.size<=S.card yields no size increase, while S containing an original dirty AND gives strict junk decrease. This is conditional repair infrastructure, not a proof that an arbitrary unresolved bad gate admits such a prefix/anchor.


### Independent review: safe-anchor OR path

UTC: 2026-11-25T09:57:36.396196+00:00; reviewer repair_exchange. PASS archival partial. prefix_anchor_path_route.lean:1762lines,79109bytes,SHA256 88c6b7aaf64ed03712dc1b223d3ea1b2c59e5ec7fe736676e2050d8f1fc16595. Exact reviewed prefix_anchor_route prefix plus55lines. Independent scratch-copy rebuild and main axiom print exited0; only propext, Classical.choice, Quot.sound. Full review-prefix-anchor-path-axioms.log retained; inherited warnings only. Source-format scans clean.
The new safe_anchor_or_path derives rather than assumes an OR-only path from an existing safe AND to output in any minimum TopForm circuit. orReach_cone proves the syntactic reach-to-cone bridge. A maximal OR-reachable gate exists in a finite gate range; if not output, minimal_gate_has_reader supplies a strictly later effective reader. TopForm excludes AND at that reader because the safe anchor is in its strict cone, hence the reader is OR and contradicts maximality. No extra global liveness or ReadsBack hypothesis is hidden; strict later-reader semantics is proved from minimum in the existing clean prefix. No girth assumption or final ownership theorem is asserted.

[2026-11-25T09:58:25.797413+00:00] counterexample: Direct all-ownership synthesis added in finite/sat_ownership_compare.py (ordinary versus all-good, not merely presence of a bad optimum). P4controls≤3UNSAT/4SAT; C5+leaf6vertices6edgesτ3:ordinary≤7UNSAT7.9s,all-good≤7UNSAT3.5s,all-good8SAT1.2s with complete truth-table/cone verification. Thus no separation. Theta2337vertices8edgesτ4:all-good≤10UNKNOWN180s, no lower bound. New exact bitset ancestor-AND truth union encoding in sat_ownership_bitset.py disables sampleconstant pruning for all-good and retains all semantic duplicate signals; P4controls pass. Final theta120s andC5leaf7 runs pending. Documentation OWNERSHIP_COMPARE_README.md states normalization/freeconstant caveats and noLean-certificate scope.

[2026-11-25T09:59:15.229387+00:00] counterexample: All ownership-comparison artifacts now frozen. Bitset theta233≤10 returnedUNKNOWN(timeout120s), so together with explicit-cone180s this target consumed5min and proves no lower bound. Bitset C5leaf≤7 returnedUNSAT4.7s without sampleconstant pruning, agreeing with explicit-cone and unrestricted results. Full log pairs saved; reviewer notified. No running search processes remain. No all-good versus unrestricted size separation found.

2026-11-25T09:59:18.604485+00:00 ownership_route
GREEN global star-signature normalization: star_tightening_route.lean1097lines (build5 exit0, independently reviewed) defines finite total gate-truth mass, nested Nat.find minimization after minimumsize/minjunk/minbad/TopForm, and proves clamp rigidity. For j=P AND Q, if P accepts singletona and every true graph pair atj containsa, replacing P byliteral a is pointwise down, agrees onall graphpairs, preservesallowners, and keepsTopForm byminjunk; leastmass forcesgatefunction unchanged.
GREEN stronger star_operand_route.lean1859lines (build1 exit0, reviewpending) adds semantic_operand and operand_is_literal. Using the all-ones-except-a assignment, if P has anytrue inputwitha=false then Q requiresa, makingj aliasQ and contradictingminimum. OtherwiseP isexactinputa andminimalno-aliasforceswirep=a.val. Composition: clean_route670 +star_tightening body1095 +new94lines. No triangle/no-four hypotheses needed. Remainingstarbadcases: neitheroperandacceptssingletona, orliteralcenter a withQ acceptingedgeabthroughAND ancestry.

### 2026-11-25 10:04:02 UTC — bad-star route scope and obstruction (lean_setup)

The global claim that every bad AND in the nested canonical minimum has two vertex-disjoint accepted edges remains UNPROVED. Singleton-center operand tightening does not cover the case where both immediate operands reject that singleton. An accepted-edge star may then arise from an intersection of two OR supports; the OR of their common leaves need not already be a wire. Constructing it while preserving arbitrary external source reuse has no established gate-budget bound. The checked disjoint-pair cluster repairs do not bridge this remaining case.

GREEN/FROZEN concrete weak-hypothesis obstruction `lemmas/bad_star_obstruction.lean`: graph edges 01,02,13; R=(0 OR 3) AND (1 OR 2), bad gate j=0 AND R, separate edge13 and output OR. The six-gate circuit is monotone, correct, TopForm, has an owning earlier AND, and j accepts two graph edges forming a star while owning none. A four-gate correct implementation is supplied, proving it is NOT minimum. This is neither a refutation of the canonical-minimum claim nor a refutation of L-meta-1772; it shows that girth, TopForm, prior ownership, literal center, and two accepted signatures alone are insufficient. Full log `/tmp/oec/pequalnp-pilot-77/bad-star-obstruction-build-3.log`, exit 0, kernel evaluation only.

Informal narrower repair route (not additionally formalized): a literal-centered bad AND with exactly one AND ancestor R can discard its OR-only literal additions on graph pairs by badness, then absorb the factor of R that is true on the center singleton. Repointing the final gate to the other pure-OR factor removes all AND ancestors without changing external readers. This does not handle multiple AND ancestors or the both-operands-center-false case. No complete global charging or common-leaf construction argument was found.
