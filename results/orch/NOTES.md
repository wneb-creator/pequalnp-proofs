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
