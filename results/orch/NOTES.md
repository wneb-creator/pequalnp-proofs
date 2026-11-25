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
