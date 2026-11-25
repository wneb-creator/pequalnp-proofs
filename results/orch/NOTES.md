# Pilot 152: L-meta-4970

Lease held only by root. Assignment received 2026-11-25T15:40:22Z. Reductions closed.

Exact desk assignment: /tmp/oec/pequalnp-pilot-152/assigned-gap.json
Statement: /tmp/oec/pequalnp-pilot-152/statement.txt
Lean environment: source /tmp/oec/pequalnp-pilot-152/toolchain-env.sh
Use narrow imports, initially PEqualNP.Defs. Fetch targeted prebuilt cache before missing Mathlib dependencies. No Mathlib source builds.

Every agent owns its named lemma file and appends timestamped findings here; root owns final L_meta_4970.lean. No agent calls desk, commits, or pushes. Notify root immediately of any compiling result.

Strategies and findings follow.

2026-11-25T15:43:02.227627+00:00 status_review: Only tCount precedent is L_meta_4791; useful OR reach/orIn propagation toolkit at lines626–737. No stronger lower bound found. Detailed notes in lemmas/library-search.md. Independently reviewed root empty_edges partial: preservation-only approved after compilation; no posted theorem yet.

2026-11-25T15:43:26.523848+00:00 [stars] Compiled results/orch/lemmas/stars.lean: left_star_unique and right_star_unique prove a leaf set of size at least two has a unique center under posted C4-free condition; left_star_inter_card_le_one gives intersection at most one for distinct centers. ownership_cover turns any endpoint-assignment into a vertex cover. ownership_ledger gives the exact finite-fiber identity sum (fiber.card - 1) + image.card = E.card. All helpers use only PEqualNP.Defs, no sorry or added axioms. Build via lake --dir lean env lean results/orch/lemmas/stars.lean passed with empty output. Root notified immediately for push-early.

## Counterexample audit 2026-11-25T15:44:13.104168+00:00

IsAO2 rules out malformed forward reads/fan-in issues. No edge/zero-side defect found. Semantic star witness OR-reach can be empty: b0 OR b1, duplicate AND of that wire, then duplicate OR; this computes OR{b0,b1} but final orIn is empty. Both proof agents informed. Small exhaustive semantic-state search ran p=q=2 through 3 gates and p=2,q=3 through 4 gates; see scratch counterexample-small-search.log and .py. No counterexample found.

2026-11-25T15:44:13.990357+00:00 [stars] Second compiled version adds semantic injectivity of left/right OR leaf sets, opposite-color OR-function distinction for nonempty leaves, and same_right_or_center_unique. These show a nontrivial star OR gate can serve only one center and one color. No extra imports. Root and ledger agent notified.

2026-11-25T15:44:31.362581+00:00 status_review: Useful ledger precedents found in L_meta_8933 gate_budget323–415 and L_meta_2235 s2233(output OR count), s2234(star leaf OR count). They need extra cleanliness/read-once hypotheses. T0 does NOT force semantic monochromatic singletonSupport: duplicate singleton AND wrappers hide OR reach. Details in library-search.md.

## Ledger route — 2026-11-25T15:45:05.471775+00:00

Compiled `lemmas/ledger.lean`: `no_two_colour_of_zero` and `or_reach_monochrome` establish syntactic OR-reach monochromaticity from T=0.

Main remaining obstacle: arbitrary circuit AND gates can have singleton support and can be dirty; star OR witnesses may be unused or have ANDs in their cone. Existing L_meta_8933 gate_budget needs reachable AND singleton support empty and pair-safety, so not directly applicable. L_meta_2235 s2233 counts AND gates in output OR closure versus output OR count; s2234 gives disjoint leaf OR accounting. Semantic agent is adapting L_meta_529 to OR-only star charge. Distinct witness components at the same center must be counted separately unless a stronger gate realizes their union.

## 2026-11-25T15:45:05.890914+00:00 Semantic strategy

Adapted L_meta_529 to count only OR gates. File results/orch/lemmas/semantic.lean proves `Semantic.or_outputs_bound`: for pairwise intersections at most one, monotone fan-in-two multi-output pure OR computation requires sum_i (|S_i|-1) OR gates. `Semantic.main_inv` gives per-family charge set D(Q): gate is OR, false on complement-of-Q assignment, and true on two distinct singleton inputs. Such charge gates are disjoint for distinct-center stars and disjoint from all gates below the final edge function (those have no true singletons). AND cannot merge the singleton classes. No reliance on syntactic OR reach.

2026-11-25T15:46:33.453922+00:00 status_review: Independently reviewed revised stars, ledger, all341 lines semantic, and audit counterexample. Approved partial preservation after reported compilation; audit is not gap refutation. Pure OR semantic charges robust through AND wrappers. Main residual circuit ledger still needed.
