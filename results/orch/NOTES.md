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
