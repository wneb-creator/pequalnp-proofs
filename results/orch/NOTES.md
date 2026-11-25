# pequalnp-pilot-154 — L-meta-4970

Only parent holds/renews lease and changes final Lean file. Each agent appends timestamped findings here and writes only its assigned candidate.

Exact statement: /tmp/oec/pequalnp-pilot-154/statement.txt
Allowed project imports: PEqualNP.Defs only. Reductions are not open.

Toolchain PATH prefix: /tmp/oec/pequalnp-pilot-154/lean-4.36.0-linux/bin
Checker also needs PEQUALNP_REAL_LAKE pointing to that lake, and PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-154/pnp-state.

No sorry, new axioms, native_decide, altered statement, or unlisted project imports. Helpers must use final module namespace. Notify parent immediately when a meaningful Lean component compiles so it can be reviewed and pushed.

## 2026-11-25T15:42:26.281361+00:00 — checker_review semantic and delivery audit

- Desk L-meta-4970 is proof kind (row kind omitted means check); lease reductions_open=false. No reduction submission is available. A negation would compile locally in refute mode but is not an ordinary accepted submission for this proof-kind row.
- Star-OR witnesses are existential anywhere in C. They need not feed the output, be ANDed with their claimed center, or be used at all. Their equality is semantic, so their internal cone may contain AND gates.
- T=0 prohibits syntactically mixed OR-reach; reach stops at every AND. It does not directly prohibit an OR whose semantic function depends on both colors.
- IsAO2 ensures exactly two operands, AND/OR only, and ReadsBack; duplicate operands are allowed. C.size counts every gate; C.output can name any wire or a nonexistent wire. No minimality or TopForm hypothesis is present.
- Final source needs only allowed project import PEqualNP.Defs, helpers inside PEqualNP.Outside.L_meta_4970 (or its _aux namespace), fully qualified target theorem at top level and last. The exact statement is fixed in scratch statement.txt.
- Guard invocation: node .github/scripts/outside-guard.mjs imports <source> <imports.json> lean/PEqualNP/Outside/L_meta_4970.lean check. Then lake build and tools/check-lean.mjs with exact statement.txt, kind check.

- 2026-11-25T15:42:54.053009+00:00 counterexample: IsAO2 prevents missing-wire/constant/fan-in loopholes. E=empty is trivial, and one-edge E cannot satisfy a cardinality>=2 star witness. First nontrivial examples K1,2 and C6 meet the proposed bound with 2 and 8 gates. Semantic star witnesses can be unused, so the sketch’s direct reader argument needs repair. Investigating random small circuits under exact truth-table checks.

## Ledger 2026-11-25T15:43:19.987137+00:00

Compiled results/orch/lemmas/ledger.lean successfully with only Mathlib.Data.Finset.Card. Three lemmas: star_centre_unique (>=2 common leaves force equal centres), distinct_centres_intersection_card (leaf supports at different centres overlap in at most one leaf), or_function_determines_leaves (semantic equality of pure OR functions forces equal supports). Build log: /tmp/oec/pequalnp-pilot-154/ledger-build-1.log. Full gate-count connection remains unresolved: witness OR gates may be unused and no associated AND gates are hypothesized.

- 2026-11-25T15:44:18.078402+00:00 counterexample: CHECKED `star_centre_unique` and `reverse_star_centre_unique` in results/orch/lemmas/counterexample.lean, using only Mathlib.Data.Finset.Card. Both deduce equal centres from a common >=2-leaf set under the exact no-C4 hypothesis. Lean exited 0; log at /tmp/oec/pequalnp-pilot-154/counterexample/centre-unique-build.log. Parent notified for immediate independent review and push.

## Lemma search — 2026-11-25 15:47 UTC

Only exact tCount occurrence in Outside is L_meta_4791 (T=0 conversion at factor six). Existing reusable engines: L_meta_7241 lines391–840 has countUnion/dag_union_bound, cover_half and edge_finset_gate_bound; its full theorem assumes all AND gates reject nonedge pairs. L_meta_4897 gives exact bipartite bound with IsReadK=1, L_meta_3706 gives a doubly-read-edge penalty, L_meta_4183 and L_meta_1491 give top-form ledgers with Ustar penalty. None directly closes this gap. The listed numeric neighbors 4962/4964 are unrelated finite graph certificates; 4968 builds appended DNF; 4972 is a union/switch pruning lemma.

- 2026-11-25T15:45:43.878185+00:00 structural_proof: checked abstract monotone AND bypass for pure-OR targets; candidate structural.lean compiles, 75 lines. If f∧g≤OR(Q), one operand≤OR(Q), via maximal assignment outside Q. If f∧g=OR(Q), one operand=OR(Q). Working toward simultaneous pure-star OR gate count.

## Lemma search compiled component — 2026-11-25T15:47:03.428976+00:00

`results/orch/lemmas/library_route.lean` compiles with pinned Lean (exit 0): row_centres_unique, column_centres_unique, or_support_injective. These are generic C4-free centre uniqueness and OR support extensionality facts, helpers in final namespace. Log: /tmp/oec/pequalnp-pilot-154/library-route-build.log.

Further search: L_meta_1006 refutes generic C4-free AND-count >= cover using a nonbipartite 11-vertex graph, 6 AND gates, cover >=7. L_meta_217 and L_meta_2399 prove that count only for t<=5. L_meta_7653 proves |accepted edges|+|accepted matching|<=size+1 for OR-block then AND-block shape.
