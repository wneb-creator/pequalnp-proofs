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
