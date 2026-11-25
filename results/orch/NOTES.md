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

## Ledger 2026-11-25T15:48:05.977538+00:00

Eight helper lemmas compile (ledger-build-4.log empty, exit 0). Added same-side finite-OR support uniqueness, impossibility of nonempty point OR = line OR, and star_family_cover_card / star_family_ledger. The latter extracts a vertex cover S from any finite edge-covering star family indexed by I: |S| <= |I|, |E| <= sum_i |B_i|, and final desired graph bound follows from sum_i |B_i| + |I| <= circuit size + 1. Multiple disjoint witness supports at one centre require retaining their root/component count, not replacing it by one.

- 2026-11-25T15:48:37.940564+00:00 structural_proof: checked pure_or_root_count (245 lines total structural candidate). For any monotone binary AND/OR DAG with singleton-support small on inputs, roots all semantically below OR(Q), total union of root singleton supports has cardinal <= number of roots + number of OR gates below OR(Q) with singleton-support cardinal >1. Correctly handles arbitrary AND intersections via maximal-complement bypass. Snapshot structural-checked-2.lean, clean compile log structural-count-build.log.

## Ledger 2026-11-25T15:49:28.493056+00:00

Published checked checkpoint with 11 lemmas (ledger-build-5.log, exit 0). Added star_line_centre_unique and point_centre_unique_of_same_function / line_centre_unique_of_same_function, so same semantic star-OR function cannot be assigned distinct centres. Candidate is stable; further development stays in scratch until checked.

- 2026-11-25T15:49:39.666273+00:00 counterexample: Random search completed 6,462,553 valid T=0 AND/OR circuits (6/8/10 inputs, 360 s). It found 534,496 C4-free quadratic outputs, covering 9,351 distinct labeled graphs, and no gate count below |E|+matching−1 after pruning unused gates. Every candidate function was checked by its complete truth table. This is randomized evidence only and does not prove the general statement. Full script/log: /tmp/oec/pequalnp-pilot-154/counterexample/random_search.py and random-search.log.

- Counterexample audit: L_meta_1006 only verifies a six-AND circuit on maximal independent sets and their one-vertex extensions, not on every input; it does not directly refute the AND-count lower bound for an exact edge function. Its graph also has triangles and a pentagon, hence is not bipartite.

- 2026-11-25T15:50:05.300107+00:00 counterexample: C6 seven-gate T=0 MILP search reached its 120-second limit with no feasible solution and no infeasibility proof (2,993 nodes). A fixed eight-gate positive control passed the same encoding with all constraints satisfied. Treat seven-gate feasibility as UNVERIFIED, not disproved. Logs: counterexample/milp-search.log and milp-control.log under task scratch. Counterexample strategy has produced no refutation; ready for reassignment.

## Abstract output-pruning engine — 2026-11-25T15:50:12.800153+00:00

`results/orch/lemmas/library_route.lean` now has only substantive pruning helpers in namespace PEqualNP.Outside.L_meta_4970.Pruning; duplicate centre facts removed. Pinned Lean compilation passed, exit 0, log /tmp/oec/pequalnp-pilot-154/library-pruning-build.log. `selected_dag_cover` handles arbitrary bipartite endpoint embeddings: input supports size<=1, selected-child gates, paid binary-union gates, dead gates. Accepted graph edges induce a vertex cover support(root), with cardinal <=1+(range total intersect paid). For parent retained-subDAG application, use empty support and false hit at inactive wires, and put active OR gates in paid.

Canonical simultaneous choice tools found in L_meta_3765 and L_meta_6015; latter canon_sub gives a single selector assignment simultaneously respecting any target support bound available under some assignment.

## Ledger 2026-11-25T15:50:54.695788+00:00

Published checked checkpoint with 12 lemmas (ledger-build-6.log, exit 0). New exists_private_edge_subfamily: from any finite star/edge family covering E, selects a subfamily J still covering E such that each selected index has a private edge e in E belonging to its set and no other selected set. Proof chooses minimum cardinality with Nat.find and deletes redundant members. This may support careful root selection; it does not prove any circuit AND count.
