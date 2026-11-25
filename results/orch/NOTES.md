# Pilot 176: L-meta-5012

Goal: first-rung universal no-one-junk assumption implies universal no-two-junk conclusion for least fan-in-two AND/OR circuits of bipartite C4-free edge functions.

Only root holds the desk lease. Helpers must live in namespace PEqualNP.Outside.L_meta_5012 or its _aux namespace. No sorry, axioms, native_decide, strings, or forbidden commands in delivered Lean. Exact statement: /tmp/oec/pequalnp-pilot-176/statement.txt.

Append strategy findings with UTC timestamps here. Each agent owns separate lemma files under results/orch/lemmas; tell root immediately when any file compiles. Do not mutate the final Lean target or git state.

- 2026-11-25T18:58:46.674303+00:00 antecedent_search: upstream L_meta_3760 and L_meta_8725 already prove universal no-one-junk, so vacuity route abandoned. Running exact truth-table Z3 circuit synthesis for C6, 8 gates, exactly two junk ANDs. Uses system libz3 via ctypes; no external install.

- 2026-11-25T18:59:16.279279+00:00 [restriction] Upstream L_meta_3760 and L_meta_8725 already prove exact first-rung antecedent. L_meta_1501 normalizes to TopForm preserving size and junk cardinality. Restricting inputs preserves graph class and function shape, but leastness does not automatically survive; no valid splice argument found yet.

- 2026-11-25T18:59:24.373178+00:00: structural inventory: exact first-rung antecedent is already proved in Outside/L_meta_3760.lean (10039 lines); target 5012 still needs second-rung argument. L_meta_1501 normalizes to TopForm preserving leastness, size, and junk.card (1123 lines). L_meta_5391 gives nested direct-reader two-junk erasure with size budget controlled by residual edge count; L_meta_5412 rules out two double-star rectangle junk gates at a lift fixed point. None may be imported under current target imports, but helpers can be copied with namespace changes.

- 2026-11-25T19:01:34.459452+00:00 antecedent_search: two-junk SAT searches UNSAT for P4 at4 gates, P5 at5 gates, C6 at8 gates, and all six other nonisolated 3+3 C4-free bipartite graph isomorphism types at the star-cover bound m+τ−1 (gate sizes5,6,5,6,7,7). Encoding uses exact complete truth tables and safe minimum-circuit normalizations: distinct gate functions, no gate equal to input, every gate used, commutative operand order, independent adjacent gate order. P4 zero-junk at4 gates SAT control. These are computational evidence, not Lean proofs.

- 2026-11-25T19:01:51.476898+00:00 [restriction] Naive leastness transfer is false: P4 function ab OR bc OR cd has least 4-gate circuit b(a OR c) OR cd. Zero a and simplify constants gives bc OR cd (3 gates), but c(b OR d) needs 2. Exhaustive distinct-function AO enumeration through 3 gates on 4 inputs found no P4 realization (12/114/988 states); 4-gate witness verified. Script and full stdout/stderr in scratch restriction_nonleast.*. Drafted graph-class preservation, zero-extension semantics, edge-pair completeness, and matching-lift-cost leastness lemmas in results/orch/lemmas/restriction_graph.lean; not compiled yet.

## Inventory 2026-11-25T19:02:24.630226+00:00

- Scanned all 201 Outside files mentioning junk/IsLeastAO/IsDirtyAnd. No final theorem excludes exactly two junk gates in general. First rung already proved by L_meta_3760 and L_meta_8725.
- L_meta_5412 excludes two double-star-product junk gates under IsLiftFixedPoint; self-contained 448,991 bytes. Other two-junk statements either bounds residual Ustar or specialize an 11-vertex non-bipartite graph. No existing flag classification theorem found.
- Draft bridge results/orch/lemmas/inventory_lift_bridge.lean (329 lines, 15,010 bytes): IsAO2 + computes graphFun + TopForm implies IsLiftFixedPoint. New semantic proof finds a clean AND below any implicant wire, then TopForm forces OR propagation to output. Not compiled yet; waiting for Defs.olean. L1501 TopForm normalization preserves size and junk cardinality, so this supplies the fixedpoint hypothesis if valid.

## Toolchain bootstrap 2026-11-25T19:04:21.283760+00:00

Lean 4.36.0 installed at /tmp/oec/pequalnp-pilot-176/toolchain/lean-4.36.0-linux/bin. Source /tmp/oec/pequalnp-pilot-176/lean-env.sh. Pinned Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842 and all manifest dependencies fetched; selective cache for 67 external roots (2480 artifacts) completed. Verification with lake --no-build build of those roots passed: All targets up-to-date (4974 jobs). Then lake build PEqualNP.Defs passed, building 86 project modules and no Mathlib source.

Checker storage issue: CheckLemma.lean imports full Mathlib at runtime, so a lone umbrella artifact is insufficient. Current overlay is 7.9 GiB total; toolchain 3.1 GiB and selective cache 2.5 GiB leave about 800 MiB. Lean module imports require .olean.server and .olean.private; do not trim these. Full logs are in job scratch.
