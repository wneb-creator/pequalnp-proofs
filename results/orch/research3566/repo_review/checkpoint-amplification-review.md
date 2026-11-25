# Independent amplification checkpoint review

Reviewer: `repo_review`; reviewed 2026-11-25. Verdict: **PASS for research preservation and candidate validation**. These are finite searches and checked upper witnesses, not a proof or refutation of L-meta-3566.

## Amplification and pendant scorers

Reviewed `evolve_amplification.py`, `evolve_combined.py`, `pendant_helpers.py`, `audit_combined_extensions.py`, and their previously reviewed dependency `reusable_helpers.py` in the gap3566 scratch directory.

The cheap helper screen is a valid optimistic bound. If O is the output cone and H_i the helper cones, the sets U_i = H_i minus (O union all other helper cones) are disjoint, and every selected helper must pay its U_i. Therefore ignoring all remaining shared costs gives an upper bound on possible profit. The implementation uses exactly this bound and never accepts a positive score without the full audit.

Pendant eligibility follows an OR-only path from the output, checks either an original input or a singleton-support operand with the required absorption inequality, and assigns distinct AND gates to distinct centers. The insertion remaps old gate indices after adding inputs and inserts exactly one OR per chosen gate. Matching on the augmented bipartite graph gives the exact cover rise. Adding leaves at every eligible center bounds the rise for every tested subset, so the early zero-rise screen is sound.

Helper profit and pendant cover rise can be combined. After pendant insertion, each old wire lies between its old value and that value OR the enlarged output. Thus an old safe helper retains its singleton support and absorption property modulo the enlarged output; adding pendant leaves preserves its graph constraints. The selected helper cones plus the inserted pendant gates realize the claimed combined charge. The scorer additionally builds the transformed circuit and re-runs the full helper audit before accepting any positive combined score. All positive acceptance paths check the actual emitted circuit's complete truth table, bipartition, absence of four-cycles, exact cover count, and gate count.

Independent lightweight replay passed all 22 combined seeds, including four with deficit 2 and cover rise 2 and four with deficit 1 and cover rise 1. Saved literal/generalized pendant controls were independently checked on all 1,024/512 assignments. The best amplification-trial circuit was independently checked on all 16,384 assignments: 14 inputs, 21 edges, cover 7, 27 gates, profit 0.

Recorded scope and results:

- Amplification trial: 180.000 s; 260,997 evaluated circuits, 114,088 valid evaluations, 43,792 distinct recorded graph keys, 16,183 complete compatible-helper subset audits, zero incomplete audits, no positive result.
- Pendant audit: 2,269 saved circuits; 118 with generalized operands; 393 with positive cover rise; no counterexample.
- Combined saved-circuit audit: those 393 cases, all valid, maximum profit 0.
- Combined scorer: the reviewed checkpoint contains seed validation only, not a completed evolutionary run.

The negative claims are limited to the circuits visited, normalized canonical helper cones considered, and pendant subsets of at most four centers. They do not establish an unrestricted circuit lower bound. Exact subset auditing does not make the evolutionary search exhaustive.

## Completed native helper sweep

The immutable input is `c8-all-safe.input`, with geometry and complete extremal rows in `c8-all-safe-metadata.json`. `large_helper_sweep.cpp` is unchanged from the previously reviewed version. The final summary and full log agree: start index 0, next index 137,233, total 137,233, found false, 419.036 s. Completed counts by helper formula cost 4, 5, 6, 7 are 10,872; 26,140; 43,996; 56,225.

This exhausts the implemented class: four specified safe C8 OR-pairs are free sources; one additional helper has minimum formula cost d in 4..7 over those sources; the residual target formula has cost at most 10−d with that helper free. The emitter shares that helper once and may share identical reconstructed functions. This is not an exhaustive search over arbitrary DAG circuits or all circuits with one shared wire. No candidate was emitted, and no Lean lower-bound claim follows from this search.

## Reproduction and source identity

The independent lightweight replay is `gap3566/repo_review/checkpoint_amplification_audit.py`; its complete stdout/stderr is `checkpoint-amplification-audit.log` in the same scratch folder. It completed with exit 0. No solver or Lean build was launched by this review.

Additional observed-helper SAT review passed for `gadget_sat.py` SHA-256 `f2b461c3b147b6776653b9b4af10835c2a7b7fad4290e34b62a2897587c6ccce`. The new mode forces observed OR-support sinks, protects their subset nodes to exact OR-only decompositions, and charges every selected noninput node plus the final term count. Thus actual emitted gates are at most the SAT budget minus one. Geometry checks enforce a common bipartition, no old shared neighbor inside a support, and pairwise support intersections at most one. Every SAT model checks the graph output and each helper on all old-input assignments. Independent checks confirmed the subdivided K3,3 geometry (15 inputs, 18 edges, minimum cover 6, eight triples, overhead 16), so improving raw/paid limits are 38/22. A P5 observed-helper control was independently amplified and checked on all 128 new-input assignments; it has 7 edges, cover 3, and 9 gates, hence no improvement. Complete check output is `observed-helper-mode-audit.log` in the review scratch folder. Solver negatives in this mode remain limited to the supplied finite recipe library.

The `free_pair_synth.py` overlap change and `amplify_pairs.py` constructor also passed source review. Same-side pairs with disjoint old neighborhoods can overlap in one vertex. Original-input essentiality still holds by setting one neighbor and every helper partner of the tested input to true; toggling that input changes the graph output while all helper sources stay fixed. The optional AND-count threshold recurrence is correct. The amplifier retains only used helper cones, remaps gates after adding fresh inputs, and checks the actual extended graph, matching, and complete truth table. Its `vertex_cover=left` metadata describes a valid bipartition cover, which need not be minimum; its `expected_lower` correctly uses maximum matching cardinality.

SHA-256:

- `evolve_amplification.py`: `c3bafed15a4208dc52112b23f2975b56bb8081dcec97172ff4d2e32b065a6c05`
- `evolve_combined.py`: `ec018274a4d75eee72dca86a8260fa255f5a8c33fc6daa65908abe1f1512a93c`
- `pendant_helpers.py`: `db0afe34bc43e2eb1fca196bf64e4ce1f18ded69ba49b23ab90413487297e325`
- `reusable_helpers.py`: `093cf1a173360aa38b62957c200e7243a06b2476dcea94bd3f12496dbc9bbe9a`
- `audit_combined_extensions.py`: `efd7fe3dabb9ba8100005bdb62efbf6a782ab7b1f24033b8a06be8cb00de06a7`
- `large_helper_sweep.cpp`: `61f1cb524d1d6bdc61a8f88df620a9e854eb79702501440ba7bb7126690af47d`
- `c8-large-helper-summary.json`: `3382c826886f982b16ad85ac304e20be343b95df328207ab613798d492bd7af2`
- `c8-large-helper-sweep.log`: `66c01b6557c0e4e2f9734267ca140e373d829953d2a938cb2b26f42ff7c29a52`
