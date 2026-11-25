# K4 incidence cone with free matching sums

2026-11-25 UTC. Constructive, coordinated with circuit_search. Root prioritized this as the next short SAT strategy. Constructive prepared the target, correlated rows, seed, and full embedding validator; no solver was started here.

## Exact sufficient construction

Keep the three Heawood left stars at vertices 1, 2, and 4 fixed. Their neighborhoods are respectively {7,9,13}, {8,12,13}, and {10,11,13}. Each costs two ORs and one AND; two further ORs combine the stars. This fixed part costs 11 gates and supplies three intermediate sums for free:

`S1 = x7 OR x9`, `S2 = x8 OR x12`, `S3 = x10 OR x11`.

The remaining four left stars form H, the incidence graph of the four K4 vertices {0,3,5,6} and their six pairs. A circuit for H with at most 14 additional gates, allowed to use the three free sums as cut inputs, gives a full Heawood circuit with at most `11 + 14 + 1 = 26` gates. The last gate ORs the fixed part with H.

This differs from the earlier standalone induced-subgraph search: the cone receives three correlated OR signals computed by the fixed stars. They are the three pairs of opposite K4 edges. A standalone search charging their construction would miss this sharing opportunity.

## Dominance normalization and boundary rows

Initially the contextual cone could use all original inputs and all fixed intermediate wires. The four outside variables {1,2,4,13} are zero on every residual minimal-true edge row. Setting them to zero inside a monotone cone preserves those positives and can only remove false positives. Consequently the fixed sums `x13 OR Sj` reduce to Sj, and the completed fixed AND/union outputs reduce to false. This dominance normalization was independently reached by circuit_search and constructive.

After normalization the cone must compute H exactly: extending a residual assignment with all outside variables false makes the fixed part false. Thus the SAT target has ten independent original variables and three correlated cut sums, with only 12 minimal-true edge rows and 12 maximal-independent negative rows. Although there are 13 cut signals, the boundary justification is monotonicity in the ten original variables, not treating the sums as independent.

The local original-variable order is `[0,3,5,6,7,8,9,10,11,12]`. Cut signals 10, 11, and 12 are ORs of local pairs `(4,6)`, `(5,9)`, and `(7,8)` respectively. The SAT decoder must evaluate all 1,024 original assignments with these correlations, then validate the full 14-input embedding on all 16,384 assignments.

## Embedding and validation

The fixed three-star blocks are consecutive, so their sum wires are 14, 17, and 20, and the fixed union output is wire 24. Cone inputs 0 through 9 map to the original variables above; cone inputs 10 through 12 map to those three fixed sum wires. Cone internal wire 13+j maps to full-circuit wire 25+j. A 14-gate cone is followed by the final OR at wire 39.

The script checked the ordinary 15-gate cone against all 1,024 residual assignments and its 27-gate embedding against all 16,384 full assignments. Both are exact. A 14-gate near-seed omits local edge (0,4), corresponding to original edge (0,7). It has 13 residual false negatives and its 26-gate embedding has 47 full false negatives; all other behavior equals the target with that one edge removed. It is not a witness.

An initial off-by-one in a fixed-star AND input was caught by the full-table assertion and corrected before the artifacts were written. The final successful validation reported 12 positive rows, 12 negative rows, 13 cut signals, and the error counts above.

## Stable artifacts

Under `/tmp/oec/pequalnp-pilot-70/constructive/`:

* `matching_cut_cone.py`
* `matching-cut-cone-rows.json`
* `matching-cut-cone-automorphisms.json`
* `matching-cut-cone-baseline15.json`
* `matching-cut-cone-seed14.json`
* `matching-cut-cone-seed26-embedded.json`

Reproduce with `python3 matching_cut_cone.py --output-dir <the scratch directory>`. The script uses only the Python standard library and completes in under one second in the current environment. No 14-gate exact cone has been found yet.

The optional symmetry artifact lists all 24 K4 permutations induced on the 13 cut signals. Every action was checked on all 1,024 original assignments, including the cut identities and target invariance. There are nine distinct-operand first-pair orbits. The separate `all_first_pair_representatives` field also includes the three repeated-pair representatives (0,0), (4,4), and (10,10), so an encoder need not assume a minimal noncopy first gate. The initial reviewed solver encoding used no such symmetry restriction.
