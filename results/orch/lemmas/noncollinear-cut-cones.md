# Noncollinear fixed-star cone family

2026-11-25 UTC. Constructive, following root's complementary Fano-orbit proposal. Prepared data and checked embeddings only; no solver was started here.

Fix the three left stars at vertices {0,1,2}, a noncollinear Fano triple. Each star uses two OR gates and one AND, and two further ORs form their union: 11 fixed gates. The residual four-star graph H has left vertices {3,4,5,6}, all seven right vertices, and 12 edges. A 14-gate cone for H, followed by one final OR with the fixed union, would give 26 gates.

The residual variable order is `[3,4,5,6,7,8,9,10,11,12,13]`. All seven right variables occur in H, so both the first two-neighbor sum and the full three-neighbor sum of each fixed star remain useful cut candidates. There are 17 correlated signals: 11 original residual variables, then the six OR cuts in star order 0,1,2, with pair sum followed by full sum for each star. The fixed cut wires are `[14,15,17,18,20,21]`; the fixed union is wire 24. Cone internal index 17+j maps to full wire 25+j.

Each fixed star has three choices of its first pair sum. The 27 combinations split into seven orbits under the S3 stabilizer of {0,1,2}. A choice records which neighbor is excluded from the first pair: -1 means that star's unique external neighbor, and j means the shared line with fixed vertex j. The seven lexicographic representatives and orbit sizes are:

| Variant | Excluded-neighbor choices | Orbit size |
|---|---|---:|
| 0 | (-1,-1,-1) | 1 |
| 1 | (-1,-1,0) | 6 |
| 2 | (-1,0,0) | 3 |
| 3 | (-1,0,1) | 6 |
| 4 | (-1,2,1) | 3 |
| 5 | (1,0,0) | 6 |
| 6 | (1,2,0) | 2 |

The generator explicitly extends all six stabilizer permutations to the 14 Heawood vertices and verifies edge preservation. It verifies the action on the pair/full cut supports, and checks each representative's cut-signal stabilizer on all 2,048 residual assignments. The orbit sizes sum to 27; this is a complete classification of pair choices for this fixed triple, not a claim about all monotone circuits.

Every variant has the same complete monotone boundary basis: 12 positive edge rows and 15 maximal-independent negative rows, totaling 27 assignments. Cut columns differ across variants. Coverage of every residual assignment by the appropriate positive or negative extremum was checked directly.

The ordinary 15-gate cone and four 14-gate near-seeds are provided. The near-seeds omit original edges (3,7), (3,11), (3,12), or (5,9), representing the four edge orbits under the fixed-triple stabilizer. All four were checked against the corresponding edge-deleted residual graph on all 2,048 assignments. For each of the seven cut variants, the baseline embedding was checked against the full Heawood target on all 16,384 inputs; the embedded (3,7)-missing seed was checked against the full target with that edge removed and has 47 false negatives. No seed is an exact witness.

Stable files under `/tmp/oec/pequalnp-pilot-70/constructive/`:

* `noncollinear_cut_cones.py`
* `noncollinear-cut-cone-variant-0.json` through `noncollinear-cut-cone-variant-6.json`
* `noncollinear-cut-cone-symmetries.json`
* `noncollinear-cut-cone-baseline15.json`
* `noncollinear-cut-cone-seed14-missing-3-7.json`
* `noncollinear-cut-cone-seed14-missing-3-11.json`
* `noncollinear-cut-cone-seed14-missing-3-12.json`
* `noncollinear-cut-cone-seed14-missing-5-9.json`

Reproduce with `python3 noncollinear_cut_cones.py --output-dir <the scratch directory>`. The script uses only the Python standard library and completes in about two seconds in the current environment. The SAT search and any resulting model validation belong to circuit_search.
