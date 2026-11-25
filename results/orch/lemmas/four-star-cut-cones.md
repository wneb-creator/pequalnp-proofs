# Ten-gate cone after fixing four stars

2026-11-25 UTC. Constructive, authorized by root for preparation and a separately reviewed short solver probe. No solver was started here.

Fix the left stars at {0,3,5,6}. Four three-gate stars and three union gates cost 15. The residual graph consists of the three collinear left stars at {1,2,4}, with nine edges and variable order `[1,2,4,7,8,9,10,11,12,13]`. A ten-gate residual cone followed by one final OR would give 26 gates. It receives eight free OR cuts, the pair and full neighbor sum from each fixed star, for 18 correlated signals in total.

The exact monotone basis is nine positive edge rows and eight maximal-independent negative rows. Every one of the 1,024 residual assignments was checked against these extrema. The fixed cut wires are `[14,15,17,18,20,21,23,24]`, fixed union output is 28, and cone internal wire 18+j maps to full wire 29+j.

The fixed stars are K4 vertices. Choosing the first OR pair amounts to excluding one of the three incident K4 edges, so a choice is a function from four vertices to distinct neighboring vertices. The 81 choices split into six S4 orbits:

| Variant | Excluded neighbors | Orbit size | Stabilizer size |
|---|---|---:|---:|
| 0 | (1,0,0,0) | 12 | 2 |
| 1 | (1,0,0,1) | 12 | 2 |
| 2 | (1,0,0,2) | 24 | 1 |
| 3 | (1,0,3,2) | 3 | 8 |
| 4 | (1,2,0,0) | 24 | 1 |
| 5 | (1,2,3,0) | 6 | 4 |

The generator verifies the full Heawood automorphisms extending S4, all cut-support transformations, and every representative's stabilizer on all 1,024 residual assignments. Variant 3 is the two-disjoint-2-cycles choice and has the largest stabilizer; prioritizing it is only a search heuristic.

The ordinary 11-gate residual baseline embeds to the exact 27-gate target. Two ten-gate seeds omit original edge (1,7) or (1,13), the private-neighbor and common-neighbor cases. Their residual functions were checked exhaustively. For each of the six variants, the complete baseline and the (1,7)-missing seed were checked on all 16,384 full inputs; the seed has exactly 47 false negatives and no other errors. No seed is a witness.

Stable artifacts under `/tmp/oec/pequalnp-pilot-70/constructive/`:

* `four_star_cut_cones.py`
* `four-star-cut-cone-variant-0.json` through `four-star-cut-cone-variant-5.json`
* `four-star-cut-cone-symmetries.json`
* `four-star-cut-cone-baseline11.json`
* `four-star-cut-cone-seed10-missing-1-7.json`
* `four-star-cut-cone-seed10-missing-1-13.json`

Reproduce with `python3 four_star_cut_cones.py --output-dir <the scratch directory>`. Only Python's standard library is used; the complete preparation and exhaustive validation took about four seconds in the current environment. This is a restricted sufficient family, not an optimality result for arbitrary circuits.
