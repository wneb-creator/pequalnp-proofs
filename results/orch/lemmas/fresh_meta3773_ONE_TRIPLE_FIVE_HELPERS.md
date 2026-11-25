# Five-helper strata in the one-triple five-point patch

The model fixes the reduced five-point graph and the seven outside OR features described in `fresh_meta3773_ONE_TRIPLE_HIGH_HELPERS.md`. Five actually used helpers leave an excess read budget of three. Four helper-set orbits remain under the twelve automorphisms of the representative point set `{0,1,2,3,6}`. Mask bits follow the feature order in `fresh-meta3773-five-point-types.json`.

Each table entry gives completed primitive-multiset representatives over the total in that stratum. The columns count extra primitive occurrences. The remaining excess is available for repeated internal gates.

| Helper mask | 0 | 1 | 2 | 3 |
| --- | ---: | ---: | ---: | ---: |
| 31 | 0/1 | 1/9 | 26/64 | 360/360 |
| 47 | 0/1 | 0/13 | 35/106 | 650/650 |
| 55 | 0/1 | 0/12 | 22/99 | 616/616 |
| 62 | 1/1 | 11/11 | 94/94 | 594/594 |

The search completed 2410 of 2632 representatives, across 7 fully completed strata. It completed every stratum for helper mask 62. No completed representative produced a 20-gate reduced circuit. Unfinished prefixes and untouched strata are inconclusive. The table concerns only five-helper replacements of the selected point stars. It supplies a computational diagnostic with no Lean certificate or bound on arbitrary circuits.

`fresh_meta3773_five_helper_summary.py` constructs the automorphisms directly from the line neighborhoods and helper supports and counts multisets under each installed-helper stabilizer. It verifies every completed ordinal against the full stdout/stderr chunk logs. The progress files count completed representatives only. A cone checkpoint inside the next representative records which earlier cones have been visited. The last stored cone is replayed when the search resumes.

The final optimized recurrence retains minimal positive and maximal negative row patterns on the available primitive multiset. Monotonicity implies the discarded obligations. Among duplicate patterns it retains the lowest row index. It also drops tokens always zero on the retained positive rows or always one on the retained negative rows: assigning those tokens their indicated constants preserves every required acceptance or rejection before simplifying the formula. It uses the earlier component splitter up to sixteen components and the earlier multiset recurrence outside that range. The code is independently reviewed, and the 56 direct comparisons, the generated 13–19-token positive controls and the 19-token ordinary star control pass. The preceding 12-component solver remains a way to reproduce each result.

The optional checkpoint wrapper records only complete failed suffixes having at least one unit of internal excess. Each length-prefixed binary record gives the full ordered tuple of primitive truth tables, the raw-vertex mask, sorted possible carrier slots and remaining internal excess. Records use explicit little-endian fixed field widths. The wrapper reuses an exact key only, ignores and truncates an interrupted trailing record, and excludes root states from this cache. The cache inventory validates every complete serialized key and binds each file hash. The cache keys belong to these exact archived row and model conventions. The original checkpoint wrapper and its short-write-checked revision are both preserved. The inventory verifies that the fixed model data hash is `54d3b8cf7a11e73b8e48f37f18952e026c5375475337e9c83ad3bdaaaa4c0d10`. These cache files improve interrupted runs. Starting with empty caches or using the preceding non-checkpointed solver reproduces the same model.

For a fresh run, use the previously archived model inputs and sources from the high-helper packet. Compile `fresh_meta3773_readonce_wide.cpp` and `fresh_meta3773_component_sixteen.cpp` together into `fresh-meta3773-sixteen.so` with `g++ -std=c++17 -O3 -shared -fPIC`. The previously described `fresh-meta3773-readonce-ext.so` is also required. Run `python fresh_meta3773_five_sixteen.py 1 mask dup`, choosing a mask and column from the table. Substitute `fresh_meta3773_five_checkpoint.py` to record complete failed suffix states for reuse following interruptions.
