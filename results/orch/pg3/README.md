# PG(2,3) search for L-meta-2583

No counterexample was found. These heuristic nonfindings are not UNSAT results or circuit lower bounds. All active searches were terminated when the root agent reported confirmed lease loss (HTTP410); no further proof search was performed.

## Exact instance and tests

The incidence is p in {l,l+1,l+3,l+9} mod13. `generate.py` independently checked 13 points, 13 lines, degree4,52 edges and unique point-pair lines. It enumerates all8192 point subsets to obtain every maximal independent set:704 sets, with size census6:52,7:468,8:156,10:26,13:2. The52 minimal true inputs plus704 maximal false inputs form756 decisive tests for monotone circuits.

`tests-triples.txt` adds all1092 three-variable assignments containing an incidence edge, giving1144 positive and704 negative tests. Those extra positives only improve a heuristic gradient; the original756 tests already decide correctness for AND/OR circuits.

## Programs and checks

- `search.cpp`:63-gate full-circuit heuristic; modes0 annealing,1 neutral drift,2 multi-gate moves. Randomized64-gate point/line star circuits are checked in100 baseline trials before deleting one gate to seed search.
- `weighted.cpp`:same search, but missed minimal positives cost8 and false positives cost1. Its best weighted score8 was still a missed edge.
- `triples.cpp`:same search using1848 tests; best score19 remained the initial missing edge and associated triples.
- `block.cpp`:searches below-incidence blocks of sizes9,14,...,59. If k is block size,m its accepted edge count, and tau the minimum cover of residual edges, completion by stars uses at most52+k-m+tau gates. It seeks zero false positives and k-m+tau<=11. No score below the star baseline12 was found.
- `block-initial.cpp`:preserves the exact preliminary version used for block-hard.log, which was stopped and replaced by block.cpp. The later version explicitly skips already visited matching vertices.
- `matching_audit.cpp` and `check_matching.py`:1054 matching results checked against independently computed exhaustive minima over all8192 point-side vertex-cover choices for each residual graph. All passed.325 randomized star-block baselines (25 for each star count1..13) also passed at score12.

Semantic-audit agent independently reviewed the generator, full-circuit search and final block search, finding no static issue. Any candidate would still require independent dynamic validation and Lean checking. None was found.

Build commands used g++ -std=c++20 -O3 -march=native for search programs; matching audit used -O2. No external libraries are needed. Arguments and final/last logged counts are in status.json and the complete logs. Program exit1 means the configured time budget elapsed; exit143 means SIGTERM, not a proof result.

All program outputs and best-circuit descriptions are retained. No Lean proof of the posted statement or its negation is claimed by this directory.
