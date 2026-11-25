Pilot132 computational circuit searches for L-meta-650.

These are computational artifacts, not Lean proofs of the posted63-gate statement. No63-gate witness has been found.

Gate encoding is [op,a,b], where0=AND and1=OR. With n inputs, gatej emits wire n+j. Single-output JSON lists use the last gate as output. Input counts differ by experiment:
- Full-plane sources, cases.json, seed64.json, seed66-absorb.json and control witnesses: n=26;52 minimal positives plus704 maximal negatives.
- search-tap-exact.cpp and tap61-tests.json: n=25; residual output and tap are separately specified. The old search fixes residual output85 and tap84. The exact802 tests consist of48 residual positives,553 residual maximal negatives,4 special singletons and197 restricted negatives. This fixed-tap layout is a restricted search, not evidence about arbitrary tap positions.
- search-grid-superset.cpp: n=17; six selected full point rows [0,1,2,3,6,7], line map [13,14,15,16,19,20,21,22,23,24,25],24 edges and52 maximal negatives. Its adjacency file is grid6.txt.
- Historical search-small.cpp: compile with -DNV=10 -DNG=14 for arc4core.txt, or -DNV=14 -DNG=18 for arc4private.txt. These targets were later ruled out using checked L_meta_723 and private-leaf elimination; do not repeat those searches.

Build with a C++17 compiler and optimization. Ordinary search CLI: executable SECONDS OUTPUT_DIRECTORY WEIGHT RANDOM_SEED. Grid/small searches additionally require ADJACENCY_FILE as the fifth argument. The output directory must already exist. Adaptive and superset variants retain the WEIGHT argument for compatibility but ignore it. Use nice10 and no more than two concurrent search processes on this3-CPU job.

search-control.cpp requires -DCONTROL_K=64 or70. Positive controls recovered exact solutions in45.781s/336105iterations and1.38707s/6053iterations respectively; both were independently checked against all756full-plane cases. Timing is from the search logs, not independently remeasured.

search-slack-absorb.cpp explores semantic-preserving rewrites with80genotype slots and at most67active gates. Raw checkpoints can contain all80slots and must be pruned before gate-count claims. Its completed900-second run reached64, not63. prune.py performs singleton-support substitution and duplicate/dead-gate removal on26-input artifacts. describe.py, when present, classifies false minimal supports up to size3.

The66-gate absorption seed uses t=(x0 OR x1) AND (x0 OR y13), substitutes t for point0, and omits edge(1,13) from point1star. It passes all756tests but is only a starting point: the obvious distributive normalization gives65gates, still above the64baseline.

The extremal test characterizations, masks, singleton pruning, positive controls and prepared seed-bank extension were independently audited by search_audit. Full Lean validation is still required for any future witness.

Prepared seed-bank and pair-priority programs take SEED_BANK as the fifth CLI argument after SECONDS, OUTPUT_DIRECTORY, WEIGHT, RANDOM_SEED. superset-bank.txt contains18 weighted entries; data are loaded without code execution. Pair-priority adds26 singleton and273 nonedge-pair negatives,1055tests in17words, with64-bit fitness. Correctness on supports of size≤2 is recorded only as partial evidence if higher-support failures remain. search-tap-free.cpp uses25inputs, final residual output85, and arbitrary tap_output recorded in JSON. SeeSTATUS.md and complete runs/ logs for outcomes.
