# Petersen nineteen-gate local search

Reuses the independent simulated annealer from L2583, with explicit output parsing, complete exhaustive witness verification, read-1 guidance, neutral topological swaps and optional frozen prefix. Only one process/CPU is used, separate from the SAT agent.

Target graph edges: 0-1-2-3-4-0, spokes 0-5,1-6,2-7,3-8,4-9, and inner cycle 5-7-9-6-8-5. Inputs are0 through9. Gate op0 is AND, op1 is OR; gate g produces wire10+g. Candidate dumps append the explicit output wire.

The twenty-gate star baseline comes from the prior verified `counterexample/baseline.json`, whose operation convention is reversed; conversion flips its opbit. The annealer exhaustively verifies the baseline again before any search. Thirty extremal rows consist of the fifteen edges and fifteen maximal independent sets. A perfect extremal fit is always checked separately on all1024 assignments before export.

The read-1 guidance is heuristic, not an acceptance condition: half the restart objectives penalize a candidate if every accepted positive edge already has a two-leaf proof tree. Such a tree consists of one AND joining two OR-only input paths. AND/OR networks have no constants in this search, so that recurrence is exact. Search failure gives no lower bound.

First run: seed2590104,300-second cap. The baseline passed all1024 assignments. Initial deletion attains one extremal error. Read-1 guidance found another one-error circuit with an accepted edge lacking a read-1 tree. Independent exhaustive checking found zero false positives and nine false negatives for each best candidate: they compute Petersen with one edge removed, respectively(4,0) and(2,3). No exact witness.

The `anneal-logs/` copy is a live checkpoint while the first run continues; the complete original stdout/stderr remain in the scratch directory and will replace the checkpoint at completion.

Prepared but not yet compiled/run: `anneal_hot.cpp` keeps the same checked witness semantics, raises the annealing-temperature range, lengthens each restart and refreshes the best-state reservoirs. It also exports the first candidate for each distinct single incorrect extremal row, to distinguish missing-edge circuits from false-positive variants. Search runs remain sequential.

First run COMPLETED at300.003 seconds:841,470,000 mutations,28,049 restarts, bestone extremalerror andnine full-input failures. Exit1 means unsuccessful heuristic search, not a verification failure or UNSAT proof. Full completed logs replace the earlier live checkpoint.

Hotvariant compilation passed (empty compilerstdout/stderr). It remains unrun while awaiting the coordinator renewal notification required before a long search.

Hotrun completed normally at300.006 seconds:747,175,936 proposals,7,472 restarts, bestone extremalerror andnine all-input failures. Every one-error kind observed was a missingpositiveedge; no lonefalse-positive extremal candidate and no exact witness. Full completed logs, allfifteen near candidates and best/nonread candidates are archived in `anneal-logs/`.

Coordinator then ordered all work paused after another unexpected lease-expiry response. No search process remains.

A new verified seed family was prepared before the pause. Petersen plus the nonedge(0,2) has this19-gate circuit: two K2,2 blocks `(x0 OR x3) AND (x2 OR x4)` and `(x0 OR x7) AND (x2 OR x5)`, three stars centered1,8,9 with leaves{0,2,6},{3,5,6},{4,7,6}, then OR allfiveblocks. Eachblock costs3gates and their topOR costs4. All1024 assignments agree with the augmentedgraph. Relative to Petersen there are zero false negatives and fivefalsepositives, masks5,69,261,517,773; only69 and773 are maximalindependentrows.

`supergraph_seed.py` generated all30 automorphic nonedge extensions and independently verified all1024 assignments of each. Complete generatorlogs, netlists and scratchmanifest are archived. This is not a counterexample to the posted target: each circuit intentionally computes an augmentedgraph.

`anneal_super.cpp` was prepared to start exclusively from those30seedcircuits, weighting missingedges16–31times as much as falsepositive extrema. It is UNCOMPILED and UNRUN; the leasepause occurred before anysupergraph searchphase. All earlier completedruns andsources remain separately preserved.
