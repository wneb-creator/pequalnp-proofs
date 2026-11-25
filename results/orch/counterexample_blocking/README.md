# Full circuit searches with checked single-reader constraints

No 24-gate circuit or completed UNSAT result was found. The searches use the standard AND/OR/NOT selector encoding with no restriction on the number of NOT gates, plus the independently reviewed consequences of `BlockingAll.lean`. All 14 primary inputs and all nonoutput gates are required to be read. Gate normalization, constant propagation, cone trimming, and OR-copy padding remain as in the previously reviewed standard encoder.

The six single-reader constraints exclude configurations already ruled out by the Lean lemmas. Repeated positive disjunctions of other readers are compressed with fresh variables defined in both directions. This is a definitional extension; it does not change the allowed assignments to the original variables.

The capacity variant also defines D, the number of primaries with at least two distinct reader gates, and F, the number of selected false-sentinel fanin slots. There are at most 2S-F actual reads. The cone uses at least S-1 internal reads, while all N essential primaries use at least N+D reads. Therefore D+F <= S+1-N, giving bound 11 for S=24 and N=14. Per-gate primary membership is counted before the threshold, so duplicate binary fanins do not invalidate this reasoning. The independent audit and small exhaustive controls were performed on the helper supplied by the linear_network agent.

The integration saves the original variable count before adding either family of auxiliary variables. Sample-value phase hints use this saved count, and new cut auxiliaries receive no phase hints. Thus the old sample-variable numbering is preserved. The custom search formulas remain separate from the exact official LRAT encoding.

Completed results:

| Run | Gates | Result | Elapsed seconds | Validation |
| --- | ---: | --- | ---: | --- |
| blocking-smoke25 | 25 | SAT | 8.90 | Exact on all 16,384 inputs |
| blocking-general24 | 24 | UNKNOWN | 299.42 | No candidate; 2,049,029 clauses |
| capacity-smoke25 | 25 | SAT | 7.81 | Exact on all 16,384 inputs |
| capacity-general24 | 24 | UNKNOWN | 239.42 | No candidate; 2,055,239 clauses |

The two 25-gate cases are positive controls, not refutations. Both 24-gate timeouts establish no lower bound. Complete driver and solver stdout/stderr, exact commands, source snapshots, samples, schemas, phase seeds, metadata, and any control candidates are retained. Large CNFs and preference vectors are omitted because the retained sources and inputs regenerate them. Each run records hashes of all source dependencies. Restore the scratch paths listed in its command/source metadata to reproduce an invocation.
