# ABC search for L-meta-9811

Computational exploration only: no 24-gate counterexample found and no unrestricted lower bound established. Every successful mapped candidate was expanded to AND/OR/NOT primitives and independently evaluated on all 16,384 inputs. Best primitive count: 25. Cheapest transformed nonmonotone result: 28 gates, one NOT (expanded-1). The 27-gate one-NOT seed is a redundant absorption identity applied to a 25-gate star, not an improvement.

The seven completed batches contain 8631 valid mapped outputs. Their summaries, complete controller logs and best circuits are retained here; all individual command scripts, stdout/stderr logs and intermediate circuits remain in /tmp/oec/pequalnp-pilot-85/abc-search. Wide-2 stopped after a runtime cone-size limit was discovered; wide-3 uses corrected bounds and completed without errors. An earlier interrupted wide-1 trial is excluded from these totals.

Searches use unit primitive costs and a macro library whose costs equal explicit AND/OR/NOT implementations. Mapping is followed by primitive expansion, simplification and reachable-gate counting. The parser and all macro expansions were independently audited. False wires in JSON use -1 and require an out-of-range natural index when translated to Lean.

Strategies include randomized input/cube/node order, star/DNF/CNF/Shannon seeds, resubstitution with observability don't-cares, SAT-based resubstitution, DAG rewriting, refactoring, global factoring, Boolean decomposition and area mapping. The source and configuration JSON files record the exact search setup.
