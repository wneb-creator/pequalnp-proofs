# ABC search for L-meta-9811

Computational exploration only: no 24-gate counterexample found and no unrestricted lower bound established. Every successful mapped candidate was expanded to AND/OR/NOT primitives and independently evaluated on all 16,384 inputs. Best primitive count: 25. Cheapest transformed nonmonotone result: 27 gates, one NOT (masked-1). The 27-gate one-NOT seed is a redundant absorption identity applied to a 25-gate star, not an improvement.

The eight completed batches contain 10631 valid mapped outputs. Their summaries, complete controller logs and best circuits are retained here; all individual command scripts, stdout/stderr logs and intermediate circuits remain in /tmp/oec/pequalnp-pilot-85/abc-search. Wide-2 stopped after a runtime cone-size limit was discovered; wide-3 uses corrected bounds and completed without errors. An earlier interrupted wide-1 trial is excluded from these totals.

Searches use unit primitive costs and a macro library whose costs equal explicit AND/OR/NOT implementations. Mapping is followed by primitive expansion, simplification and reachable-gate counting. The parser and all macro expansions were independently audited. False wires in JSON use -1 and require an out-of-range natural index when translated to Lean.

Strategies include randomized input/cube/node order, star/DNF/CNF/Shannon seeds, resubstitution with observability don't-cares, SAT-based resubstitution, DAG rewriting, refactoring, global factoring, Boolean decomposition and area mapping. The source and configuration JSON files record the exact search setup.

The final masked-1 batch starts from nontrivial shared masks: if an existing star output G is independent of input x and G implies F, replacing every read of x with x OR G or x AND NOT G preserves F. The144 generated seeds validate on all16,384 assignments;72 cost26 monotone gates and72 cost27 gates with one NOT. The batch maps2,000 circuits, all valid, with best25 and transformed one-NOT best27. masked_seeds.py and the seed metadata index reproduce the generated family from star25.blif.
