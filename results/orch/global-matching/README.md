# Interacting two-dirty matching warm starts

This extends the reviewed mixed-OR global search with a distinct valid131-gate starting circuit. It is above the124 target and is not a counterexample.

Choose two same-side centers a,b and opposite-side vertices u,v with exactly the matching edges av,bu among the four cross pairs. Let h0=(a OR b) AND (u OR v), h1=(a OR u) AND (b OR v). Then h0 AND h1 equals av OR bu. Both factors are dirty for that matching, and no individual input variable cleans either factor. The separate Lean-checked SearchTwoDirtyMatching.lean proves this exact identity and obstruction.

The initializer inserts these three AND rows into inactive helper slots before all star nodes, removes av and bu from the original stars, and ORs the matching result into the final output. It preserves the full plane function and has exactly131 binary gates. Mixed OR rows and all other search operations remain as in the previous reviewed model. Matching initializations are counted in progress/final logs. Initializations without enough dormant slots fall back to the prior model.

Validation: eight matching warm starts were expanded and scalar-checked on all105positive+25,237maximal-negative assignments, with exactly131 gates and exactly two dirty ANDs. An independent reviewer checked another160 initializations, including43 matching starts, for exact topology, count and all25,342 test signatures. A concrete valid131-gate fixture is saved here for reuse.

Command from repository root:
```
python3 results/orch/global-matching/SearchStochasticPlaneMatching.py --seed 14772913 --seconds 1200 --output-dir /tmp/oec/pequalnp-pilot-29/stochastic-plane-004
```

No smaller circuit has been found. This next run was queued at snapshot time; the previous mixed search was still running to its cap.
