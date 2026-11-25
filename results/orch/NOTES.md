# L-meta-9811 orchestrator notes

Live step: 14 vertices, 19 edges; claim no AND/OR/NOT circuit of size at most 24. Reductions are closed.

Strategies: lower_bound (restriction proof); lemma_search (reuse/isomorphism); counterexample (upper bound search); status_review (definition audit); toolchain (setup). Parent holds lease and writes final file.

2026-11-25T11:43:32.083104+00:00 counterexample: graph is C4-free bipartite 7+7 with 19 edges. Degrees [2,2,3,3,3,3,3,2,3,2,3,3,3,3]. Exhaustive subset enumeration gives minimum vertex cover 7, exactly the two bipartition sides. Perfect matching (0,8),(1,7),(2,12),(3,11),(4,13),(5,10),(6,9). Standard star circuit has 25 gates; biclique factoring cannot improve because no K2,2. A 300-second full-truth-table stochastic search for 24 gates is running in scratch; no counterexample yet. This search cannot certify impossibility.

2026-11-25T11:44:05.903142+00:00 toolchain: Installed pinned Lean 4.36.0 into scratch because no Lean or warm cache existed. Official Mathlib cache get succeeded (9117 files); tracked config files unchanged. Source /tmp/oec/pequalnp-pilot-85/lean-env.sh per shell command. Full log /tmp/oec/pequalnp-pilot-85/toolchain/cache-get.log. Defs project oleans still require coordinated build.

## status_review: graph/definition audit and witness

- HasCircuitSize is standard fan-in-two sequential AND/OR/NOT model; no definitional shortcut found. Nullary constants and out-of-range false wires behave as documented.
- Target is Fano/Heawood incidence with (0,7),(1,9) removed. Adding those two edges gives all 21 left-pair neighborhood intersections of size one.
- Computer checked no 4-cycles; degrees [2,2,3,3,3,3,3,2,3,2,3,3,3,3]; min vertex cover 7, attained only by the two bipartition sides.
- Natural star circuit uses 12 local OR + 7 AND + 6 global OR = 25 gates. Scratch formal certificate: /tmp/oec/pequalnp-pilot-85/Upper9811.lean. Awaiting central Defs build.
- Forest lower-bound infrastructure exists in Helpers/ForestBound.lean, but only Defs is an allowed project import, so required proofs must be copied locally. General graph/biclique cost definitions explicitly give upper bounds, not general lower bounds.

## Lemma search 2026-11-25T11:45:09.600827+00:00
The 14-input 19-edge target has only a 20-gate lower bound from available restriction engines. Reconstructed exhaustive DP in /tmp/oec/pequalnp-pilot-85/lemma_search/gtree_search.py explored 106,170 states. f0/f1/b2 alone:17. Adding L_meta_5670 exact reader Pays alternatives:20. Adding268 parsed checked graph lower bounds as isomorphic bases still20. Vertex-deleted bounds18 or19. Outputs in gtree_search.log, gtree_readers.log, gtree_bases.log.
Sources: L_meta_9129.lean contains GTree checker lines7324ff, prove_base finite-frontier engine7147ff; file431KB. L_meta_9386.lean414KB proves9-variable≥14 via input identification into8-variable finite table base. L_meta_5670.lean243KB proves full Heawood incidence graph14-variable≥20 using readerTheorem and known cycle leaves. Its fanout_step lines4163ff gives Dep y and Pays=(Drop false3 AND Drop true3) OR (Drop false4 AND Drop true2) OR (Drop false2 AND Drop true4). No generator scripts were found in tools/ or lean/.
For graph edge functions with no free OR inputs, NoFunnel can be characterized combinatorially by no nonadjacent equal-neighborhood vertices and no isolated K2. Requires proof before Lean use. Any free OR input makes RestrNC fail because setting it true is constant.

2026-11-25T11:45:30.065365+00:00 linear_network: trying 11-gate AND/OR/NOT network producing the seven neighborhood disjunctions on seven inputs. A successful network would replace 12 neighborhood OR gates and yield a 24-gate refutation. Search is C++ stochastic on all 128 assignments; seeded from 24 single-gate deletions of the canonical network. Source and full logs under /tmp/oec/pequalnp-pilot-85/linear_network. No witness yet.
