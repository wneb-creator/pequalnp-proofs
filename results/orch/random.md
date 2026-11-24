Circuit-first search (L-meta-2028)

2026-11-24: independent stochastic searches, all using exact Boolean truth tables.

Completed six-input pass: 100,000,000 randomly generated binary AND/OR DAG trials; 270,332,661 output candidates exactly equal to nonempty C4-free quadratic graph functions. No counterexample. 227,739,904 candidates attain |E|+tau-1; maximal attained example has seven edges, vertex cover four, and ten gates. The lookup table contains all 7,983 labeled nonempty C4-free graphs on six vertices. This is stochastic circuit sampling, not exhaustive circuit verification.

Eight-input pass underway: up to 100,000,000 trials with 12–50 generated gates, pure graph function verified on all 256 inputs, C4-freeness tested by common-neighbor cardinalities, and minimum cover found by exact subset enumeration. Ancestor masks count only gates used by each output.

Petersen target search: 19 gates versus proposed lower bound 20 (15 edges, tau=6). Start from 20-gate minimum-cover factorizations and delete/redirect one gate; evolve a population of 32 circuits by source/op changes with neutral drift and annealing. Score is exact truth-table Hamming error over all 1024 inputs. Initial best 9 errors improved to 6 after 9,224,841 mutations; no exact witness yet.

Truncated tetrahedron target search underway: 12 vertices, 18 edges, tau=8; trying 24 gates versus bound 25, all 4096 inputs checked.

Separate eight-input pass tests stronger component inequalities: AND gate count >= tau, OR gate count >= |E|-1. Any component violation would identify a dead reduction route even without violating total size.

Code and complete logs: /tmp/oec/pequalnp-pilot-31/random/. No Lean result produced.

Completed updates
- Eight-input broad DAG pass: 100,000,000 trials; 303,190,539 exact C4-free graph outputs; 250,325,744 equality outputs; 299,066 distinct labeled graph tables observed; no violation.
- Petersen19-gate search: 100,000,000 mutations, best six errors on 1024 rows. Best circuit accepts all required pairs but also pair {1,4} and independent triple {2,5,9}; not a graph witness.
- Truncated tetrahedron24-gate search: 100,000,000 mutations, best seven errors on 4096 rows; no witness.
- Random maximal eight-vertex graphs: 500 targets, each 1,000,000 mutations, size exactly |E|+tau-2; no witness. One-row near misses are saved as JSON under random/near_one/ and handed to SAT agent.

High-density line-graph strategy
Line graph of Petersen: 15 inputs, 30 edges, tau=10, target budget38 versus proposed39. Its71 maximal independent sets have sizes3 (five),4 (sixty),5 (six). Thirty positive edge-pair samples plus71 negative maximal-independent-set samples are an exact test for monotone graph functions. evolve_line.cpp evaluates these101 constraints in two machine words; any zero-score candidate is rechecked on all32768 inputs. Running one billion bounded mutations; no zero-score candidate yet. Compressed score one is common because it can omit exactly one required edge and is not a proof of near-optimality.

The SAT agent independently reported no local<=4-gate repair for several saved n8 near misses and no witness under4140 vertex partitions for each of16 saved candidates (246 exact graph quotient circuits). See search.md for authoritative counts.

Exact search timestamps from Linux file birth times (UTC):
- L(Petersen) billion-mutation run started 2026-11-24T15:23:47.906Z. Best compressed error1; saved near-line-petersen.json misses required edge pair mask4098={1,12}.
- L(Heawood) billion-mutation run started 2026-11-24T15:27:16.263Z. Parent renewed at15:27:36, expiry15:47:35. This graph has21 vertices,42edges,tau14; trying54gates versus55. There are234 maximal independent sets (42 size5,168 size6,24 size7), hence276 exact compressed constraints.

2026-11-24T15:31:32Z update: L(Petersen) completed the full one billion mutation run without a witness; compressed best remained1. L(Heawood) at432 million ofone billion, best1. Prepared but not yet started: error-directed mutation variant for L(Petersen), and focused7-vertex Fano-orthogonality graph11-gate evolution.

Independent computational audit (status_review) passed current dimensions and semantics. Important implementation limits: multi.cpp/subbounds.cpp encode pair graph in uint64, so they are valid only forN<=11; all those runs usedN=8. The subbounds executable labels any component inequality violation COUNTEREXAMPLE, which would have to be distinguished from a main-statement witness. No component violation was found. Targeted evolution uses separate signature arrays and has no64-pair limit. Every claimed witness must still be pruned/reindexed and independently checked before Lean.

2026-11-24T15:32:50.2Z: started guided L(Petersen)1B, guided ER3 polarity1B, and focused Fano7 orthogonality100M after parent renewal15:32:07(expiry15:52:07). Fano7 finished100M in28.697s; best1 error on128 rows, no witness; near-fano7.json records it. ER3 recomputes C4/mincover and59 exact compressed constraints from theory/polarity3.json edge data.
