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

Fano7 near-miss structure
Let a,b,c form a triangle, with pendant edges ap,bq,cr, and u adjacent to p,q,r. The11-gate near candidate computes
u AND (p OR q OR r) OR ((a OR c OR q) AND (b OR ((a OR r) AND (c OR p)))).
This is exactly the nine-edge graph function OR pqr. The sole wrong input is p=q=r=true, all othersfalse. It uses AND3 and OR8, violating the desired AND>=tau4 only because of that cubic independent minterm. Adding any pair among p,q,r to absorb it creates a4-cycle through the corresponding triangle edge. The six-input core (triangle plus its three pendant edges) pluspqr costs7 gates versus graph bound8. This is a useful obstruction/example, not a counterexample to the posted statement.

2026-11-24T15:36:11Z: L(Heawood)780M/1B; guided L(Petersen)158M/1B; guided ER3 polarity206M/1B; all bestcompressed1, no witness.

2026-11-24T15:37:19.241034+00:00: parent requested resource consolidation (five CPUs shared with SAT). Paused guided L(Petersen) with SIGSTOP at221M/1B,best1; PID preserved in scratch/random/guided-petersen.pid. Heawood and ER3 remain active; no new long runs until consolidation.

2026-11-24T15:39:49.013485+00:00: L(Heawood) completed1B mutations in712.034s,best1,no witness. Resumed guided L(Petersen) after Heawood completion per parent instruction; ER3 remains active.

Short edited-target batches after parent renewal15:40:01 (expiry16:00:01)
- 2026-11-24T15:42:11.868Z–15:42:14.6Z: eight11-vertex edited graph classes, each1,000,000 guided mutations. All n11,E14,tau6,budget18; no witness; bestcompressed1. Exact data/logs/nearJSON and seeds in scratch/random/edited/summary.json.
- 2026-11-24T15:44:11.596Z–15:44:13.9Z: eight9-vertex leaf-stripped cores, each1,000,000 guided mutations, prioritizing edited-6-core. Budgets13 or14. Allbestcompressed1; full512-row validation finds8–13 false-negative rows and no false positives. Equal-score selection favored candidates with every edge pair correct, but none was found. Data/logs/nearJSON and seeds in scratch/random/cores/summary.json.
No long follow-up from these short batches has been started.

Completed long-guided runs (observed2026-11-24T15:47:37Z)
- ER3 polarity30-gate run:1,000,000,000 guided mutations, no witness, bestcompressed1; elapsed587.939s.
- L(Petersen)38-gate guided run:1,000,000,000 mutations, no witness, bestcompressed1; elapsed809.588s includes pause.
- Independent tiny C5 multioutput smoke run:1,000,000 mutations, best summed output-distance2, no witness; elapsed0.328s. SAT agent separately reports eight-gate queryUNSAT and is reviewing positive control/encoding.

New pendant-star gadget search prepared (not yet run)
For a C4-free graph outputG and available OR(S) signals, require each pair inS have zero common neighbors inG, and pairwise selectedS intersections have atmostone vertex. Attach a newcenter and leaf with3gates perS, increasingedges by|S|+1 andtau by1. Exact positive-gain criterion is E+tau-1 + sum(|S|-1) > live cost of graph output AND all selected OR signals. This requires union of their ancestor masks; counting graph ancestors alone is unsound. gadget_search.cpp precomputes all six-input graph tables and tests single/pair/triple compatible OR packs, plus greedy larger packs. It emits full baseDAG/output/auxiliary data for any positive gain; independent expanded-graph full truth verification is required before Lean.

Parent renewed15:47:03 UTC, expiry16:07:02; authorized new gadget objective for~8minutes. Started two six-input lanes with480-second internal caps, balanced seed2028 and OR-biased seed612. Gadget objective independently reviewed by status_review: PASS for currentdimensions/semantics, with required independent expanded-witness verification. Programs and complete logs remain in scratch/random/.
