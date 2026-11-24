Computational counterexample search for L-meta-2028

Scope: exact monotone binary AND/OR circuits, seeking size < |E| + tau - 1 on C4-free graphs.
All numerical search observations are computational evidence, not Lean proofs.

Tooling
- Kissat compiled from https://github.com/arminbiere/kissat into /tmp/oec/pequalnp-pilot-31/search/kissat.
- synth.py creates SAT formulas. Graph can be unknown: C4 exclusions, at least e edges, no independent set larger than n-t, and k=e+t-2 circuit gates.
- Each gate selects two distinct earlier wires and AND/OR. First input pair normalized by vertex relabeling only when graph is unknown. Gates are ordered by maximum fanin, then minimum fanin for equal maxima, which removes independent-gate ordering symmetry.
- Fixed graph encoding only evaluates its edge pairs (positive) and maximal independent sets (negative). Monotonicity makes these examples sufficient. Any candidate is independently re-evaluated on every Boolean input.
- Full stdout/stderr and CNF instances saved in scratch.

Completed initial SAT cases (UNSAT)
- n4, at least3 edges, tau>=2,3 gates:0.01s.
- n5, at least5 edges, tau>=3,6 gates:0.19s.
- n5, at least6 edges, tau>=3,7 gates:3.84s.
- n6, at least6 edges, tau>=4,8 gates:32.6s.

11-vertex L_meta_1006 seed
- C4-free graph has16 edges, tau7, proposed lower bound22.
- Its AndCount circuit expands directly to20 binary gates but has39 false negatives and no false positives; therefore it is not a counterexample.
- Missing quadratic edges: (4,10),(5,9),(6,7),(6,10),(7,9),(8,9).
- Started exact21-gate fixed-graph SAT query:5680 variables,204307 clauses,600-second bound.
- Started independent stochastic21-gate search from22-gate star-cover circuits, deleting one gate and annealing rewiring;600-second bound.

Updates through 15:30 UTC
- Positive controls: triangle has a decoded4-gate SAT solution; C4free6-vertex theta graph has a decoded9-gate solution. Full truth tables checked; these meet rather than beat the proposed bound.
- Generic n6/e7/tau3, n6/e7/tau4, n7/e9/tau4, n7/e8/tau4 searches timed out after120s each. UNKNOWN, not UNSAT.
- Enumerated all900 labeled C4free6-vertex7-edge graphs, grouped by all720 vertex permutations into4 isomorphism classes. The first3 classes (tau3, target8gates) are UNSAT in16–18s. Fourth (tau4, target9gates) timed out120s.
- Exact11vertex21gate synthesis timed out600s; no witness.
- Local repair around theory agent21gate near miss: up to3 or4 changed gates UNSAT (2.94s and54.86s);5 and6 changes timed out120s.
- Local up-to4-gate repair of random agent n8 targets30,6,11,4: all UNSAT in5–8s.
- Exhausted all4140 partitions of8 inputs for16 n8 near-candidate circuits. Found246 exact loopless C4free quotient graph circuits among286 eligible quotients, none below bound after semantic gate deduplication.
- Exhausted constant restrictions (each input free/0/1) of the same16 circuits. Found5611 exact nonempty C4free graph restrictions, none below bound after semantic gate deduplication.
- Theory dynamic candidate prunes to18gates on graph with15edges,tau5,bound19, but15 false-positive inputs. No cheap final existing-wire filter. Local4 repair UNSAT.
- Started normalized6AND-gate synthesis for original11vertex graph, both arbitraryOR and OR-budget-limited variants. Budget-limited excludes OR-subexpression sharing and is explicitly a restricted cost model.
- Started local3 repair on line graph of Petersen:15vertices,30edges,tau10,38gates,target lower39.

Independent audit
- status_review inspected synth.py and found CNF semantics and topological-order pruning sound.
- Decoder now explicitly verifies all Boolean inputs, C4-freeness, exact vertex cover number, and reports strict counterexample inequality.
- An early anneal graph/metadata filename collision was found and corrected. Files anneal.log and anneal-best.json refer to an erroneous K11 run and are DISCARDED. Correct target files are seed11-graph.json and anneal-seed11*. Original exact seed11.cnf was generated before its graph metadata overwrite and is unaffected.
