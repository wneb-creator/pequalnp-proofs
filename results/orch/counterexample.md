Counterexample route — L-meta-2592

Read CircuitLowerBounds and MetaComplexity definitions: no obvious modeling gap. FanInTwo genuinely limits operations to AND, OR, NOT and <=2 inputs; invalid/future wires read false.

Available: native C++ compiler, Python numpy/scipy/sympy. No installed z3/pysat/ortools or SAT executable. Reduction-strategy agent is building CaDiCaL separately.

Constructed 20-gate monotone Petersen circuits via six-vertex star cover (15 edges + 6 stars - 1 = 20). C++ stochastic search deletes one gate, then varies operations and prior-wire references; evaluates every one of the 1,024 assignments exactly with bit-parallel arithmetic. It tests all AND/OR/NOT choices, but this heuristic is not an exhaustive lower bound.

Initial best after ~5 seconds: 19 gates, all monotone, differs from target on five independent-set inputs. Equivalent to target plus one spurious nonedge. No counterexample found. Search artifacts are in /tmp/oec/pequalnp-pilot-100/counterexample/.

2026-11-25 13:58 UTC update:

- Unrestricted 19-gate heuristic finished 300 seconds / 1,189,871,616 mutations. Closest candidate uses 18 effective monotone gates (one dead gate) and differs on four independent triples: masks 138, 385, 521, 770. No counterexample.
- Forced 1..4 NOT heuristic finished 300 seconds / 858,324,992 mutations; best differs on 10 assignments.
- Forced active NOT heuristic finished 300 seconds / 656,343,040 mutations; best differs on 12 assignments.
- Signed 18-binary-gate search uses AND, OR, AND-NOT and NOT-AND (negation considered free for this exploratory relaxation); best currently differs on 10 assignments. No witness.
- SAT local repair uses exact 1,024 rows and at most k changed gates relative to the 18-effective-gate approximation, requiring a NOT. k=1 UNSAT in 2.5 seconds, k=2 UNSAT in 8.21 seconds, k=3 unknown at 45 seconds. These are local computational results only, not checked global lower bounds. No proof trace was generated.

Structural form of the near circuit (with four independent centre vertices 2,4,5,6):
A = x0 OR x3 OR x9, B = x0 OR x7 OR x8,
C = x1 OR x8 OR x9, D = x1 OR x3 OR x7.
Output = x4*A OR x5*B OR x6*C OR ((x2 OR A*B*C)*D).
The four shared ORs are vertex stars of K4 whose six edges are the remaining inputs.
A*B*C*D accepts the three perfect matchings (desired pair terms 01,38,79) and four three-edge stars (the erroneous triples). The six-input rows {0,1} and {1,3,7} agree on A,B,C,D but need different output values, so no repair seeing only those four summary signals can distinguish them.

Important repository discovery: L_meta_670.lean (523341 bytes) now proves the full Petersen-minus-vertex lower bound >15 total gates. Its signedRoot14 actually excludes <=14 normalized signed binary operations, so it may strengthen the non-NOT lower bound as well. Root and proof agents informed.

2026-11-25 14:04 UTC update:

All four stochastic searches completed their 300-second limits. Signed18 search tested 1,235,746,816 mutations, best10 mismatches. Total candidates across the four runs:3,940,286,464. This is a heuristic count, not exhaustive coverage.

SAT neighborhood results (all1024 assignments, requirement of at least one NOT):
k1 changed gate UNSAT2.50s; k2 UNSAT8.21s; k3 UNKNOWN45.05s; k4 UNKNOWN45.07s; k5 UNKNOWN45.14s; k6 UNKNOWN45.58s; k7 UNKNOWN45.22s.
No proof certificates were generated for these local SAT runs. They do not establish a Lean result.

A custom CaDiCaL C++ API runner now seeds preferred phases from the near circuit, including every internal truth-table bit. It is running the k<=7 neighborhood for600 seconds from14:01:20 UTC. Root notified; lease renewed14:00:54 to14:20:54 before the run. Files phase-solve.cpp, phase-solve.log and local-current.cnf are in scratch.

K4Summary.lean compiled successfully via the prepared wrapper (`lake env lean`) at approximately14:07UTC, exit0, empty stdout/stderr. File frozen for root review/preservation. This is a related helper, not a proof of L-meta-2592.

2026-11-25 14:11 UTC update:

The 600-second phase-seeded k<=7 local repair returned UNKNOWN.
Started a distinct1200-second global phase-seeded run using SAT agent leaf-CNF: full1024 rows, firstOR(0,2),1..3NOTs, exactly-one choices, some once-read primary input whose sole binary reader has a non-primary co-reader. No prooftrace.
Seed was relabeled by a verified Petersen automorphism and topologically reordered to satisfy lex constraints. One spare gate is a deadNOT. SAT agent independently evaluated all1,452,266 CNF clauses: onlyfivefailures (four target-output rows69,208,276,385 and deadNOTwire22 usage), none among18,945 extra leaf/onehotclauses.
Current driver phase-run.py automatically saves everySAT model plus all1024 computed/target truth-table rows and errorlist. Files phase-leaf-global.* in counterexample scratch. Root renewed14:10:49 before this run; automaticrenewals continue.

2026-11-25 14:34 UTC update:

The explicit19-gate full-row phase-seeded leaf search finished UNKNOWN at14:31:27 (started14:11:24).

Prepared and launched a distinct normalized signed-cost search. It has18 signed binary slots with operations AND,OR,AND-NOT,NOT-AND, all wires false at the zero input. Padding, properness, liveness, ordered sources, Petersen first-gate symmetry and lex topological order are included. There is no separate NOT position.

For each nonpadding signed binary wire choose an actual polarity p_j; original inputs have polarity0. If a selected signed operand needs the opposite polarity of its computed source, force a shared complement flag q_source. The output requires its complement flag when its computed polarity is1. Charge one actual binary gate per nonpadding slot and one NOT per q flag, total<=19. Every flagged complement can be created once and shared. Real gates cannot read the constant sentinel; padding polarities/flags arefalse. This encoding also covers monotone<=18 candidates, which refute our statement after adding an unusedNOT.

Encoding:1,380,304 clauses,201,036 variables,33,043,096 bytes. All32 primitive gate operation/input/output cases were checked independently. A full seed assignment was checked against every clause: exactlyfour wrong-output units fail (rows69,208,276,385); structural, budget, polarity and padding clauses all pass.

Root renewed before launch and requested at mostone active SAT process while the named kernel build runs. Solver uses1200-second cap and no prooftrace. A SAT model is saved completely, simplified by exact truth-table equalities, then all2^k wire polarity choices are checked to reconstruct actual AND/OR/NOT gates; final actual circuit is independently evaluated on all1024 rows. Only actual size<=19 with at leastoneNOT and noerrors would refute the held step. Scripts:gen-signed.py,add-signed-cost.py,phase-signed.cpp,decode-signed.py,signed-run.py. Logs/result:signed-cost-solve.* and signed-cost-driver.log in counterexample scratch.

2026-11-25 14:49 UTC — Monotone18 boundary route prepared, not yet launched. The exact 15 minimal true edge assignments plus 15 maximal false independent sets give 30 complete rows for monotone circuits. `genmono.py rows,lex` produced 121,947 clauses (4.9 MB). Independent seed validation finds exactly four wrong-output clauses; every structural clause holds. The separate decoder evaluates every reconstructed AND/OR circuit on all 1024 assignments, appends one dead NOT, and checks the actual gate count and all rows again. Decoder tested against the known four-error approximation. Sources and all diagnostics are under scratch counterexample/mono18-* and decode-mono.py.

Root reported an unexpected desk HTTP410 and is preserving checked results before reacquisition. No new solver launched after that report. Existing signed-cost20-minute process is exec session65060, expected to stop around14:54 UTC.

2026-11-25 14:52 UTC — Root reacquired a different step, L-meta-2583. Stopped the old signed-cost solver by SIGINT and preserved its complete stdout/stderr and interruption result. It produced neither SAT nor UNSAT. Monotone18 boundary search was never launched. No further Petersen search is active.
