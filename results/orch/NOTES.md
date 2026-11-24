Pilot 31 shared notes

Held step: L-meta-2028, negation of C4-free graph monotone circuit bound |E| + tau <= size + 1.
Exact statement is in /tmp/oec/pequalnp-pilot-31/statement.txt.
Only parent holds and renews the lease.

Strategies
- theory.md: structural mathematical argument/counterexample
- search.md: computational circuit search
- audit.md: exact definition audit
- library.md: existing reductions and available results
- toolchain agent: install missing Lean and obtain cache

Root integrates findings here. Agents own their separate notes files and scratch paths.
Public L-meta-1035 is still conjectural, with no matching open PR found in a 1780-PR census; desk assigned another step.

Findings (15:19 UTC)
- Circuit/graph definitions have no immediate loophole.
- Existing positive reductions separate OR>=E-1 and AND>=tau; neither follows from imported Defs.
- L_meta_1006 boundary-only construction misses six graph edges and39 truth-table inputs; not a counterexample here.
- Circuit-first search:100 million six-input random DAG trials,270 million candidate C4free graph outputs, no violation.
- Lean4.36 installed in scratch; Mathlib cache downloading.
- NonemptyCircuit.lean sanity lemma drafted and independently reviewed; waiting for compilation.

2026-11-24T15:30:30.643234+00:00 checkpoint
- Four checkpoints pushed; latest0e48f4ffc78be79bca79618ccffe3f5657ce5e7e.
- Named file459lines compiles. Helpers: positive size, requiredAND/OR gates, two-edge sizebound, circuitmonotonicity, independent-setextension, complete boundary verification.
- Exact posted theorem remains absent. Official checker running once to record its verdict honestly.
- Dynamic11v near witness:18livegates,E15,tau5,bound19,15falsepositiveinputs; no validwitness. Addingedges cannot repair it while preservingC4-freeness.
- Searches ongoing: fixed/dynamic SAT, normalizedAND skeletons, L(Petersen),L(Heawood),pairedrectangles.
- Independent searchaudit validated encodings and positivecontrols; rectangle results now pruned/reindexed and requireexactverification.

2026-11-24T15:33:37.548940+00:00: official checker REJECTED(no-theorem); complete output saved. No PR opened.

2026-11-24T15:34:58.529221+00:00 first strategy review
Retired: definition loopholes, one/two shared-rectangle families, complete input substitutions of both11-input near-miss circuits. No validcounterexample.
Continue: exactSAT repairs and normalized AND skeletons; guided mutation on linePetersen,lineHeawood,ER3,and7vertex polarity; dynamicgraphsearch with alternativefitness.
New analytical work: ER3 factorization and graph-edit/gadget repair of dynamic near witness.
Formal support is complete enough to validate a finite witness; no more easypositivehelpers planned.

2026-11-24T15:50:54.079993+00:00: preservation checkpoint and strategy update
- The named file remains 537 lines and builds; the second official checker run again rejected it with no-theorem. No gap proof or PR exists.
- Retired the billion-step fixed-target evolutionary runs after no witness. New randomized objective looks for exact graph circuits that also expose safe OR outputs, then adds pendant-star gadgets. Independent review confirmed graph, cover and live-ancestor cost accounting.
- A systematic nauty census now supplies 28 connected minimum-degree-two C4-free graphs on eight vertices and 112 on nine. These are search targets, not a proved restriction on counterexamples.
- Shared-A/local ER3 synthesis returned UNSAT in its restricted template; this does not prove the unrestricted 30-gate case impossible.
- The initial desk request succeeded. Null replies: 0. Only the assigned L-meta-2028 lease is held.
