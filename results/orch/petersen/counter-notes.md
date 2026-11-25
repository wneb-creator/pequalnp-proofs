# Petersen counterexample exploration

The target has 15 edges and15 maximal independent sets (10 ofsize3,5 ofsize4). These30 critical assignments determine every monotone circuit computing the target. The exact data are in counter-critical.json.

The first stochastic19-gate search from canonical20-gate vertex-cover circuits tested3,420,490,113 mutations over34,205 restarts without a witness; best candidate missed one critical assignment.

Three normalized first-gate cases were encoded from checked reduction R_meta_2590_932. Raw-function exclusions are enforced semantically by adding all singleton/pair/co-singleton/co-pair test assignments (125 samples total). Independent audit checked the clauses. Three240-second runs ended UNKNOWN. Three further240-second runs with AND-count≥6 and input-dominance pruning also ended UNKNOWN. Input-dominance pruning has a mathematical minimization argument but no Lean bridge here.

An additional safe structural symmetry orders the gates after the prescribed first gate by(maximum predecessor,minimum predecessor,op). Greedy topological sorting justifies this and was tested on1000 random DAGs. Known20-gate witnesses satisfy the strengthened encoding. Three600-second runs using it were interrupted on lease loss without a verdict.

The7-AND/13-OR20-gate witness from gate_count_theory was independently verified on all1024 inputs. A new19-gate mutation run seeded from that witness was interrupted on lease loss; no witness had appeared.

A smaller side-route was settled computationally: C6 on(a0,a1,a2,b0,b1,b2), with three opposite-pair OR resources ai∨bi supplied free, has no circuit with≤7 additional binary gates. A complete64-assignment SAT query returned UNSAT in17.55s after162461 conflicts. Its22.7MB binary LRAT proof, CNF, generator metadata, and full logs are preserved in counter-output/. This is computed evidence, not a Lean-checked proof of any posted statement.

2026-11-25T15:23:56.816565+00:00 Root reported lease loss; all owned live searches were signalled to stop. No counterexample to L-meta-2590 and no full-gap UNSAT proof was obtained.
