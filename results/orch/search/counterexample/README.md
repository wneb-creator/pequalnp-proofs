# L-meta-2592 counterexample searches

No counterexample has been found. These programs and candidates are exploratory, not Lean proofs.

* `search.cpp`: bit-parallel simulated annealing of 19-gate circuits, checked on all 1024 inputs and initialized from 20-gate star covers.
* `search_active.cpp`: the same search, preferring active NOT gates and allowing at most three NOT gates.
* `vector_search.cpp`: a six-input, eleven-gate search for outputs A, B, C, D, N such that D AND N is the matching function on three disjoint edges.
* `structured.cpp`: exhaustive restricted search of all 81 implementations of a fixed eight-gate OR base, followed by at most three extra gates including a NOT. The complete log `structured.stdout` records 17,860,500 checks and no witness.
* `exact20.txt`: a known 20-gate monotone Petersen circuit. Rows give output wire, operation, first input, and second input. Operations 0, 1, 2 mean AND, OR, NOT.
* `best95*.txt`: approximate 19-gate candidates, not witnesses. The candidates `best951` and `best952` differ from the target on 4 of 1024 assignments. Candidate `best953` uses an active NOT and differs on 8 assignments.
* `Twenty.lean`: formalization of the known 20-gate upper bound; Lean 4.36.0 accepted it with exit code 0 and no diagnostics. It does not prove L-meta-2592.

Sources, candidate data, and logs are preserved for reproduction. Search failures are not lower-bound proofs.

Additional measured search results before suspension:

* Signed 18-gate search used AND, OR, AND-NOT, and NOT-AND with free operand negations. The completed 900-second run recorded 3,593,000,000 mutations and 17,965 restarts; its best candidate still has four false positives among 1024 inputs. This does not establish a lower bound.
* Signed 17-gate search was stopped early to prioritize the actual counterexample architecture. Its best candidate has twelve errors. No completed-run mutation total was recorded.
* Second architecture: cycle inputs `(a,b,c,d,e,f)=(x2,x3,x8,x6,x9,x7)` and control `t=x0`. The four outputs are `A=t OR a OR d`, `B=t OR b OR e`, `C=t OR c OR f`, and the C6 edge function R. A 13-gate vector plus six outer gates would give a 19-gate Petersen circuit. The best monotone vector has two wrong output rows (18 and 82, both in R); the composed circuit has five false positives: 520, 521, 522, 552, 554. It is not a witness.
* Later stochastic variants prefer an effective NOT(t) and nonlinear sharing inside A/B/C, since the fixed six-OR implementation has been excluded by the proof team. Their logs distinguish overall near-witnesses from candidates passing those heuristic preferences.
* A 30-second tightness probe sought C6 using seven signed gates after a free bank of the three opposite-pair ORs. It recorded 495,700,000 mutations and found no witness; the best candidate has one wrong input. This does not improve the checked bank lower bound.

All work stopped when the root agent reported desk HTTP 410. Full source, candidate data, and complete stdout/stderr logs were saved before stopping. No counterexample was found.
