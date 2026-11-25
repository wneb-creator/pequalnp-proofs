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
