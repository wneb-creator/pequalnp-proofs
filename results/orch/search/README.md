# Computational diagnostics for L-meta-2583

These are exploratory computations, not Lean proofs of the posted statement or its negation. No counterexample has been found. An UNSAT result below is an unverified solver diagnostic, not a kernel-checked certificate.

## Fano target and encoding

The seven point-line neighborhoods are `{l,l+1,l+3}` modulo 7. Inputs 0 through 6 are points; inputs 7 through 13 are lines. The exact monotone target is characterized by its 21 positive edge-pair assignments and 37 maximal independent sets. A complete Python truth-table check covers all 16,384 assignments.

`counterexample_sat_nofirst.py --gates 26 --out fano26-full.cnf` regenerates the corrected encoding: 5,928 variables and 164,819 clauses. Each gate is AND or OR with two distinct earlier operands. All gates feed the final output, and right-operand indices are nondecreasing. These restrictions preserve the existence of a circuit of at most 26 gates by redundancy elimination, topological reordering, and absorption padding. No read-1 condition is imposed.

Independent audit corrected a symmetry error in the historical `counterexample_sat.py`: forcing the first nonincident pair `(0,8)` can conflict with right-operand ordering. The corrected generator removes all first-pair restrictions. Its SHA-256 is `5a0c17171f2b07a2a303ae1e6db8a82927a183a86bba4d16b3e33a052f035f2c`. The old search remains a sound search for witnesses but is not complete. No UNSAT conclusion was drawn from it.

`counterexample_sat_validate.py` validates the known 27-gate star circuit against every one of 175,949 CNF clauses and all 16,384 truth-table inputs. `known-27-gate-witness.json` is that positive control, not a counterexample.

## Completed initial searches

- CaDiCaL 3.1.0: `cadical -t 600 fano26.cnf`. Result UNKNOWN after 600.02 real seconds, 446.10 CPU seconds, 5,985,100 conflicts. Complete output: `fano26-sat.log`. This used the historical restricted encoding.
- Fano stochastic walk: `python3 counterexample_walk.py --seconds 600 --seed 76`. Evaluated 33,823,394 mutations over 2,254 restarts. Best circuit differed on 36 full truth-table assignments, consistent with a missing edge. Complete output: `fano26-walk.log`.
- C6 diagnostic: `python3 counterexample_c6.py --gates 8 --out c6-8-nonread1-full.cnf`, then `cadical -t 120 c6-8-nonread1-full.cnf`. The encoding additionally requires edge `(0,1)` to have no read-1 proof tree. All six positive pairs and five maximal independent sets are enforced. With no first-pair symmetry restriction, solver result UNSAT in 23.42 real seconds and 7.23 CPU seconds. This does not establish a Lean theorem. `c6-8-nonread1.log` is an earlier, more restricted run; `c6-8-nonread1-full.log` is the corrected diagnostic.

## Structured repair and larger-case walk

`counterexample_repair.cpp` uses incremental CaDiCaL, loading `fano26.cnf`, `fano26.seed`, and `fano26.phases`. A deterministic seed-76 shuffle frees 8 through 16 gate positions per trial; all other operations and operands are fixed by assumptions. Each solve has a 20,000-conflict cap, and the entire run has a 600-second wall-clock cap. The archived first repair run uses the historical restricted base and is only a heuristic neighborhood search. Future runs should use `fano26-full.cnf`, whose variable numbering is identical. The phases and seed do not contain credentials.

The order-3 plane has neighborhoods `{l,l+1,l+3,l+9}` modulo 13, 26 inputs, 52 positive edge pairs, and 704 maximal independent sets. Its star circuit has 64 gates. The 63-gate walk targets a possible improvement. The ordinary walk optimizes boundary mismatches; the positive-priority walk weights each missing positive edge by 1,000, above all possible 704 false-positive boundaries. Commands use 600 seconds and seeds 76 and 77 respectively. These walks are weak diagnostics and are not exhaustive searches.

`snapshot.json` records when the log copies were taken and which runs were ongoing. `source-hashes.json` hashes the archived programs. CNFs, solver binaries, third-party source code, and large build artifacts are deliberately omitted; instances are reproducible from the programs.
