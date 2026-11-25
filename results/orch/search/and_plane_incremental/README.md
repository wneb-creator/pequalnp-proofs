# Incremental AND-count premise tests

These are exploratory SAT tests of the premise that the 26-input projective-plane incidence function needs at least 13 binary AND gates when OR gates are free. They do not settle L-meta-2602.

The restricted encoding has 12 AND gates. Each operand is a nonempty OR of inputs or earlier AND outputs, and the final output is an OR of selected AND outputs. Both runs forbid an original input from occurring in both operands of the same AND. The reduced run additionally forbids a prior AND output from occurring in both operands. Completeness of these restrictions for unrestricted circuits has not been proved here. The initial test set contains all 52 minimal positive inputs and 28 maximal negative inputs having at most one point or at most one line. If a candidate had passed these constraints, the script would have evaluated all 704 maximal negatives and added up to 16 diverse violated inputs per round. Neither run reached a candidate.

- Plain run: UNKNOWN after 60.35 seconds, 14,832 variables and 58,997 clauses.
- Symmetry/reduced run: UNKNOWN after 180.31 seconds, 14,832 variables and 59,089 clauses. Its additional restrictions require the first AND sides to contain inputs 0 and 13 respectively, disjoint selections including earlier AND outputs, every AND to be used, and every AND to accept some positive input. No claim is made that these extra restrictions are complete for the unrestricted problem.

Complete DIMACS files and solver stdout/stderr are retained. A solver timeout is not evidence of unsatisfiability. No Lean proof or counterexample resulted.

Commands used from the repository directory:

```
python3 /tmp/oec/pequalnp-pilot-64/and_count_search_incremental.py plane3 12 --seconds 60 --rounds 10
python3 /tmp/oec/pequalnp-pilot-64/and_count_search_incremental.py plane3 12 --seconds 180 --rounds 3 --sym-first --reduced
```

Solver stdout and stderr are stored as deterministic gzip files, preserving every original byte. The compression manifest records both archived and decoded hashes and decoded sizes.
