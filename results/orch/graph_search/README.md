Pilot-180 graph search artifacts for L-meta-10760.

These computations are not Lean proofs. The formula result does not establish
the circuit lower bound in the posted gap.

- `witness14.json` and `witness14.txt`: a monotone 14-gate circuit, output wire 20.
  Checked exhaustively on all 128 Boolean inputs by graph_search and status_review.
- `full_formula.cpp`: exact formula-cost dynamic programming on the 28 selected
  assignments consisting of 7 singletons and all 21 pairs. Evaluation is an
  AND/OR homomorphism. All generated row signatures are upward closed. Indexing
  stores the singleton mask and the pair bits not forced by a true singleton,
  giving exactly 2,350,602 states. Constants are free, so lower bounds remain
  conservative. Minimal-cost layers 0 through 13 enumerate every binary formula
  of at most 13 gates. The target is absent. This establishes an ordinary
  computational monotone-formula lower bound of 14, independently source-reviewed
  by status_review. It is not Lean-checked and says nothing decisive about DAGs.
- `full_formula.stdout.txt`: complete fresh-run log, 7,376,368,038 operation
  checks reported in 44.10 seconds. Reproduce with a C++17 compiler and a scratch
  checkpoint filename supplied as argv[1].
- `orbits.cpp`: groups all signatures by adjacent input transpositions and
  verifies that their capped formula costs are constant on each orbit.
  Exactly 1,253 orbits result. A fingerprint comprising the number of vertices
  outside the singleton set and the sorted local profiles (degree, twice the
  incident triangle count, sorted neighboring degrees) distinguishes all 1,253.
  `orbit-costs.txt` records representatives, capped costs, and those profiles.
  A table cost of 14 means at least 14; the search did not determine larger costs.
- `cover.py`: restricted shared-disjunction biclique-cover MILP, with a
  solver-reported optimum of 14.
- `formula-certificate.txt`: a 13,329-byte certificate containing just 1,253
  orbit representatives and capped costs. `compressed_check.cpp` verifies it
  independently of the dynamic-programming checkpoint. It reconstructs every
  orbit, rejects conflicting or duplicate classes, checks complete state
  coverage and the free-input costs, then verifies 47,460,228 binary
  subadditivity cases after normalizing the first operand by input permutation.
  The remaining cases have a right-hand side at least 14 and are automatic.
  `compressed_check.final.stdout.txt` records acceptance with target potential 14.
  This checker is C++, not Lean.

The orbit data provides a compact ordinary formula certificate, but a complete Lean
verification of universal closure and normalization has not been implemented.
