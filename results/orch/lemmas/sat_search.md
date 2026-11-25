# Constraint-guided search for L-meta-2583

## Method
Uses installed libz3.so.4 through its C API (version4.13.3); no solver download. Encodes26 AO2 gates on14 inputs, with each gate reading two distinct earlier wires and either AND or OR. Packed bitvectors encode21 minimal positive and37 maximal false assignments of the cyclic Fano incidence function. Each satisfying model is independently evaluated on all16,384 Boolean assignments.

## Validation
- Exact27-gate baseline: SAT; all16,384 inputs passed.
- Unchanged26-gate near-witness: UNSAT.
- Searches within1 and2 changed gates started. These are restricted searches, not full lower bounds.

Scratch: /tmp/oec/pequalnp-pilot-144/sat_search/; complete SMT files, solver logs, result JSON, and generator retained.

## Final search status
Stopped at 2026-11-25T15:06:27.359714+00:00 after root reported the lease was no longer live. All active solver processes terminated; no further search performed. One-gate repair was UNSAT in3.61s and two-gate repair UNSAT in22.60s. Three-gate repair and unrestricted26-gate canonical synthesis were interrupted and have no verdict. No counterexample found. Independently confirmed all37 maximal false assignments by exhaustive Boolean enumeration. All source, SMT problems and complete logs remain in scratch/sat_search.
