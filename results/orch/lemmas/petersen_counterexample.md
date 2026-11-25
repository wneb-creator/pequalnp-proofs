# L-meta-2590 Petersen counterexample strategy

Extracted the exact fifteen-edge Petersen graph and independently enumerated its fifteen maximal false assignments, matching R_meta_2590_1. Built a twenty-gate monotone binary circuit from the six-vertex cover complementary to independent set 116. Exhaustive evaluation on all 1024 assignments passes. This validation is Python only so far.

Data: /tmp/oec/pequalnp-pilot-144/counterexample2590/petersen_cases.json. Gate representation is [operation, earlier wire, earlier wire], operation 1=OR and 0=AND, inputs0..9, output29.

## Checked partial
PetersenSamples.lean passed Lean 4.36.0 via lake env lean -M4096 (exit0, empty samples-build-1.log). It verifies size20, Monotone2, circuit evaluation on all30 decisive rows, and target values on those rows. Full-function equality is currently being checked separately.

## Model caveat
Monotone2 allows constant/unary gates and forward/missing wire reads, unlike IsAO2. Constant propagation and wire renaming can normalize these for a nonconstant target without increasing gate count, but any strict-AO2 SAT lower bound needs that argument formalized. No model exploit found.
