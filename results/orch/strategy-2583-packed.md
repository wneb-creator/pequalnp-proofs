# Packed circuit verification for L-meta-2583

Frozen draft: results/orch/lemmas/PackedCircuit2583.lean,217lines.
SHA256:2bdc88274464f219d2f33078cdf0cbcc66d2e1d3a414161f90bafa36f0fab349.

The draft defines a BitVec-width evaluator for monotone circuits. Each bit position is one input row; AND and OR gates operate on all rows simultaneously. A list-fold proof connects each output bit to the ordinary Circuit.eval result. It supports arbitrary AND/OR fan-in and does not assume a trusted native evaluator.

Point patterns use logarithmic repeated doubling of a block of zeros followed by ones. They avoid lists of8192 entries and large decimal literals. The point-pattern theorem identifies row r at input p with Nat.testBit r p. Line patterns are complements of the OR of incident point patterns, so the26-input layout matches the closedInput used in IncidenceCriticalRows.lean. Every Boolean point subset is represented by some row; the proof uses a13-bit BitVec of the point list, with no enumeration of functions.

Build3 exited1. All declarations through represent_subset elaborated successfully. The only error is the final closure_correct_of_zero proof at line215: the simplifier rewrote the point function but not its uses inside the universal line-closure predicate. The expected remaining fix is to rewrite the pointwise equality hr directly before using the packed-soundness equality. No edits were made after the second lease410 stop instruction.

The complete draft has NOT compiled and is NOT a checked certificate. No8192-row concrete circuit certificate has yet been benchmarked, so kernel runtime and memory for a future63-gate witness remain unmeasured. This is verification infrastructure only; it claims no counterexample or unrestricted lower bound.

Diagnostics are preserved at scratch/gate-elimination/2583/packed-build-3.stdout and packed-build-3.stderr. Earlier builds are in the same directory.
