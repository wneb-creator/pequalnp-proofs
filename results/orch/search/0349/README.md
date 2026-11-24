# Reviewed OR-sink query and streaming encoder

This package preserves independently reviewed search preparation. No query in this package has yet produced a SAT witness or UNSAT result for L-meta-1024. The all-OR-output-sink reduction is mathematically reviewed, but its general Lean bridge is still being formalized. The CNF writer was checked byte for byte against the original writer on four fixtures; the complete test log and output hashes are included.

The runner and writer sources were independently approved in NOTES.md at 03:39:50 UTC. Encoder dependencies are preserved in ../0326; source paths intentionally retain the original scratch layout and require relocation before reuse. The solver is the bundled CaDiCaL from the task toolchain. No portability or independent Lean certificate claim is made.

The two runners differ only by the streamed clause writer and distinct output directories. Each full candidate is checked independently on all 3003 required input rows. Restriction and normalization assumptions are recorded in the runner and prior archive. Huge solver traces remain in scratch; this is source preparation, not a solver result.
