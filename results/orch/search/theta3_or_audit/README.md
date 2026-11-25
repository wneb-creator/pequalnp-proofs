# Theta graph OR-count attempts

The graph has three length-three paths between vertices 0 and 1, through pairs (2,5), (3,6), and (4,7). It has eight inputs and nine edges. As in the neighboring C6 audit, each OR operand and the final output are arbitrary nonempty conjunctions of inputs and earlier OR outputs.

Three seven-OR searches each timed out after 30 seconds: all 256 assignments, an exact 18-row monotone boundary basis, and that basis with lexicographically ordered operands to remove OR commutation symmetry. **All three results are UNKNOWN.** They do not establish a lower bound.

An eight-OR control returned SAT in 18.14 seconds. Its circuit was independently evaluated on all 256 inputs. This is a computational upper-bound control, not a result for L-meta-2602. No normalization or circuit-to-CNF interpretation has been proved in Lean.

The archive preserves exact scripts, complete gzip solver outputs, summaries, the positive control, and an independent validator. The manifest records encoder, dependency, solver and CNF hashes and exact solver arguments. Reproducible CNFs are omitted. The scripts retain their original job-local paths.
