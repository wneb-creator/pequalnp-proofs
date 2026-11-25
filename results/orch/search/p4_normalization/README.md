# P4 operand-order normalization

This research artifact proves that sorting each of a typed five-gate candidate's two earlier inputs preserves both its direct Boolean evaluation and its formal derivative trace. With an explicit distinct-input hypothesis, the sorted candidate meets the strict ordered-source constraints of the P4 CNF encoding.

`ReductionsNormalizeFast.lean` compiled successfully with Lean 4.36.0. The five exported helpers use only `propext` and, for the strict-order arithmetic proof, `Quot.sound`; the complete axiom output is preserved. It imports the previously checked direct-evaluator semantics module. This normalization is a real checked helper, but it is not itself a P4 lower bound or a proof of L-meta-2602. The full circuit-to-CNF clause bridge is still compiling separately.

The first fast attempt left evaluator goals because one-pass simplification did not expose the record projections before applying the symmetry lemmas. The successful source separates `dsimp` from the generic gate rewrites. The complete first failure log is retained. An earlier 32-case whole-circuit attempt was explicitly terminated after the successful faster proof; its empty output and termination metadata are retained, and no result is claimed from it.

For reproduction, restore the previously archived Reductions, ReductionsIR and ReductionsSemantics modules into the job scratch directory, compile them there, regenerate this source with `p4_normalize_fast_generate.py`, and run Lean through `lake env` with that directory prepended to LEAN_PATH. The axiom probe is also preserved. These are research modules with helper namespaces and research imports, not an Outside proof PR file.
