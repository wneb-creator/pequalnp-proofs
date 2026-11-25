# Trusted LRAT control

`results/orch/lemmas/Reductions.lean` proves that its explicitly listed CNF is unsatisfiable. It uses the repository LRAT checker and `decide +kernel`. The file compiled, and an explicit axiom audit listed only `propext`, `Classical.choice`, and `Quot.sound`. It contains no native evaluation or new axiom.

The CNF was generated for the five-gate four-input central-edge search described in the neighboring `path_center_audit` archive. **That circuit-to-CNF interpretation has not been proved in Lean.** The checked theorem is only UNSAT of the concrete formula. It is not a proof or refutation of L-meta-2602, and does not establish the eight-input double-star lower bound.

The proof uses 1,274 trimmed RUP steps from a CaDiCaL LRAT certificate. The generator checks the hints, supplies explicit unit literals, renumbers clause keys, and packs the resulting tokens. The kernel-checked soundness theorem makes the generator and SAT solver untrusted. The complete original certificate, CNF, solver output, build output, axiom output, exact source references, and hashes are preserved here. No default BVDecide proof is included; its separate scratch control was rejected for introducing a native axiom.
