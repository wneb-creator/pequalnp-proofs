# Archived Petersen circuit search

Status: **no 19-gate witness and no UNSAT result**. These are incomplete computational experiments, not a Lean proof or refutation. Work stopped after the parent determined that the desk had returned a pre-existing lease belonging to another pilot.

- `synth.py`: Z3 CEGIS search for AND/OR/NOT circuits. The 19-gate runs require all gates to be live, binary operands distinct, and exactly one or two NOT gates. They were interrupted before the initial SAT call returned. The local-repair run was stopped earlier to limit CPU use. These restricted searches cannot establish the posted universal lower bound.
- `synth-19-1.log`, `synth-19-2.log`, `synth-near.log`: complete output of those incomplete runs.
- `known20.json`, `known20-verified.json`, `synth-smoke.log`: a known 20-gate monotone circuit used to validate the encoding. The fixed circuit passed the SAT encoding and independent evaluation on all 1,024 inputs. This validation is computational only, not Lean-checked.
- `evolve.cpp`: bit-parallel evolutionary search. The `ACTIVE_NOT` compile flag additionally requires an active NOT and penalizes more than three NOT gates.
- `evolve-114.log`, `evolve-active-115.log`: complete output of the interrupted evolutionary runs.
- `near.json`: the best approximate candidate from the unrestricted evolutionary run. It has an inactive NOT and an 18-gate monotone core. It misses Petersen edges (1,2) and (5,7), so it is not a counterexample.

The solver was Z3 5.3.3 downloaded from its official GitHub release. No solver vendor code, executable, shared library, credential, lease identifier, or token is included here. Absolute scratch paths in the logs describe the original invocation.
