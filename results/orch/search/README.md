# Counterexample search artifacts for L-meta-2592

No valid counterexample was found. These are heuristic and bounded SAT searches, not a lower-bound proof.

- `known20.json` is a 20-gate monotone circuit verified on all 1024 inputs.
- `best19.json` contains 18 active monotone gates and one unused NOT. It has four false positives and is not a solution. Its 18-gate approximation was separately checked in Lean in `../lemmas/approximation.lean`.
- `run-98.log` and `run-multi11.log` are complete logs of interrupted exploratory runs; they do not report a final candidate count.
- `run-relaxed11.log`: completed 300 seconds, 1,474,300,000 candidate edits, best eight care-row errors.
- `run-active19.log`: completed 300 seconds, 867,200,000 edits, best 18 errors.
- `repair1.log` and `repair2.log`: complete local-neighborhood searches, 7,872 and 56,123,136 candidates, no improvement below four errors.
- `run-cycle13.log`: completed 300 seconds, 1,615,500,000 edits, best six core care-row errors. The lifted candidate has 19 gates and two NOTs, but 15 Petersen errors.
- `core13-one-not-solver.log`: complete SAT log, UNKNOWN after about 164 CPU seconds and 2.05 million conflicts.
- `core13-two-not-solver.log`: complete SAT log, UNKNOWN after about 117 CPU seconds and 1.37 million conflicts.
- `core13_reach.py` is a prepared signed-reach strengthening, not yet run at this snapshot.
- `lift_core13.py` independently checks all 128 core rows and all 1024 lifted Petersen rows. A 14-gate core baseline lifts to a correct 20-gate circuit.
- `known20.blif`, `unitbasis.genlib`, and `blif_to_circuit.py` prepare an ABC route. No ABC run occurred because the official binary artifact download was blocked. No download diagnostics or redirect URLs are included here.

The C++ programs use only the standard library. Build with a C++17 compiler. The SAT Python scripts require the existing Kissat executable path recorded in their source; `core13.py` and `synth.py` originate from the exact-synthesis agent. The selected sources, candidates, and complete run logs are hashed in `MANIFEST.json`. Binaries and regenerable CNF files are omitted.
