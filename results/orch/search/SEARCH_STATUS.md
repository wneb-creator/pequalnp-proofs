# Search status at the lease interruption

All search processes are paused after the root agent reported HTTP 410. No counterexample or global lower-bound result was obtained. Complete stdout and stderr snapshots are preserved beside the sources.

Completed results:
- Exactly-one-NOT Z3 synthesis: 51 sampled inputs gave a candidate with 42 errors on the full truth table; the 67-input refinement timed out after 120 seconds.
- A 110-input boundary sample with exactly one NOT timed out after 300 seconds.
- The fixed NOT(input0) case timed out after 603 seconds in Z3.
- The signed 18-binary-gate case timed out after 600 seconds in Z3.
- A local repair constrained to at most three changed gate records from the six-error seed was UNSAT on 118 sample inputs after 88 seconds. This excludes only that bounded neighborhood.
- Exact two-gate repair of the same seed found no one-NOT repair after 45,097 mutation/care-set pairs.
- Plain CGP: 889,847,808 iterations in ten minutes, best six assignment errors with no NOT.
- Annealed CGP: 605,159,424 iterations in ten minutes, best nine errors.
- Boundary-weighted CGP: 975,699,968 iterations in twenty minutes, best nine errors.
- The 60-second signed-17 minimal-edge separation probe visited 1,977,856 states and timed out; no witness.

Paused runs and reproduction parameters:
- synth_circuit.py --size 19 --timeout 1200000 --all-minimal --near-log cgp1.stdout --max-changes 4 --seed 6 --out witness19-near4.json
- synth_circuit.py --size 19 --timeout 1200000 --all-minimal --ordered --many-nots --not-count 2 --seed 8 --out witness19-two-not.json
- cadical_input_not.py --solver CADICAL --prefix cadical-inputnot --seconds 1200 --seed 5
- cadical_input_not.py --solver CADICAL --prefix cadical-not-and-edge --kind and-edge --seconds 1200 --seed 10
- cgp_forcednot 1200 7 0 1 12 seed-one-not.txt 1
- cgp_usednot 1200 9 0 1 12 seed-one-not.txt 2
- cgp_signed17 1200 11 0 1 12
- signed_search_bounded.py --budget 17 --first ornonedge --seconds 1800 --output signed17-ornonedge-long.json

CGP builds use g++ -O3 -std=c++17. The signed-17 build additionally uses -DCGP_GATES=17 -DCGP_SIGNED=1. CADICAL is the Lean toolchain bin/cadical, version 2.1.2. Z3 uses the system /usr/lib/x86_64-linux-gnu/libz3.so.4 through ctypes. The signed search is the finite agent's algorithm with its generated signal dictionary restored on recursive return to limit memory. Its restrictions require the existing nine-vertex and smaller graph bounds; it is search evidence, not a Lean certificate.

The direct CNF encoding was checked against a known 23-gate one-NOT circuit: its full truth table matches the Petersen function, and all 37,408 clauses for eight selected rows hold. optimize_phases.py removes dead signed gates, searches output polarities, shares complement wires, and independently verifies any resulting physical circuit on all 1,024 inputs. Its baseline test reproduced the known 20-gate monotone circuit.

Library census: 1,166 files mention nine-input circuits. No final named theorem found in the textual census gave a nine-input size-at-least-17 bound conditional on NOT usage. Relevant specialized size-at-least-16 statements and deletion bridges are recorded in the census files. Equivalent formulations may have escaped the text filters.
