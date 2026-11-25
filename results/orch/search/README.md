Counterexample search for L-meta-2373

No19-gate witness has been found. These searches are not lower-bound proofs.

search.cpp: stochastic19-gate AND/OR/NOT search seeded by deleting one gate from verified20-gate star-cover circuits. Initial600-second run ended with weighted mismatch6 (six false negatives, zero false positives); complete stdout/stderr is search-log.txt.

synth.py: CaDiCaL CEGAR synthesis, one-hot selectors, optional structural search constraints. Fixed20-gate source validated SAT on all1024 rows. Unseeded20-gate monotone positive control was UNKNOWN after120 seconds; see sat20-control-run.txt. Global19-gate searches and incremental local searches remain running as of this snapshot.

local_sat.py and cadical_wrap.cpp: incremental CaDiCaL search for a20-gate circuit with one identity gate, altering4–10 gates of known20-gate references. Positive control SAT before trials. --promise uses91 rows (76 independent sets plus15 edges); every candidate is separately checked on all1024 rows.

The shared library is built from the pinned Lean toolchain bundled libcadical.a, with its libc++ runtime; no downloaded solver source is used. The source hashes are recorded in counterexample-manifest.json.

Global19-gate first-AND(edge) and first-NOT(input) cases both returned UNKNOWN at600 seconds. Complete solver stdout/stderr is preserved under sat-andedge/round0.log and sat-not/round0.log. These are time limits, not UNSAT results.
