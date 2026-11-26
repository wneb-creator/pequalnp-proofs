# Exact hash index for signed search wires

This native memory optimization stores truth tables once in the wire table.
The index maps a machine-word hash to candidate wire IDs. Every lookup compares
the complete 1024-bit truth table; hash equality alone never merges wires or
excludes search states. True hash collisions therefore affect only performance.

The independent source review checks interning, target-DAG emission, restart
lookups, and vector reallocation. It records the invariant that IDs and wire
records remain exactly those of the original complete-word index.

Validation passed:

* All 18 cap-17 frontier files, the complete wire table and the collision
  histogram are byte-identical to the original search.
* Both known 20-gate Petersen circuits pass with **every hash forced to zero**,
  including all projection checks, exact collisions, and 120 symmetry images
  on all 1024 rows.
* A forced-collision test interns 2,000 distinct words, repeats them, checks
  absent lookups and vector growth, and emits the known 20-gate target DAG.
  Phase reconstruction verifies that emitted circuit on every row.
* In the cap-17 comparison, peak RSS falls from 40,716 to 32,052 KiB. CPU time
  falls from 10.259 to 9.698 seconds. These are machine-specific measurements;
  memory savings for the ongoing larger run have not yet been measured.

Generate the same `probe-data.hpp` and `pools.bin` using `signed_data.py`.
Compile `signed-hash.cpp` as C++20 with the generated header directory on the
include path and `cached-collision.hpp` beside the source. Run it in a directory
containing `pools.bin`. Its arguments and checked restart format match
`signed-resume.cpp`; a restart must use a different output directory.

For the forced known-circuit test, compile `hash-known-sanity.cpp` with
`-DFORCE_WIRE_HASH_COLLISIONS`. `hash-collision-unit.cpp` enables that test mode
inside the source. The unit writes `target.json`, which was renamed here to
`known20-target.json`; it is a format test using a previously known circuit,
not a new counterexample.

The source includes the earlier exact collision cache and compact projection
banks. This package is native research, not a Lean proof or a claim that the
ongoing cap-18 search has closed. Complete test output and error streams are
included; `validation.json` and `hash-review.json` state their respective scopes.
