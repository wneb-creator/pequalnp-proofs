# Late full-instance repair diagnostic

The frozen 63-gate seed is not a witness. It computes exactly the desired
52 quadratic edges plus two unwanted edges (point0,line2) and(point12,line9).
Independent antichain propagation verifies that there are no higher minterms.
Its prescribed first gate is OR(0,1). It accepts all52 positives and wrongly
accepts148 of the756 listed negative tests.

The reviewed whole-instance SAT encoder searched at most six gate changes,
with all756 distinct constraints (all808 posted rows modulo duplicate negatives)
and the posted first gate. The80-second query returned unknown after80.72s.
No repaired circuit, global lower bound, or new Lean proof is claimed.

The frozen source, exact inputs, metadata, complete stdout/stderr and original
DIMACS hash/length are retained. The183,866,483-byte DIMACS is not duplicated
because it regenerates deterministically from the preserved source/data:

    python /tmp/oec/pequalnp-pilot-79/meta3773-late63-whole-encoder-source.py --first 1 --round 9 --seconds 80 --all-tests --near-seed /tmp/oec/pequalnp-pilot-79/meta3773-late63-frozen-seed.json --changes 6 --false-phase --sat-profile --generate-only

Restore the files under the named job directory before running that command.
The preservation verifier also rechecks the seed, every posted row, exact
quadratic minterms, metadata test completeness, immutable source and CNF hash.
