# Four-cap local separator to global circuit

Independent review on 2026-11-25: PASS for the source, data and 15-OR baseline embedding. No Lean or SAT process was run for this audit. There is no 14-OR local witness in this package.

The local coordinates map to global inputs [0,1,2,5,13,14,15,17,18,19,22,23,24,25]. They contain four points with no collinear triple and all ten lines incident to those points. The local graph has 16 incidence edges. The 468 prescribed generic rows project to 222 distinct local assignments; their 83 inclusion-maximal members suffice as negative tests for a monotone local function.

For a local canonical program with n=14 initial inputs, reference i<n maps to the corresponding global coordinate, and reference n+g maps to global OR signal 26+g. This preserves every local Boolean operation exactly. Its final AND list is used as one operand of the first appended OR. The other operand is an incidence monomial not contained in the local graph. Appending all 36 remaining monomials uses exactly 36 additional OR gates. Thus a 14-OR local witness would give 50 global ORs; the checked Python control has 15 local ORs and gives 51 global ORs.

The logical negative-case argument uses monotonicity: every projected generic row is contained in one of the 83 tested maximal projections, so rejection of the maximal projection forces rejection of that row. Every appended incidence monomial is also false on every generic row. Positive rows either belong to the local graph or are one of the explicitly appended monomials. No constraint on untested local assignments is needed.

The independent audit reconstructs all 468 generic rows directly from the 8192 point subsets and the Singer incidence relation. It checks all 16384 local assignments for the direct-DNF baseline, the exact reference map and operation lists, and all 547 global positive/generic/singleton/empty samples. A separate symbolic expansion confirms that the 51-OR control has exactly the 52 incidence edges as minimal terms, establishing its Boolean function on all inputs at the Python/algebra level. The 520-sample masks use precisely the already checked compiler ordering and all 13520 input bits agree.

Run `cap4-embedding-audit.py` with arguments `cap4-full-truth.json cap4-direct15-control.json cap4-direct15-global51-control.json fixed-compiler-samples.json <output-directory>` to reproduce the independent audit and mask export. The copied original data/embedding scripts retain their original scratch paths for provenance; the audit script accepts explicit paths and is portable.

`Cap4GlobalControl.lean` is a prepared Program plus mask-certificate source. It has not been compiled and is not a refutation: it contains 51 OR gates. Exact source/input hashes and full output are retained in the JSON report and log.
