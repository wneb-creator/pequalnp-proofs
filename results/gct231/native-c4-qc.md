# C4-support quadratic/cubic finite-field unit result

The native sparse solver returned the unit basis `[1]` over F1009 for the
six quadratic and ten cubic necessary equations of the direct C4-support
chart. It exited successfully after 17.229 seconds with peak child RSS
81,300 KiB. The input has 12 variables and 492 terms. There were 144
pair-processing rounds followed by one final basis reduction.

This is a finite-field computational result. It does not establish a QQ or
complex inconsistency and is not a Lean proof. An exact characteristic-zero
ideal-membership certificate is still required before using this result in
the proof. The solver's unit claim has not yet been independently certified
as an ideal-membership identity.

The subset was selected by total degree of the three parameter monomials,
keeping exactly degrees two and three in the original order; quartic
conditions are omitted. Its source is the reviewed direct path-C4 JSON,
SHA256 `95581baa94cc80db67d9a6a6025dfd9de935ae13f825cac51ef52f88081b50e1`.
The sparse input was independently reconstructed row by row modulo 1009.
Its entire body is byte-identical to the compact QQ tracer's corresponding
input; only the characteristic field in the header differs.

The run used the unchanged reviewed native engine, exact sparse linear
algebra option 2, one thread, and pair-selection parameter 32 with upstream
same-LCM boundary ties. Limits were 600 wall seconds and 4 GiB address space,
with core dumps disabled. It completed well within both limits.

The frozen 17-file `native-c4-qc/` archive preserves the exact source/subset,
extraction and conversion programs, input/provenance, row and QQ crosschecks,
launch hashes, complete stdout/stderr, outcome, and single-polynomial basis.
