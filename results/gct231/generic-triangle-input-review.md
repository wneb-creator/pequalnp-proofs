Independent generic triangle reduction/input review: PASS. Source transformation completed 2026-11-25T12:12:59Z; actual F1009 input review completed 12:15:44Z.

The 11-variable / 20-equation / 1,050-term JSON has SHA256 `8ded9d5e1145761185086336d90b749165633b5bad27a9c8de1677e32617eb48`. Independent Ryser expansion verifies all retained permanent coefficients. All 16 matrix entries agree with the reviewed 12-variable triangle chart after x=X, y=S*Y, z=T*Z and the stated parameter substitution. All preceding star and diagonal minors pull back to zero. The reverse assignment follows from the center-kernel equations and its diagonal vanishing; the saturation w*S*T=1 records precisely the assumed nonzero coordinates.

The actual F1009 sparse input SHA256 `bacc87ff96af321a3b15be71a0ed38ce4c80b2b7796481f18849bafadaccef54` has all 20 rows, variable order and primitive scalings verified against the JSON. No coefficients disappear modulo 1009.

Scope: necessary equations for the triangle stratum admitting a center-star kernel vector with all three coordinates nonzero. Edge weights 1,S,T remain explicit. Zero-coordinate kernel branches and sufficiency of omitted quartics are not asserted. This note certifies the transformation/input, not a solver outcome.

Complete exact sources/logs: scratch `triangle_generic/independent_review.py`, `independent-review.log`, `sparse_input_review.py`, `sparse-input-review.log`.

Review note saved 2026-11-25T12:19:39.017330+00:00.
