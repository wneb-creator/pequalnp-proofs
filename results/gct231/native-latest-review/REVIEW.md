# Native full-star batching and C4 quadratic/cubic archive review

Reviewer: global_normal_form, 2026-11-25 UTC. Verdict: PASS for archive
integrity, equation selection/conversion, and diagnostic scope. No solver
was run and neither archive was modified.

The seven-file `native-star-b32-r2` archive has exact manifest coverage and
all hashes match manifest
`8e7952e8fc121c96dea4006f4bc6eae2d4f92cda1dc844f31172b79494829f44`.
Its input is byte-identical to the prior reviewed full-star input. The outcome
is UNKNOWN_TIME_LIMIT at 600.085482908 seconds, peak RSS 1,645,844 KiB, with
126 completed pair rounds and no basis. The last completed round and the
maximum reported selection of 35 match the adjacent note. This is only a
finite-field diagnostic.

The seventeen-file `native-c4-qc` archive has exact coverage and all hashes
match manifest
`f1be8e19526bbf50bdde4baf975b2c1e9f910827e5e84d57872741e2886f72d4`.
The extracted equations are exactly the original ordered rows whose three
parameter exponents sum to two or three: six quadratic and ten cubic rows.
All other chart data are unchanged; the source hash matches. The twelve
unknowns and all 492 sparse terms were parsed independently. Every actual
row equals its exact primitive rational source polynomial, all positive
content/denominator factors match and are invertible modulo 1009, and no
modular term was dropped.

The modular input body is byte-identical to the corresponding compact QQ
trace input; only the characteristic changes from 1009 to zero. This checks
that both experiments address the same necessary equations; it does not
transfer a finite-field verdict to characteristic zero.

The native result is exactly [1] over F1009, exit zero, in 17.229024379
seconds, peak RSS 81,300 KiB. The complete log has 144 pair-processing rounds
and one final basis reduction (145 displayed reduction rows in total).
Launch/input/binary/library/output hashes and one-thread/4-GiB parameters
match the metadata. The basis claim remains a finite-field solver result,
not an independently checked ideal-membership certificate, QQ contradiction,
or Lean theorem. The adjacent note accurately states those limits.

The independent checker and complete diagnostics are `check.py` and
`check.log` in this directory.
