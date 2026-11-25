# Full-star partial checkpoint: independent integrity review

The frozen five-file `star-center-r1-progress01/` archive passes exact coverage and SHA256 checks against manifest `80ffe4c0e3b614991f94b2268b75d227c5f1581a16b75ba194e7e812b119b73a`. Full gzip decompression yields 42011622 bytes and raw SHA256 `556b3c1775a6994e297e27645d9257f3dc7f32cbef180069be0682d1dab1b498`.

All 1003249 numeric terms in 445 nonempty rows parse correctly over F1009 with 18 variables, nonzero denominators and coefficients, nonnegative exponents, and no repeated monomial within a row. The first 31 generators match the reviewed input with identical exponent order and equal field coefficients. Negative input coefficient representatives are canonicalized modulo 1009 in the snapshot; byte equality was therefore not assumed. The remaining 414 rows have 999649 terms, within the one-million-term budget. All selected/available/omitted counters and source/engine hashes agree with metadata.

The saved snapshot is sequence 2, round 79. The log is an entire prefix captured during the ongoing run and extends beyond that snapshot to sequence 3, round 106, followed by an unfinished next row. Its preservation metadata correctly identifies this as partial progress, not a final basis or solver verdict. No ideal-membership claim for the appended rows was independently proved by this artifact check.

Standalone source/full log: `/tmp/oec/pequalnp-pilot-75/gct231/star_center_partial_review.py` and `star-center-partial-review.log`, completed 2026-11-25T11:54:53.950606+00:00. The initial reviewer attempt compared integer representatives literally; its diagnostic is retained, and the corrected field comparison passes. No live solver or original snapshot was touched.
