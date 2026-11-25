# Direct path-C4 exact QQ trial

This is a conditional twelve-variable specialization of the full path chart: off-diagonal entries 02 and 13 are identically zero. The source has 31 equations, 973 terms and source SHA256 95581baa94cc80db67d9a6a6025dfd9de935ae13f825cac51ef52f88081b50e1. It is distinct from the earlier six-variable Witt-coordinate chart. The source JSON is preserved here.

The converter clears denominators and divides each polynomial by nonzero integer content. Independent coefficient-by-coefficient reconstruction of all 31 converted polynomials passed; exact source/input hashes and scaling factors are in direct-c4-qq.provenance.json and input-review.log.

The reviewed native SIMD/OpenMP engine ran exact QQ, sparse mode 2, one thread, all pairs per degree, with a 120-second wall cap, 122-second CPU soft cap, 3 GiB address-space cap and disabled core dumps. Result: UNKNOWN_TIME_LIMIT at 120.049 seconds; peak child RSS 704,504 KiB. Complete engine stdout/stderr are in direct-c4-qq-native1.log. Six rounds completed: 82 × 434, 555 × 1639, 2505 × 4918, the degree-5 matrix 3410 × 5152 (577 new rows, 48 zero reductions, 66.61 seconds), and the degree-4 matrices 189 × 761 and 562 × 1260. The run stopped during the degree-4 matrix 1049 × 1561. No basis file or mathematical verdict was produced. This is a bounded computational diagnostic, not a proof or refutation of the full gap or this chart.

The executable/library hashes are bound in direct-c4-qq-native1.result.json. Engine source/patch/provenance/control artifacts are preserved separately in ../sparse-native/. No vendor binary is included here. The run began after the root confirmed its 10:35:30 UTC lease renewal, expiry 10:55:29.889 UTC; see preflight.log.

Metadata-only correction on 2026-11-25: the progress description above was corrected against the preserved complete log. Original solver logs, source, exact input, provenance, and UNKNOWN result metadata are unchanged.
