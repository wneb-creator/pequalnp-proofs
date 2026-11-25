# Reviewed finite-field checkpoint engine

The isolated native sparse-engine extension exports the original input generators followed by the current active basis rows at completed-round boundaries. These files are restart inputs containing polynomial consequences. They are not asserted to be Gröbner bases, membership certificates, or characteristic-zero proofs. Original generators remain present on restart, and the driver verifies their prefix against the original input.

Snapshots use a temporary file followed by an atomic rename and metadata publication. The last two complete snapshots are retained. The default minimum interval is 60 seconds, checked only at completed rounds; a long unfinished round can therefore leave an older checkpoint. The driver retains bounded wall time, address space, output size, CPU, and disabled core dumps. The arithmetic engine is unchanged apart from snapshot hooks.

All nine unit/nonunit/rational controls across primes 101, 1009, and 65537 passed. Tests include independent SymPy reduced bases, every appended snapshot polynomial as an original-ideal consequence, deterministic stop and resume, preservation of the root-generator prefix, and rejection of a mismatched base. An initial control harness incorrectly reused residue coefficients from prime 1009 for other primes; preflight rejected that input. The corrected harness uses the original rational coefficients. The initial harness and complete failure log are retained; no engine change was needed for the correction.

An independent review checked all 14 provenance hashes, all 54 retained snapshots, 126 appended rows, all 21 completed or resumed control bases, and every one of the 2450 terms in the grouped full-star input. The grouped order is ordinary degree-reverse-lexicographic order with the variables grouped by basis directions A, B, C; it is not a new block-elimination order.

The frozen `checkpoint-engine/` archive has 240 files and manifest SHA256 `54b11bbfccf1ec1f07f078380a03a3515c7656e44249a4cc18b79cf4a1176416`. It contains the extension, generator, wrapper, bounded runner, full controls, provenance, and grouped input. The upstream source and binary are identified by provenance hashes and are not copied into this archive. The independent five-file `checkpoint-review/` archive has manifest SHA256 `1b89c8632a03d9a50105dc161341e7a54faa72a4c99953dc1d7c738ad597b70d`.

A longer full-star run is recorded separately when complete. This tooling archive makes no claim about that run's outcome.
