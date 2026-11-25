# Resource-capped exact-QQ C4 follow-ups

Both runs ended **UNKNOWN_OUTPUT_FILE_SIZE_LIMIT** (SIGXFSZ), with no basis, unit, or nonexistence verdict. Complete stdout/stderr, run parameters/binary hashes, exact companion input, and omitted-trace hashes are preserved.

- Compact baseline: 900-second wall cap, 4 GiB address-space cap, 2 GiB per-output-file cap, one thread, 32 pairs per batch. It stopped after 716.184 seconds at its trace cap.
- Primitive-row variant: 600-second wall cap, 4 GiB address-space cap, 512 MiB per-output-file cap, one thread, 32 pairs per batch. It stopped after 169.576 seconds at its trace cap.

The separate comparison uses the earlier compact 512 MiB run and the primitive 512 MiB run. Both completed 31 rounds and emitted 808 complete output polynomial snapshots; every corresponding polynomial payload is byte-identical. Largest complete coefficient lengths fell from 4,859 to 3,240 decimal digits, but this yielded no additional completed rounds before the same trace cap. The runs overlapped other work, so wall-time differences are not a controlled speed benchmark.

All inputs describe only the fixed-C4 support family's quadratic and cubic necessary equations. Modular unit evidence remains distinct from these unsuccessful rational attempts. Large failed traces remain in scratch and are intentionally excluded; no prefix is represented as a proof. Reviewed adapter sources are in the sibling neogb-compact and neogb-primitive archives.
