# Reduced triangle exact-QQ trace attempt

**Outcome: UNKNOWN_OUTPUT_FILE_SIZE_LIMIT.** The reviewed primitive-row QQ trace engine was interrupted by SIGXFSZ (return code -25) after 80.5414999129971 seconds when its algebraic trace reached the 256-MiB per-file limit. No final basis file was produced, no exact trace replay was completed, and no rational or complex contradiction is claimed.

The input is the independently reviewed necessary reduced triangle-stratum system: 12 variables, 26 equations, 686 terms. The rational coefficient and monomial rows are byte-identical to the independently checked F1009 input; only the characteristic field in the header changed to zero. Source SHA256 is `03a8aa61b2a83e2918457d922059fb481128cc02b3d1532c2cfcc11677ed0ce7`; exact QQ input SHA256 is `4c5ebcabb1bfab850ce72be671eb2b2e754151c55f208837a1e9549032f4f50c`.

The run used the existing independently reviewed serial primitive trace engine, pair-selection parameter 32, 600-second wall deadline, 2,048-MiB address-space cap, 256-MiB per-file cap, and disabled core dumps. It used no new engine implementation. `preflight.json` records exact source, runner, executable, and shared-library hashes; `elf-dynamic.log` records the executable's actual RUNPATH binding. The engine review is [here](../neogb-primitive/review/REVIEW.md).

The complete solver stdout/stderr log records 30 rounds with completed timings. The last completed round was degree 6, matrix 2,635 by 4,476, with 31 new elements and one zero reduction. The interrupted next round was degree 6, matrix 1,807 by 4,089; its log stops after the new-element counts and has no completed timing. There is no final basis-reduction or success summary.

The separate algebraic trace contains exactly 268,435,456 bytes, SHA256 `5599bfbfb6881818bc0c0f38222d2d2d85a8d405df1ee7308e7aa98fc32819d7`, and ends in a truncated record without a newline. A lossless gzip copy was verified against that raw hash; its sizes and hash are in `trace-preservation.json`. These large, unverified algebraic trace files remain in scratch and are intentionally excluded from this repository archive. They are neither process stdout/stderr nor a checked certificate.

This archive preserves all process stdout/stderr, complete runner and limit metadata, exact source and sparse input, the rational replay companion input, converter and runner source, preflight checks, and trace hash/preservation metadata. There are no engine binaries or vendor trees. The scratch invocation was:

```text
python3 gct231/sparse-engine/run_neogb_trace_primitive.py gct231/triangle-qq-trace-r1/triangle-qq.in gct231/triangle-qq-trace-r1/triangle-qq-run --seconds 600 --memory-mib 2048 --pairs 32 --output-mib 256
```

The finite-field unit result is separately preserved in `../triangle-native-r1/`. It is not promoted to a characteristic-zero result by this interrupted attempt. Independent outcome/archive review is recorded outside this frozen directory.
