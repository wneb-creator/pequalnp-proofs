# Interrupted triangle QQ trace: independent outcome and archive review

The frozen `triangle-qq-trace-r1/` archive passes exact 19-file coverage, SHA256, text-only and size checks against manifest `ce31e3a5f594cc94dccbdfc1f285c14afac166090abd548681312121bf7e1617` (70713 bytes including the manifest).

The source is identical to the reviewed triangle reduction. All 26 rational input rows were reconstructed exactly from the source, including primitive scaling; they agree byte-for-byte with the F1009 coefficient rows, with only the characteristic header changed. The rational replay companion represents those same rows. Preflight source/runner/executable/library bindings match the preserved and current reviewed files.

The outcome is `UNKNOWN_OUTPUT_FILE_SIZE_LIMIT`, SIGXFSZ return code −25, after 80.5414999129971 seconds under the recorded 600-second, 2048-MiB address-space and 256-MiB per-file limits. The complete log has 30 rounds with completed timings, ending at 2635×4476, then an unfinished 1807×4089 round. There is no final basis or completed replay.

Independent streaming byte checks verified the full 268435456-byte raw-trace hash, the gzip hash and its lossless decompression. The raw trace has 269716 newline characters and ends without a newline. No algebraic records were parsed or replayed. Both large files remain outside the repository archive, as documented.

The README correctly distinguishes this interrupted, unverified rational trace from the separate finite-field unit result and makes no rational or complex contradiction claim. No solver was rerun.

Independent source/full log: `/tmp/oec/pequalnp-pilot-75/gct231/triangle_qq_outcome_review.py` and `triangle-qq-outcome-review.log`, completed 2026-11-25T12:10:23.464797+00:00.
