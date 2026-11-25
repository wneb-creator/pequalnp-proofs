Independent completed generic triangle r1 outcomes: PASS at 2026-11-25T12:21:11Z.

The F1009 run produced the actual unit basis [1], exit 0, in 2.234835424 seconds with 22,652 KiB peak RSS. Its log has 78 pair rounds followed by final reduction. The final checkpoint preserves all 20 original polynomials modulo 1009 and appends exactly 1. Engine/basis/input hashes agree with recorded metadata.

The traced QQ run is UNKNOWN_OUTPUT_FILE_SIZE_LIMIT, SIGXFSZ −25, after 4.798031911 seconds. Its log has 15 completed timed rounds and unfinished matrix 1328×2094. The trace is exactly 67,108,864 bytes, SHA256 `ad5f235a6510f6fc90a768609e99a0133d0c05a25110daf127517299ae9df207`, and ends without a newline. No basis or algebraic replay was produced. The compact adapter binary and library search path match the recorded engine.

The separate untraced QQ r1 is UNKNOWN_TIME_LIMIT after 120.061819876 seconds, with 745,384 KiB peak RSS under 120 seconds / 1,024 MiB. Input and reviewed qqfix binary bindings match; no basis exists. Both QQ inputs and the replay companion were independently reconstructed over QQ. The signed input rows are identical to the reviewed F1009 rows except for the characteristic header.

No characteristic-zero contradiction is claimed. The subsequent r2 run is outside this review. No solver was rerun or trace algebra replayed. Full checker/log: scratch `triangle_generic/outcome_review.py`, `outcome-review.log`. The initial FF/traced-only log is retained separately.

Saved 2026-11-25T12:21:39.875122+00:00
