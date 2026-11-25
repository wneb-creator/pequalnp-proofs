# First grouped full-star checkpoint attempt

The reviewed finite-field engine was run on all 31 full-star equations, with variable priority grouped by the three basis directions. Its configured limits were 1800 seconds, 4 GiB, one thread, pair-selection parameter 32, and at least 60 seconds between periodic snapshots.

It stopped safely with `UNKNOWN_CHECKPOINT_FAILURE` after 61.403535 seconds, maximum RSS 409428 KiB. The first periodic export exceeded the validated import limit of ten million terms or one hundred thousand generators. No final basis or mathematical verdict was produced. The sole published snapshot is the initial original-generators-plus-initial-basis state, not the later active basis.

The complete logs, launch/result metadata, and initial snapshot are preserved in the adjacent six-file archive. A separately reviewed export-only revision will retain a bounded subset of derived rows while always retaining the original generators; it leaves the solver's live basis unchanged. This record does not claim a result from that later revision.
