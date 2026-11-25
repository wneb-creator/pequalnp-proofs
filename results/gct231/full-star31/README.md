# Checked full-star coefficient interface

`FullStar31Individual.lean` is the successful frozen artifact: 916 lines, 73,248 bytes, SHA256 d7bf606daad095450d7e07956c199a4c53a96aab17ad1d3f93196c405f3fe351. It compiles with Lean 4.36.0 and the pinned project Mathlib cache, using eight explicit Mathlib imports. Full compiler/profile output and resource metadata are included: exit 0 in 84.875 seconds, peak sampled process-group RSS 4,051,760 KiB.

It proves all 31 primitive-scaled quadratic, cubic and quartic coefficient equations from the formal constant-permanent identity for the normalized 18-parameter star matrix. Independent exact mapping, split-source and prefix reviews are preserved. These are necessary equations only; no contradiction or full posted theorem is proved.

The earlier FullStar31, FullStar31Split and FullStar31Lean sources are retained solely to reproduce the source-delta reviews. They are NOT the successful artifact: earlier attempts hit memory limits, and the final conjunction wrapper hit heartbeat/time limits. The successful file omits that redundant wrapper and retains every individual equation lemma unchanged.

The named project file remains the previously checked 624-line partial. Its latest checker verdict is REJECTED (no-theorem). No proof/refutation PR has been opened.
