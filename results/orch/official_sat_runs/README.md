# Completed searches on the exact official formula

Both runs used the unchanged, independently cross-checked LinkN2 encoding for 14 inputs, 24 gates, and 571 sampled rows. The CNF SHA-256 is `b877eccd57565a513b25c347eca5193429883cc32be15b30ebc0230dd2c084b0`. Its generator, inputs, metadata, and independent Lean comparison are preserved in `../official_sat/`.

- The default-preset screen ended after 240.84 seconds with exit 0 and UNKNOWN.
- The unsatisfiability-preset run ended after 1200.13 seconds with exit 0 and UNKNOWN.

These runs produced no candidate circuit and no completed UNSAT certificate. Their complete stdout and stderr are retained in `screen.log` and `long-unsat.log`, with commands and exact status metadata. Each run wrote a text LRAT prefix while searching. Both traces were renamed with `incomplete` in the filename; neither is an UNSAT certificate, and neither has been checked in Lean. The large incomplete traces remain in scratch during the job; their complete sizes and SHA-256 digests are recorded in `incomplete-trace-metadata.json` rather than committing hundreds of megabytes of incomplete proof data.

The later phase-only run and its positive controls are separate and were not complete when this archive was frozen. This checkpoint contains only the two completed UNKNOWN runs.
