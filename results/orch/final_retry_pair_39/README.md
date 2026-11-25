# Final retry of pair39

This separate checkpoint preserves the earlier frozen archives unchanged. It tests the remaining pair of right-side stars10 and12, keeping the other17 gates fixed and allowing a7-gate tail for total24. The retry adds a FULL circuit cone constraint: every primary and every nonoutput gate must have a reader. In particular the frozen prefix aggregate must be used, which was not required by the original local model.

The reviewed compact single-reader blocking rules and reviewed capacity bound are included. The capacity helper receives the FULL24-gate schema; tail ordering and prefix-aware blocking receive the sliced tail schema. A complete25-gate positive control passed before the600-second retry budget began. Every SAT candidate is validated on all16,384 assignments.

Any UNSAT result excludes only this strengthened model and MUST NOT change the earlier41/42 original-family exclusion count. It is external SAT evidence, not a Lean proof. No unrestricted lower bound follows.

Full solver stdout/stderr, controller output, exact commands, samples, decoder schemas, source snapshots/hashes, metadata and results are retained. CNF files are losslessly compressed as .cnf.gz; metadata records each original uncompressed SHA256. No proof certificate is claimed from the solver log alone.

Snapshot UTC: 2026-11-25T13:30:15.815974+00:00
State: UNSAT_STRENGTHENED_MODEL
