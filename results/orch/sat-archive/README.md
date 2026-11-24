# L-meta-5112 SAT search archive

Snapshot UTC: 2026-11-24T22:08:29.327034+00:00.

These are unsuccessful search artifacts, not a proof or a refutation. No completed SAT witness or UNSAT certificate was obtained before this snapshot. The final result submitted by the root agent is tracked separately.

Generator sources, metadata, and complete stdout/stderr streams are preserved here. Logs of any still-running processes are complete through the snapshot time. `MANIFEST.json` records SHA-256 hashes and sizes. CNF files are reproducible from the generators and are represented by hashes; incomplete large LRAT traces remain excluded and explicitly unproven.

Key generators:

- `complete24.py`: exactly 14 arbitrary gates, Fin28 selectors including default zero, 24 selected original bit rows; no normalization assumptions.
- `complete.py`: analogous 58-row encoding.
- `free_and.py`: at most 10 OR gates with arbitrary conjunctions as operands and final output.
- `free_and_closed.py`: canonical conjunction closure preserving all positive rows and decreasing negative rows; stronger normalization proof not completed here.
- Other variants impose additional minimality or symmetry conditions and were used only for witness search. An UNSAT answer from those variants alone would not establish a refutation.

Every solver run either reached its time limit, was stopped for CPU availability, or was still active at snapshot time. Full logs record the actual status.

All remaining solver processes were terminated by root request after the accepted reduction was ready. No process remains active, and no SAT/UNSAT result was obtained. Exit statuses and shell termination messages are recorded in `termination-summary.json`.
