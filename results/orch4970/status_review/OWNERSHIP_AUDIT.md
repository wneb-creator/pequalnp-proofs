# Independent ownership and final preservation audit

This correction supersedes earlier claims in this review directory that the root held its own lease. Ownership was never established. No new proof work was performed during this audit.

The job began 2026-11-25 at14:00:30UTC. Raw desk responses contain:

| Response gap | Frozen terms issued_at (UTC) | Response received (UTC) | Holding |
| --- | --- | --- | --- |
| L-meta-2592 | 13:44:05.796 | approximately14:00:59 | 5 |
| L-meta-2583 | 13:59:02.364 | 14:52:34 | 5 |
| L-meta-2590 | 15:07:28.124 | 15:10:16 | 5 |
| L-meta-4970 | 15:22:04.914 | 15:39:27 | 5 |

Each response contains exactly: `you hold 5 gaps, the most one handle may hold at once; release one to get another`. The first two issue times even precede this job. The allowed retry returned the identical L4970 lease ID and identical issued_at; the comparison was performed without printing the ID.

The fetched join.txt says at lines70–71 that lease.terms are frozen when the lease is taken, and at lines92–94 that another=1 adds one more up to five. These responses therefore cannot establish a new allocation to this pilot. Successful beats only show that the shared-handle lease exists. The user's explicit existing-lease rule controls: stop after the one unchanged retry and do not release another pilot's lease. Root stopped work and renewal; no release occurred. Earlier unexplained HTTP410 responses are not evidence that this pilot owned those leases.

Three null replies were verified against the exact raw JSON: queue521, with respective hourly completion counts542/513/490 and estimates58/61/64minutes. FINAL-DESK-REPORT.md preserves their exact text.

Final preservation review: all additional working Lean files match reviewed snapshots, or are earlier subsets of reviewed extensions. The old ReadOne snapshot with global options remains a historical artifact; V2 is clean. OrCharge.prefix has one harmless unused Nat.add_zero warning. Existing global status explicitly says no complete proof/refutation, no proof PR, checker fault rather than acceptance, Floor17 unfinished, Floor18 terminated exit137, and SAT searches UNKNOWN. Raw solver/HTTP log whitespace is retained byte-for-byte; no Lean/Python/new-code whitespace issue was found. This is approval for artifact preservation only, not for a proof submission.
