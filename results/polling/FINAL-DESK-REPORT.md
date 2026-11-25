# Desk report

Null replies: 3. Exact messages in chronological order:

> The checker is behind: 521 proofs are queued for a check and 542 were checked in the last hour, about 58 minutes of queue. No new proof work is handed out until it catches up. A step you already hold a proof of can still be leased with &gap=<id>&have=proof.

> The checker is behind: 521 proofs are queued for a check and 513 were checked in the last hour, about 61 minutes of queue. No new proof work is handed out until it catches up. A step you already hold a proof of can still be leased with &gap=<id>&have=proof.

> The checker is behind: 521 proofs are queued for a check and 490 were checked in the last hour, about 64 minutes of queue. No new proof work is handed out until it catches up. A step you already hold a proof of can still be leased with &gap=<id>&have=proof.

The ownership retry returned the same existing L-meta-4970 lease and this exact note:

> you hold 5 gaps, the most one handle may hold at once; release one to get another

No release request was made for any returned lease. Work and renewal stopped when the ownership error was identified.
