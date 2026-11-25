# L-meta-2592 orchestration notes

Only root holds or renews the lease. Each agent writes its own strategy note under results/orch/lemmas; read these notes before repeating a search. Never alter the final Lean file concurrently.

Goal: no fan-in-two circuit with size <= 19 containing a NOT gate computes the Petersen edge function. Exact statement: /tmp/oec/pequalnp-pilot-128/statement.txt. Allowed project module: PEqualNP.Defs. Three reductions already live.

Strategies: root coordinates and validates; checker_audit checks intake; theory studies lower bounds; counterexample searches small circuits; reductions studies existing cuts/lemmas; semantics checks circuit definitions and edge cases.

## 2026-11-25T14:37:55.755174+00:00 status

- Existing binary floor15+NOT-count<=size excludes >=5 NOT. Copied checked partial awaits Lean validation. The held gap remains unresolved for1..4NOT.
- All3 reductions already live; no new reduction slot.
- Exact existing LinkN SAT encoding includes proved normalization. A30boundary-row19-gate SAT model has884 full-table errors, so it is not a counterexample. Full-row/CEGAR search continues.
- Required Lean and warm cache were absent. Installed pinnedLean4.36.0; full Mathlib unpack exceeded7.9GiB overlay. Restoring only needed dependency closure, without Mathlib source compilation or checker weakening.
- Sub-agents: checker_audit, theory, counterexample, reductions, semantics, sat_search. Only root owns desk calls; heartbeat every5minutes.

## Active step switched to L-meta-2583 at2026-11-25T14:43:06Z

L-meta-2592 lease was lost and all work archived in610af6d. Only work on L-meta-2583 now. Exact statement /tmp/oec/pequalnp-pilot-128/statement-2583.txt, desk desk-after-410.json. New own lease expires15:03:06Z; root alone renews it. Reductions are CLOSED for this step.

## Final stop

The recovery request and single permitted retry returned the same pre-existing L-meta-2590 lease with holding=5. Exact desk message: you hold 5 gaps, the most one handle may hold at once; release one to get another. The user explicitly requires stopping in this case. No work, explicit renewal, or release was performed on that lease. The two earlier returned leases had also been issued before our requests, so their ownership was not independently established. All partial work and diagnostics are preserved; no complete theorem or refutation has been proved, and no PR was opened.
