# Historical L-meta-2602 orchestration notes

Exact statement: /tmp/oec/pequalnp-pilot-71/statement.txt
Only parent holds lease and submits. Lease acquired 2026-11-25T05:50:41Z; expires 06:10:38Z; parent renews every 10 minutes.

Assigned: structural_proof direct counting; counterexample semantic/construction search; lemma_search reusable proofs; status_review reduction dependency review. Only PEqualNP.Defs and Mathlib allowed. Reductions live: 3, so currently cannot add another reduction.

Agents write independent findings under results/orch/lemmas and notify parent.

# L-meta-2962 orchestration notes

Assigned at 06:06:37 UTC. Exact statement /tmp/oec/pequalnp-pilot-71/statement-2962.txt. New lease confirmed 06:06:53, expires06:26:53. Old L2602 work remains paused. Four agents reassigned: core review, core structural, core charging, core counterexample.

## Checkpoint 2026-11-25T07:01:48.897840+00:00

The six-agent phase now separately tests shared maximal cores, an AND-budget model with free OR gates, and its OR-budget dual. The gap row remains posted with no reductions flag at 07:00 UTC. GateCharges and ProspectiveGateCut compile, but neither charge is proved and no reduction is eligible. The repository checker rejected the main partial for its missing final theorem, as expected.

## Checkpoint 2026-11-25T07:46Z

See REPORT.md for the current synthesis. Checked wrapper components have been pushed. The posted target remains unproved, and its row still lacks reduction eligibility. The reconnect preserved files but killed old solver/timer processes; those searches are interrupted with no verdict. The lease was renewed and its timer restarted; two Fano26 retries now use persistent status files.
