# Active state: recovery polling

Do not end the task yet. The user requires four-minute desk polling after null replies, within the overall job budget. No live lease is currently held by this job.

- Job began2026-11-25 07:02:59UTC; overall six-hour deadline13:02:59UTC. Ninety-minute minimum effort already exceeded. Current update2026-11-25T09:05:47.960889+00:00.
- Poller PID20197, execsession37580. Script /tmp/oec/pequalnp-pilot-75/poller.py; output poller-process.log; PID file poller.pid. Sleeps in at-most30second pieces; exact curl-s next URL uses handle=wneb-creator&another=1&hard=1 every240seconds.
- Latest recovery response09:03:10 gapnull; nullcount8; next due09:07:10. Initial six nulls referred to4 recent-handback steps, then3, now2. Exact messages andUTC times are in desk-log.txt.
- Poller stops on assignment, error, stop-poller flag, or job deadline. ALWAYS inspect poller-assigned.txt / poller-error.txt / poller-complete.txt before issuing a new request. Raw recovery responses are desk-recovery-NN.json; future assigned responses may include private lease IDs—never print those. Check process STAT after environment refresh; PID presence alone can mean zombie.
- On assignment: inspect only safe gap metadata and lease expiry; renew ONLY the new supplied lease. Restart a heartbeat configured to read that new recovery response. The existing heartbeat.py reads old desk-first.json and MUST NOT be reused unchanged. stop-heartbeat currently exists and old heartbeatPID13568 exited.

## Prior assigned gap and preserved result

L-meta-2448 was assigned07:04:37. Its timer renewal08:23:23 advertised expiry08:43:23, but renewal08:31:23 returned no-such-live-lease. The timer made the mandatory same-call curl-si retry once and receivedHTTP410, then stopped. Root discovered this08:32:51. All compiled artifacts had already been pushed. No release request was made because the lease was already unavailable. Explicit recovery request08:35:08 returnedgapnull and began the current polling phase.

Public read-only review found no accepted proof or withdrawal explaining410; another pilot's PR13028 was refused for no theorem. See read-only-status.md. Do not touch that PR or another pilot's leases. Work on L2448 stopped after410; only archival/status work followed.

- Repository /workspace/pequalnp-proofs, authorized branchpnp/pilot-75; push only origin fork. Latest pushed before this notea2e40148ebce58746142fc4686761c65005a1715. No PR opened.
- Named partial lean/PEqualNP/Outside/L_meta_2448.lean is9440lines/476959bytes, SHA72c333a765a480d06fbae71d6afa211f788c15109a7f201eae70da7a1f798890. Only Mathlib+PEqualNP.Defs imports.
- Strongest helper constructs a minimum star-profile circuit under explicit extra premises: supplied publicminimum AO2 circuit, correct graph function, and junk.card<=1. Full posted theorem remains UNPROVED.
- Named build12 passes. Local checker12: REJECTED(no-theorem), because the unconditional main declaration is absent. Full logs are in results/orch/. Final helper uses only standard3axioms. Independent provenance/scope/format/axiom reviews passed.
- Old2078line helper collection is preserved as results/orch/lemmas/IntegratedRepairs.lean and earlier branch history. Standalone source/logs/provenance under results/orch/standalone/. All143 older lemmas audited too.
- Final finite archive137artifacts independently reviewed; freeOR archive14runs independently reconstructed. Timeouts are UNKNOWN. No solver processes remain.
- HANDOFF.md and per-strategy notes explain the remaining sharing/boundary inequality, checked local obstructions, and why essential-star/minimumAND/all-neighborhood extraction routes fail. None refutes the full gap.
- All three reduction slots were occupied; no extra reduction submitted.

## Tools and team

Prepend /tmp/oec/pequalnp-pilot-75/lean-tools/lean-4.36.0-linux/bin toPATH. Full pinned Mathlib cache fetched; never lake update or build Mathlib from source. Checker needs PEQUALNP_REAL_LAKE set to that lake binary and PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-75/build-state.

Seven distinct subagents used, all currently completed: status_review, structural_proof, library_route, finite_cases, lean_setup, global_normal_form, fresh_main_proof. Reuse agents via followup_task; send_message alone does not wake idle agents.

If a different gap is assigned, work only that new posted goal under the remaining job time and keep one lease. Before any successful proof PR, its final diff must add exactly its one named Lean file; prior partials/results remain recoverable in pushed history. Do not submit the current helper-only file.

At final completion preserve the complete desk log, null count/exact messages, final timing and checker output; stop poller/heartbeat; release only any then-live OWN lease. Final must acknowledge msg-8f0f42bb760e4ee78f16c6cd, print Sub-agents and TIMING total=<min> subagents=7, and end with gap/pr/checker lines.
