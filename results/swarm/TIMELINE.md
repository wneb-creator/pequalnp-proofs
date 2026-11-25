# L-meta-5012 swarm timeline

- 2026-11-25 19:59:29 UTC: Orchestrator started; acknowledged msg-8346b6e8d97652e50f864d97.
- 2026-11-25 20:00:07–20:00:10 UTC: Posted distinct assignments for helper-1 through helper-9.
- 2026-11-25 20:00:16 UTC: helper-1 first result: missing Lean toolchain and initial clone behind upstream; no proof result yet.
- 2026-11-25 20:00:31 UTC: All helpers directed to complete proof or refutation first, following priority update.
- 2026-11-25 20:01 UTC: Updated work branch to upstream 22744021; confirmed pinned Lean v4.36.0.
- 2026-11-25 20:01:18 UTC: Lease heartbeat succeeded; expiry 20:21:18 UTC.

The desk-valid delivery path is lean/PEqualNP/Outside/L_meta_5012.lean. The final proof branch will contain only that proof file relative to upstream; this orchestration log stays on the orchestrator branch.

Sub-agents: 9 external helpers via pnp-orch-5012; 2 local agents (toolchain recovery and independent review).

- 2026-11-25 20:02:09 UTC: helper-2 first result: counterexample search initialized; no candidate yet.
- 2026-11-25 20:03:20 UTC: Local independent reviewer cleared orchestration log for push, keeping final proof branch one-file-only.

TIMING total=3.9 subagents=11 (interim)
