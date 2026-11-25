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

TIMING total=27.2 subagents=11 (interim)

- 2026-11-25 20:04:22 UTC: Pushed orchestration log commit 3fc5c46a to origin/pnp/swarm-L-meta-5012-orch.
- 2026-11-25 20:02:45 UTC: helper-3 first result: online and route accepted; tooling recovery in progress.
- 2026-11-25 20:02:48 UTC: helper-4 first result: online and route accepted; tooling recovery in progress.
- 2026-11-25 20:03:08 UTC: helper-5 first result: online and route accepted; tooling recovery in progress.
- 2026-11-25 20:03:19 UTC: helper-6 first result: online and route accepted; tooling recovery in progress.
- 2026-11-25 20:03:15 UTC: helper-7 first result: online and route accepted; tooling recovery in progress.
- 2026-11-25 20:03:19 UTC: helper-8 first result: online and route accepted; tooling recovery in progress.
- 2026-11-25 20:03:44 UTC: helper-9 first result: online and route accepted; tooling recovery in progress.
- 2026-11-25 20:04 UTC: Verified upstream L_meta_8725 proves full one-junk antecedent; directed complete routes to two-junk exclusion or witness.

- 2026-11-25 20:12:42 UTC: Root CrossStar support lemmas compiled with empty logs and passed independent review; copied exact reviewed bytes to results/swarm/CrossStar.lean.
- 2026-11-25 20:12:42 UTC: Independently fetched helper-3 dd38c5cd9 and compiled its TopForm-to-lift-fixed helper with empty logs. No full gap proof yet.
- 2026-11-25 20:12:42 UTC: Root SAT search: C6 at eight gates exact-two junk UNSAT; P8 at ten gates UNKNOWN after 240 seconds. Computational evidence only.
- 2026-11-25 20:16 UTC: Named lake build passed for the partial one-file integration; pushed b8e551bab to origin/pnp/swarm-L-meta-5012. Explicit PARTIAL bus message; no final posted theorem.
- 2026-11-25 20:19:25 UTC: First replan posted. Dropped unrestricted four-output color-split bound, naive promotion, and alias-only routes; reassigned helpers to full case closure and explicit degeneracies.
- 2026-11-25 20:20 UTC: Independent root builds passed for h2 7f14cd98, h6 93e19266, h7 d2d78892, and h9 d986fd84 support files. No full target theorem in any.
- 2026-11-25 20:22 UTC: Verified compact existing crossing-star exclusion source: DenseFinal5412.lean, 393985 bytes, saves 55006 bytes; source statement preserved, Lean compile passed.
- 2026-11-25 20:17 UTC: Root computational search found no two-junk size9 C6-plus-leaf circuit (UNSAT); P8, C8 and C6-plus-two-leaves runs timed out (UNKNOWN). No finite-search result is represented as a Lean certificate.
- 2026-11-25 20:26:41 UTC: Current proof coverage: normalization/lift and several geometry/replacement lemmas checked. Helper-3 reports a compiled restricted apart case forcing both flags, but full nested, mixed-color, singleton-factor and overlapping-factor closures still pending. No FINAL posted; no PR; lease not released.
