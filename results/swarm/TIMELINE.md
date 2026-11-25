# L-meta-1890 swarm timeline

Earlier helper findings predate the orchestrator start. Helper claims below were not yet independently checked unless explicitly stated.

- 2026-11-25T20:59:33Z — Helper 1 reported the missing-input witness argument for surjectivity. (Bus message 1379; helper report.)
- 2026-11-25T20:59:55Z — Helper 3 reported monotone seed elimination and identified NOT gates as the remaining obstacle. (Bus message 1384; helper report.)
- 2026-11-25T21:00:13Z — Helper 5 reported size-preserving input relabeling to the identity map. (Bus message 1389; helper report.)
- 2026-11-25T21:00:44Z — Orchestrator started; acknowledged msg-42788a4cb2241de859e959a2.
- 2026-11-25T21:01:28Z — Nine distinct full-proof/refutation assignments posted to helpers 1–9 within one minute of start.
- 2026-11-25T21:01:29Z — Helper 7 reported an independent-set enumeration giving independence number four and cover number six. (Bus message 1410; helper report.)
- 2026-11-25T21:02:00Z — Fast-forwarded work branch to upstream main e716431b307e55f4b6521ec8452101e7a9959e57.
- 2026-11-25T21:02:32Z — Helper 9 reported the updated namespace rule and audited constant/missing-wire semantics. (Bus message 1445; helper report.)
- 2026-11-25T21:03:18Z — Completed pinned Mathlib cache fetch without building Mathlib from source.
- 2026-11-25T21:03:46Z — Helper 2 reported a 20-gate baseline verified computationally on all 1024 inputs. (Bus message 1471; helper report.)
- 2026-11-25T21:04:13Z — PEqualNP.Defs build passed (5147 jobs).
- 2026-11-25T21:05:52Z — Helper 6 reported that complement and Shannon searches were running; no candidate. (Bus message 1512; helper report.)
- 2026-11-25T21:06:25Z — Helper 8 identified existing NOT-capable LRAT encodings and generators. (Bus message 1527; helper report.)
- 2026-11-25T21:06:38Z — Helper 4 reported that all edge-partition star formulas need at least 20 gates. (Bus message 1533; helper report.)

## Delivery constraints

The authoritative desk filename is `lean/PEqualNP/Outside/L_meta_1890.lean`.
The swarm-specific instruction governs delivery: final branch `pnp/swarm-L-meta-1890`; the Mac opens the PR. No lease acquisition or release.
Timeline and validation records stay on the orchestrator branch so a proof delivery can have exactly one added Lean file.

## Measurement

Sub-agents: nine external bus helpers; two local agents for toolchain/certificate support and independent review.
TIMING total=in_progress subagents=11
