# Pilot121 checkpoint after third lease failure

Acknowledged job message msg-61f9b55d28c5586ddb66ac34.

Paused 2026-11-25T15:24:23.764473+00:00 after three HTTP410 lease failures and two assignment retries. After pushing this checkpoint, request another assignment under the later410-specific instruction. No full posted theorem or Lean-checked refutation was completed. No PR was opened. No lease was released by this pilot; all three returned410 while renewal timestamps still showed future expiry. The records do not establish another pilot's ownership or the reason for the lease failures.

## Desk record

Three gap responses, zero nulls: L-meta-2592, L-meta-2583, then L-meta-2590. All requests included another=1 and hard=1. Desk responses and renewal log with lease-control credentials redacted, and each error's complete HTTP headers/body are preserved in this folder. Latest410 occurred15:21:28UTC after successful15:19:36 renewal with expiry15:39:36UTC. Exact message:

> no such live lease: it expired or was released. Ask /desk/next again.

A final read-only GitHub search could not confirm closure: HTTP422 reported the named upstream repository could not be searched. Full response preserved in pr-2590-final.json. No credential/authentication fallback was attempted.

The special L-meta-1035 step was not assigned. The saved public feed and local exact-path history did not establish its current status; no refutation claim is made.

## Checked partials and limitations

- L-meta-2592: named file lean/PEqualNP/Outside/L_meta_2592.lean contains checked helpers, including the15-non-NOT bound and candidate NOT-count consequences. Named lake build passed. It does not declare a proof of the full posted statement. 3218 lines.
- L-meta-2583: compiled components include exact-size read-one star constructions, OR surgery/normal forms, critical-row correctness criteria, and order-three read-one lower bounds. No proof of the unrestricted normalization statement.
- L-meta-2590: ReadOnePetersen2590.lean compiles and proves20 gates under explicit IsAO2 and joint IsReadK1 hypotheses. Independently reviewed. 1447 lines. No full L_meta_2590.lean target file was created.
- Every newly preserved2590 draft except ReadOnePetersen2590 is UNCOMPILED (failed, never run, or interrupted). Old leftover2592 drafts are obsolete UNVERIFIED snapshots; stronger checked components were preserved earlier.
- Local tools/check-lean.mjs was not run for any full posted theorem, because none was completed. No ACCEPTED verdict is claimed.
- No cleanup pass was performed; the prerequisite full build plus local-checker acceptance was not met. The checked read-one file remains1447 lines before/after; the named2592 helper file remains3218 lines.

## Search outcome

All1024 assignments validate the20-gate Petersen positive control. The19-gate stochastic search performed1,001,837,447 proposals in192 seconds; its best candidate misses two edges and is wrong on22 assignments, so it is not a counterexample. The SAT run was terminated on410 and returned no SAT/UNSAT verdict. Complete source, queries, controls, logs and stop timestamps are in search2590/ and sat2590/. Earlier search archives are also retained. All searches and builds were terminated.

Sub-agents: circuit_search, gate_elimination, not_elimination, proof_route, status_review, toolchain_setup
Checkpoint measurement
TIMING total=69.2 subagents=6

Checker status at this checkpoint: not run; full posted theorem unproved.
