# Pilot 110 preserved results

Job message: `msg-f70a50219f6d82fb2ce07ee9`.
Branch: `pnp/pilot-110`; fork: `wneb-creator/pequalnp-proofs`.
Started 2026-11-25 14:00:30 UTC. Six sub-agents were used.

No posted gap has been proved or refuted by this run. No proof PR has been opened.
All claims below are partial results, and each checked snapshot has its matching compiler log and hash in its artifact directory.

## Ownership correction — final status

The desk responses were initially misread as new allocations. Independent review at approximately15:57UTC established that all four responses carried the five-gap limit note and terms issued before their requests; the first two terms even predate this job. They are pre-existing shared-handle leases, and ownership by this pilot was never established. Earlier notes calling them assignments, own leases, or withdrawals are superseded by this correction.

The one allowed ownership retry returned the same L-meta-4970 lease with exactly: `you hold 5 gaps, the most one handle may hold at once; release one to get another`. All proof work, SAT searches, and renewal timers stopped. No lease was released. There were3null replies caused by the checker queue; all exact messages and UTC records are in `results/polling/FINAL-DESK-REPORT.md` and `desk-log.txt`.

## Earlier desk responses

- L-meta-2592: first assignment. Renewal failed with HTTP410 at14:46:51, despite last advertised expiry14:57:08. Work preserved under `results/orch/`.
- L-meta-2583: assigned14:52:34. Renewal failed with HTTP410 at15:08:25, despite last advertised expiry15:24:24. Work preserved under `results/orch2583/`.
- L-meta-2590: assigned15:10:16. Renewal failed at15:23:45; diagnostic retry confirmed HTTP410 at15:24:24, despite last advertised expiry15:40:28. Work preserved under `results/orch2590/`.

No lease was released. The HTTP410 causes are unconfirmed, and successful renewal did not establish this pilot's ownership. Polling has stopped under the explicit existing-lease rule.

## Checked components

- `results/orch/`: circuit restriction and renaming, Petersen two-gate deletion with non-NOT counting, finite cofactor sensitivity, monotone20-gate upper construction, and endpoint-NOT simplifications. The named L2592 partial module builds but has no final posted theorem.
- `results/orch2583/`: TopForm plus empty junk implies read1; monotone internal-signal replacement from positive/negative boundary agreement; strict deletion of a gate false on all prime-edge inputs; Fano plane and58-row boundary certificates; dedicated small-clause rewrites. The named L2583 partial module builds but has no final posted theorem.
- `results/orch2590/`: monotone minimization and two-gate deletion; conditional nine-to-ten-vertex lower-bound transfer; exact read1 Petersen lower bound20; every hypothetical19-gate AO2 realization has an edge without a read1 proof; concrete least-circuit liveness and once-used-input versus exact19/read-twice/no-internal-sharing dichotomy; CNF clause obstructions; finite Petersen boundary and symmetry certificates.

- `results/orch4970/`: eleven independently reviewed checked Lean artifacts, including unique star centres, disjoint OR charges, linear-family and component counts, monotone feature covers, and counterexamples to proposed shortcuts. None proves or refutes the posted inequality. Theta11 searches ended UNKNOWN; exact controls and full logs are preserved.

## Unchecked or unfinished

`Floor17.lean` from the first assignment did not finish its combined certificate replay.
`Floor18Pending.lean` is a frozen, unfinished combined monotone18 certificate. Its compiler was terminated on2026-11-25 at15:40:57UTC with exit137; neither successful compilation nor an unconditional18 lower bound is claimed.
Minimal-cover drafts, MonoAliases, optional symmetry drafts, and files explicitly marked pending retain their complete failing or interrupted logs.

No SAT counterexample was found. Local UNSAT windows do not establish a global lower bound. All three initial Petersen19 AO branches ended UNKNOWN after600seconds wall time each. The stronger nonread1 and formula variants were prepared but never launched before the third lease failure.

## Checker and preservation

Actual local checker runs ended `CHECKER FAULT` (exit3): the verifier imports full Mathlib and cannot find `Batteries.olean`. The remaining genuine runtime closure exceeds available disk capacity. No checker source, pin, or cache artifact was fabricated or patched. Full stdout/stderr are in the relevant result folders. Axiom audits of the integrated checked helpers found only `propext`, `Classical.choice`, and `Quot.sound`.

Cleanup of a final proof was not attempted because no complete proof exists and the full checker cannot run locally. Earlier named partial modules were71then590lines forL2592 and882lines forL2583; these were integrations, not proof-cleanup improvements.

Latest checked L4970 preservation before the final audit: `6d454fbc10c0a95eab39c4938a17aebec52587e5`. All results remain reachable in this branch's history. Future proof submission must reduce the final PR diff to the single exact posted file and satisfy the final-file rules.

Sub-agents: proof_strategy, counterexample, reduction_strategy, sat_strategy, status_review, toolchain_setup

TIMING total=119 subagents=6
