# L-meta-650 research checkpoint

The posted63-gate claim is not proved or refuted. No proof PR has been opened. This branch preserves independently reviewed Lean components, search sources, complete diagnostics and explicitly incorrect candidates.

## Checked components

| File under lemmas/ | What it proves |
| --- | --- |
| lean_baseline/BaselineCorrect2.lean | An explicit64-gate monotone circuit computes the exact posted52-edge function on every input. |
| verification/FiniteVerification.lean | A monotone≤63-gate candidate passing the specified finite boundary tests proves the exact posted statement. It supplies no candidate. |
| lean_baseline/BipartiteBasis.lean | Generic soundness of edge positives and independent-extension negatives for monotone bipartite functions. |
| reduction_analysis/SpecializedLiftFast.lean | Exact smaller-core completion routes, including a≤28-gate six-row core. |
| reduction_analysis/PairTapCompletion.lean | A≤29-gate exact six-row core with the specified conditional pair tap extends to63 gates:29+4+30. |
| reduction_analysis/AttachFull.lean | The two-gate attachment half of the existing residual/tap reduction. |
| algebra_strategy/FourRowLower.lean | The designated four-row core needs at least19 gates; its proposed18-gate route is impossible. Research imports. |
| reduction_analysis/SixLeafCycleLower.lean | The designated three-row subproblem with six private leaves needs at least14 gates. Research imports. |
| reduction_analysis/SingletonDirtySemantic.lean | A semantic replacement under explicit one-unsafe-AND form hypotheses; no global normalization or size bound. |

Further checked monotonicity, geometry, lifting, Boolean identities and normalization lemmas are recorded in NOTES.md and validation.txt. Research imports are not eligible for the final proof file without inlining permitted dependencies. Every quoted compiler success applies only to its named component. The repository checker has not accepted the posted target.

## Search status

The best preserved28-gate six-row approximation computes the24 required edges plus four unwanted edges. It fails17 maximal-negative tests and accepts255 additional inputs out of131072. It is not a witness. The repairs from25 to23 to17 failed tests strictly improve the represented function. The defective13-gate three-row cone cannot be repaired in isolation, by the checked14-gate lower bound.

Active construction routes are exact28-gate core synthesis, joint exact-core/conditional-tap synthesis, and full-plane63-gate guarded merges. Full boundary verification remains mandatory. SAT timeouts are UNKNOWN; local UNSAT results apply only to explicitly bounded neighborhoods.

Large direct finite-set kernel computations reached12–13GB and were stopped. The small symbolic-evaluation calibration passed; unfinished benchmark files are not checked proofs. Complete diagnostics are retained in snapshots.

## Administration

Special check L-meta-1035 returned not_open; the response did not identify whether it was checked or stood down. Three initial hard-desk requests returned null with the exact note: no step is free that you have not already looked at and handed back in the last hour (2); new steps are posted through the day, ask again in a few minutes. L-meta-650 was assigned on2026-11-25 at02:14:27 UTC. Only its lease is renewed by this job.

An optional authenticated GitHub API read returned401. VENDOR-LIMITATION git-auth-401 was reported; no alternate credentials were used. Git fetch and preservation pushes succeeded.

Sub-agents: algebra_strategy, circuit_search, lean_baseline, lower_bound, reduction_analysis, status_review (6 distinct agents).

TIMING total=94.3 subagents=6 (checkpoint at 2026-11-25T03:35:27.477097+00:00; work continues).

Job ID: msg-e98796d0d0ad050188abca1f.
