# L-meta-650 research checkpoint

The posted claim is not proved or refuted. No proof PR has been opened, and the repository checker has not accepted the target. This branch preserves independently reviewed Lean components, research programs, complete diagnostics and explicitly incorrect candidates.

## Checked components

| File under lemmas/ | What it proves |
| --- | --- |
| lean_baseline/BaselineCorrect2.lean | An explicit circuit with 64 gates computes the exact posted function on every input. |
| lean_baseline/FullPairAugment.lean | A circuit with 60 gates computes the 52 required edges plus six extra edges. It is not a target witness. |
| lower_bound/AugmentedCandidate17.lean | A circuit with 28 gates computes the 24 core edges plus four extra edges. |
| verification/CertifiedAugmented17.lean | The same augmented circuit is verified by finite DNF certificates for all input lists of length 17. |
| reduction_analysis/DNFVerifierMono.lean | A sound gate-by-gate DNF certificate checker, including every wire, false-default references and Monotone2. |
| verification/FiniteVerification.lean | A candidate passing the stated finite boundary checks suffices for the exact posted target. No candidate is supplied. |
| reduction_analysis/SpecializedLiftFast.lean | Smaller-core completion routes, including a circuit with at most 28 gates for the six-row core. |
| reduction_analysis/NineRowCompletion.lean | A nine-row circuit with at most 43 gates extends to the posted 63-gate target. |
| reduction_analysis/PairTapCompletionWeak.lean | A core with at most 29 gates and the conditional pair tap extends to 63 gates. |
| reduction_analysis/TripleTapCompletion.lean | A core with at most 30 gates and the conditional triple tap extends to 63 gates. |
| reduction_analysis/NineTapCompletion.lean | A circuit with at most 17 gates computing two stars and nine cross-OR taps extends to 63 gates. |
| reduction_analysis/AttachFull.lean | The two-gate attachment half of the existing full residual/tap reduction. |
| algebra_strategy/FourRowLower.lean | The designated four-row core needs at least 19 gates. Research imports. |
| reduction_analysis/SixLeafCycleLower.lean | The designated three-row subproblem with six private leaves needs at least 14 gates. Research imports. |
| algebra_strategy/FreeCrossPairLower.lean | The two-owner function cannot use eight additional gates with all nine fixed free cross-OR features. Research imports. |

Further checked monotonicity, geometry, lifting and normalization lemmas are recorded in NOTES.md and validation.txt. Research imports are not eligible for the final file without permitted inlining. The fixed-feature lower bound does not automatically exclude the more general interleaved multioutput completion theorem.

## Current search and verification status

The best preserved bare six-row approximation fails 17 maximal-negative tests and accepts 255 extra assignments among 131072 inputs. Its repairs from 25 to 23 to 17 failed tests strictly improve the represented function. The defective three-row cone cannot be repaired in isolation by the checked lower bound. New feature-aware candidates use values already computed by outside stars; their results are recorded separately.

Construction routes now include free-feature gadgets, full-plane coupled repair, and joint synthesis of the full residual and a conditional tap. Every proposed witness must pass the complete boundary verifier and then Lean. SAT timeouts are UNKNOWN; restricted UNSAT, formula-DP and MILP results apply only to their documented models.

The DNF verifier now avoids large input enumeration for Lean proofs. Its concrete augmented-circuit certificate passed in about eight seconds including imports. Earlier large finite-set batches were stopped for memory and are retained as unsuccessful diagnostics. The submission assembler binds the exact assigned statement, rejects the known incorrect circuit, and creates no target file until a candidate has at most 63 gates and exactly the 52 required prime terms. Its complete generated final theorem still needs a positive-candidate Lean build and repository checker run.

Four preservation snapshots retain changed programs, datasets, seeds and selected complete logs. MANIFEST files record original and stored SHA256 hashes; large datasets are gzip-compressed. Snapshot STATUS files distinguish checked results, near misses, calibration circuits and unfinished experiments.

## Administration

Special check L-meta-1035 returned not_open; the response did not say whether it was checked or stood down. Three initial hard-desk requests returned null with this exact note:

> no step is free that you have not already looked at and handed back in the last hour (2); new steps are posted through the day, ask again in a few minutes

L-meta-650 was assigned on 2026-11-25 at 02:14:27 UTC. Only this job's lease is renewed. An optional authenticated GitHub API read returned 401; VENDOR-LIMITATION git-auth-401 was reported, and no alternate credentials were used. Git fetch and preservation pushes succeeded.

Sub-agents: algebra_strategy, circuit_search, lean_baseline, lower_bound, reduction_analysis, status_review (6 distinct agents).

TIMING total=139.7 subagents=6 (checkpoint at 2026-11-25T04:20:49.246161+00:00; work continues).

Job ID: msg-e98796d0d0ad050188abca1f.
