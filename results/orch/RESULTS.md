# L-meta-650 research checkpoint

The posted claim is not proved or refuted. No proof PR has been opened, and the repository checker has not accepted the target. This branch preserves independently reviewed Lean components, research programs, complete diagnostics and explicitly incorrect candidates.

## Checked components

| File under lemmas/ | What it proves |
| --- | --- |
| lean_baseline/BaselineCorrect2.lean | An explicit circuit with 64 gates computes the exact posted function on every input. |
| lean_baseline/FullPairAugment.lean | A circuit with 60 gates computes the 52 required edges plus six extra edges. It is not a target witness. |
| lower_bound/AugmentedCandidate17.lean | A circuit with 28 gates computes the 24 core edges plus four extra edges. |
| verification/CertifiedAugmented17.lean | The same augmented circuit is verified by finite DNF certificates for all input lists of length 17. |
| verification/CertifiedFullTwoExtra.lean | A 63-gate circuit computes the 52 required edges plus exactly (1,20) and (2,15). It is not a target witness. |
| verification/SubmissionCalibration64.lean | The final DNF proof body proves the exact posted function with a 64-gate calibration circuit. |
| reduction_analysis/FilteredPairIdentity.lean | Four checked Boolean identities supporting the filtered-pair seed rewrites. |
| reduction_analysis/SaturatedNegativeFamily.lean | At the negative-family counting limit, each binary AND has unequal children on every member. |
| reduction_analysis/FourOwnerSaturation.lean | Every paid binary AND in an exact four-owner core with at most four binary ANDs is graph-sound, even with arbitrary pure-OR features. The assembled size contradiction is separate. |
| reduction_analysis/DNFVerifierMono.lean | A sound gate-by-gate DNF certificate checker, including every wire, false-default references and Monotone2. |
| verification/FiniteVerification.lean | A candidate passing the stated finite boundary checks suffices for the exact posted target. No candidate is supplied. |
| reduction_analysis/SpecializedLiftFast.lean | Smaller-core completion routes, including a circuit with at most 28 gates for the six-row core. |
| reduction_analysis/NineRowCompletion.lean | A nine-row circuit with at most 43 gates extends to the posted 63-gate target. |
| reduction_analysis/AffineNineRowCompletion.lean | The 21-input affine nine-row core with at most 43 gates also extends to 63 gates. |
| reduction_analysis/PairTapCompletionWeak.lean | A core with at most 29 gates and the conditional pair tap extends to 63 gates. |
| reduction_analysis/TripleTapCompletion.lean | A core with at most 30 gates and the conditional triple tap extends to 63 gates. |
| reduction_analysis/NineTapCompletion.lean | A circuit with at most 17 gates computing two stars and nine cross-OR taps extends to 63 gates. |
| reduction_analysis/AttachFull.lean | The two-gate attachment half of the existing full residual/tap reduction. |
| algebra_strategy/FourRowLower.lean | The designated four-row core needs at least 19 gates. Research imports. |
| reduction_analysis/SixLeafCycleLower.lean | The designated three-row subproblem with six private leaves needs at least 14 gates. Research imports. |
| algebra_strategy/FreeCrossPairLower.lean | The two-owner function cannot use eight additional gates with all nine fixed free cross-OR features. Research imports. |
| algebra_strategy/FreeFeatureElimination.lean | The noncollinear three-owner gadget needs at least 14 paid gates despite all 22 specified free OR features. Research imports. |
| algebra_strategy/FourOwnerFreeRestriction.lean | An 18-gate four-owner gadget implies a 14-gate reduced kernel with three specified free OR features. This is necessary, not sufficient. Research imports. |
| algebra_strategy/SixCoreOrEncodedAndBound.lean | The six-row core requires at least six paid AND gates even with arbitrary free OR features. Research imports. |
| algebra_strategy/GlobalOrCharge.lean | A two-OR deletion step extends to arbitrary no-C4 graphs of minimum active degree two. It does not prove the needed 51-OR bound. Research imports. |
| reduction_analysis/RepairGuardLower.lean | A separately computed monotone guard rejecting both extra pairs while preserving all required edges needs at least 13 gates. Sharing remains possible. Research imports. |
| algebra_strategy/PlaneAndThirteen.lean | The complete accepted upstream proof plus a checked relabeling proves at least 13 AND gates for the exact posted graph. Research imports. |
| reduction_analysis/PairDirtyNecessary.lean | Every exact circuit with at most 63 gates has an AND true on an independent input with at most two active bits. Research imports. |
| reduction_analysis/ResidualPairDirtyNoncopy.lean | Every qualifying binary joint61 residual/tap circuit has such a dirty AND with distinct operand indices. No H-cone relevance is asserted. Research imports. |

Further checked monotonicity, geometry, lifting and normalization lemmas are recorded in NOTES.md and validation.txt. Research imports are not eligible for the final file without permitted inlining. The fixed-feature lower bound does not automatically exclude the more general interleaved multioutput completion theorem.

## Current search and verification status

The best preserved bare six-row approximation fails 17 maximal-negative tests and accepts 255 extra assignments among 131072 inputs. Its repairs from 25 to 23 to 17 failed tests strictly improve the represented function. The defective three-row cone cannot be repaired in isolation by the checked lower bound. New feature-aware candidates use values already computed by outside stars; their results are recorded separately.

Construction routes now include free-feature gadgets, full-plane coupled repair, and joint synthesis of the full residual and a conditional tap. Every proposed witness must pass the complete boundary verifier and then Lean. SAT timeouts are UNKNOWN; restricted UNSAT, formula-DP and MILP results apply only to their documented models.

The full-plane 63-gate near miss has exactly two extra prime terms and fails 140 of the 704 maximal-negative tests. The reduced four-owner kernel has nonlinear and quadratic near misses, but no exact 14-gate witness or verified restoration. A new OR-only synthesis model tests lower bounds with unrestricted AND counts; its computational outcomes are not Lean proofs.

The second upstream refresh found the accepted L_meta_1898 theorem, which proves at least 13 AND gates for the isomorphic projective-plane function. The complete upstream proof and the exact posted-edge adapter have now compiled together and passed independent review. No general 51-OR theorem or completed L_meta_650 proof was found. Fixed searches below 13 global AND gates were retired.

The context-based two-edit search escaped its initial nonlinear plateau. A 27-gate six-core approximation lifts to a 62-gate full-plane circuit with six extra pairs; a subsequent 28-gate core lifts to 63 gates with five extra pairs. These are different, still incorrect constructions. A separately derived 63-gate filtered pair-merge candidate also has five extra pairs and supplies a verified phase for the residual SAT search. The first-gate symmetry datasets and all search constraints retain their documented scope; heuristic profiles do not establish impossibility.

The workspace restart at 04:48 interrupted running jobs. The lease was renewed immediately and its timer restarted. Interrupted solver runs are distinguished from reported UNKNOWN timeouts; complete available logs and restart metadata are retained.

The DNF verifier now avoids large input enumeration for Lean proofs. Its concrete augmented-circuit certificate passed in about eight seconds including imports. Earlier large finite-set batches were stopped for memory and are retained as unsuccessful diagnostics. The submission assembler binds the exact assigned statement, rejects incorrect circuits, and creates no target file until a candidate has at most 63 gates and exactly the 52 required prime terms. Its proof body has now compiled in the exact-function 64-gate calibration. A genuine 63-gate candidate still needs its own build and repository checker run.

Preservation snapshots retain changed programs, datasets, seeds and selected diagnostics. MANIFEST files record original and stored SHA256 hashes; large datasets are gzip-compressed. Snapshot STATUS files distinguish checked results, near misses, calibration circuits and unfinished experiments, including frozen output from searches that were still running.

The joint four-owner model now searches all compatible outside prefix choices together. Its assembler, explicit prefix costs, symmetry constraints and bounded support counts passed independent review. The first minimum-five-AND SAT run returned UNKNOWN after 300 seconds. The next run fixes five ANDs and adds the full exponential wildcard bound, with the arithmetic encoding independently checked. No exact core has been found.

The residual SAT lane now supports bounded gate edits and counterexample-preserving recentering. A one-gate calibration was solved in under a second, and a later four-gate repair fixed both original offending pairs while introducing other errors. Local-radius UNSAT is recorded only for the stated neighborhood. Wider timeouts do not prove a global lower bound. Batching more exact counterexamples and widening the radius are the next search steps.

The third upstream refresh (2239e82d294e0253da98cc18db45925e77796b01) added 11 proofs and 177 reductions. Independent scans found reusable local packing and circuit-cleaning proofs, but no general OR51 bound, full L650 result, or equality theorem upgrading the checked 13-AND bound to pair-clean structure. Reduction hypotheses remain unproved unless separately established.

## Administration

Special check L-meta-1035 returned not_open; the response did not say whether it was checked or stood down. Three initial hard-desk requests returned null with this exact note:

> no step is free that you have not already looked at and handed back in the last hour (2); new steps are posted through the day, ask again in a few minutes

L-meta-650 was assigned on 2026-11-25 at 02:14:27 UTC. Only this job's lease is renewed. An optional authenticated GitHub API read returned 401; VENDOR-LIMITATION git-auth-401 was reported, and no alternate credentials were used. Git fetch and preservation pushes succeeded.

Sub-agents: algebra_strategy, circuit_search, lean_baseline, lower_bound, reduction_analysis, status_review (6 distinct agents).

TIMING total=214.3 subagents=6 (checkpoint at 2026-11-25T05:35:23.761499+00:00; work continues).

Job ID: msg-e98796d0d0ad050188abca1f.
