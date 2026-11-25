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
| reduction_analysis/ForcedActiveAnd.lean | A generic negative-family bound forces every binary AND active on a dominating input. Concrete restriction masks are separately audited data. |
| reduction_analysis/WeightedRejectedPacking.lean | The accepted weighted selector bound, extracted for the AndCountCircuit model without a Circuit conversion claim. |
| reduction_analysis/DirectWeightedPacking.lean | The weighted bound directly for ordinary Monotone2 circuits and their actual sequential AND operand values; constants and unary gates are supported. |
| reduction_analysis/DirectWeightedSlackTwo.lean | For 30 rejected inputs whose distinct joins are accepted, and at most five binary ANDs, every equal-child count is at most one and their sum is at most two. |
| reduction_analysis/FiveOwnerPropagation.lean | Generic AndCountCircuit earliest-origin and no-first-filter propagation lemmas, with explicit structural premises still to instantiate. |
| algebra_strategy/FiveOwnerRectangleBase.lean | Exact finite five-owner edge/allowed-pair data and basic symmetry/orientation facts; no circuit lower bound. |
| reduction_analysis/FiveOwnerCoverage.lean | Twenty elements covered by five sets of size at most four force each covering set to have size four; a generic counting component only. |
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

No exact circuit with at most63 gates has been found. The exact64 baseline and unrestricted13-AND lower bound are checked. No general51-OR theorem or full refutation is available. The familiar63-gate near miss computes the52 required edges plus two extra pairs and fails140 of704 maximal-negative tests; other numerical scores refer to distinct local cores and are not comparable full-target improvements.

The five-owner dirty-five-AND route now has a computational exclusion. Both the strengthened and original uncut arbitrary-OR-subset models returned UNSAT. The uncut model allows empty OR sides, unused AND nodes and any independent dirty input of at most two bits, with only commutative side ordering. Independent execution of Lean's LRAT checker accepted both exact certificates: the uncut case has2623 variables,10330 clauses and1344681 LRAT actions. Exact formulas, compressed certificates, runner, hashes and complete logs were pushed in b6db04f93bd630ea87d31bdb4048ec33b0e8cfa8. This is runtime CNF certificate validation; the circuit encoding and concrete checker result have not been turned into a kernel theorem. It is not a refutation of L-meta-650.

The redundant physical23-gate/five-AND solver was intentionally retired after three UNKNOWN checkpoints and an interrupted fourth interval. Its result is not UNSAT. The five-owner stochastic profile now explores at least six active ANDs. The four-owner weighted profile includes separately audited nonlinear multiguards. All these starts remain approximations. Global26-input/63-gate search preparation will also allow the previously fixed outside stars to change; its planned fourteen-AND minimum is a search profile, not a proved global lower bound.

The strengthened six-owner arbitrary-OR/six-AND model returned UNSAT with its reviewed necessary guards; independent certificate verification is in progress. The uncut model continues after UNKNOWN checkpoints. Neither is a Lean circuit theorem or a full-target refutation. The original full thirteen-AND dirty model timed out after1200 seconds; a comparison with reviewed dirty-pair symmetry and minimum-AND constraints is running. A skeleton has no total gate guarantee until its OR implementation is costed and checked. The exact66-gate/fourteen-AND double-star bank supplies another phase only. The reviewed selector-budget construction profile explicitly requires nonempty cones and checks its actual assembled size; it is sufficient for a witness but does not represent every circuit with shared OR gates.

All four-, five- and six-owner prefix packets retain reviewed exact full-plane assembly and actual gate-budget checks. The five-owner packet has16 raw inputs,36 optional features and exact per-owner OR-network cost tables; a compatible23-gate core plus40 outside gates would suffice. Full-truth calibrations, source mappings, symmetry data, necessary-cut hypotheses and phase-only status are preserved. Weighted objectives are explicitly separate from ordinary boundary failure counts. SAT timeouts, local-neighborhood exclusions and interrupted searches retain their limited scope.

The direct ordinary-Circuit weighted packing theorem and its tight30-negative/five-AND corollary are Lean-checked, as are generic forced-active and saturation lemmas. An analytic five-owner exclusion is now being assembled from finite rectangle geometry and generic AND-origin/propagation results. The complete local theorem is not yet claimed.

The final DNF proof body and assembler were calibrated on the exact64-gate circuit. A new63-gate candidate still must match exactly the52 required prime terms, compile in the named target file, and pass the repository checker. No target file or exact-target checker acceptance exists.

Three upstream refreshes found useful local tools but no full L650 proof, required OR51 bound, or thirteen-AND equality classification. The latest inspected upstream is2239e82d294e0253da98cc18db45925e77796b01. Newly accepted reductions retain open hypotheses; commented source is not treated as a checked lemma. The04:48 workspace restart and interrupted processes are documented separately from solver timeouts.

Preservation snapshots retain changed programs, datasets, seeds and complete available diagnostics. Manifests record original and stored hashes; ongoing-run logs are complete only through their freeze. Large proof certificates are stored compressed. Research imports and runtime tooling are not eligible final-PR contents without the required single-file cleanup.

## Administration

Special check L-meta-1035 returned not_open; the response did not say whether it was checked or stood down. Three initial hard-desk requests returned null with this exact note:

> no step is free that you have not already looked at and handed back in the last hour (2); new steps are posted through the day, ask again in a few minutes

L-meta-650 was assigned on 2026-11-25 at 02:14:27 UTC. Only this job's lease is renewed. An optional authenticated GitHub API read returned 401; VENDOR-LIMITATION git-auth-401 was reported, and no alternate credentials were used. Git fetch and preservation pushes succeeded.

Sub-agents: algebra_strategy, circuit_search, lean_baseline, lower_bound, reduction_analysis, status_review (6 distinct agents).

TIMING total=262.6 subagents=6 (checkpoint at 2026-11-25T06:23:43.081927+00:00; work continues).

Job ID: msg-e98796d0d0ad050188abca1f.
