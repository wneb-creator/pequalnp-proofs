# L-meta-650 final research results

The posted claim was not proved or refuted within this job. All final searches stopped before07:50 UTC; no exact target file or proof PR was produced. No proof PR has been opened, and the repository checker has not accepted the target. This branch preserves independently reviewed Lean components, research programs, complete diagnostics and explicitly incorrect candidates.

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
| reduction_analysis/FiveOwnerCoverageFull.lean | The five indexed covering sets are also distinct under the same tight count. |
| algebra_strategy/FiveOwnerRectangleComplete.lean | Finite allowed rectangles cover at most four target edges; equality classifies ordinary owner stars and four hub variants. |
| reduction_analysis/FiveOwnerBudget.lean and FiveOwnerBudgetFull.lean | The weighted30-negative budget restricts each AND and makes two dirty events consume the whole slack, under accepted pairwise-join premises. |
| reduction_analysis/FiveOwnerNegativesComplete.lean | Every independent input of the concrete16-input core lies below one of the30 listed maximal negatives. |
| algebra_strategy/FiveOwnerBridge.lean | The finite rectangle and negative-family definitions agree, with checked owner and edge identifications. |
| reduction_analysis/FiveOwnerClean.lean | Every AND is false on every independent input in any exact five-owner raw16 AndCountCircuit with at most five ANDs. Standalone1284-line Defs-only proof; the ordinary-Circuit transfer is proved in the separate file below. |
| reduction_analysis/TightConversionFull.lean | Converts an ordinary Monotone2 circuit with a false input to an equivalent AndCountCircuit with no more ANDs. When the counts are equal, each original AND value is represented by some converted AND on each input; the index may depend on the input. |
| reduction_analysis/FiveOwnerOrdinaryClean.lean | Every original AND in an exact ordinary Monotone2 raw16 five-owner circuit with at most five AND opcodes is false on every independent input. Constants, unary gates and default references are included. |
| reduction_analysis/AndCountOrSubstitution.lean and FiveOwnerFeatureClean.lean | Arbitrary correlated OR features preserve gate values and AND count; exact five-owner circuits with at most five ANDs have every AND false on encoded independent inputs. Correctness is required only on actual encodings. No shared-feature paid23 bound is claimed. |
| reduction_analysis/FiveOwnerCompletionLower.lean | An exact raw16 five-owner ordinary core with valid output and at most five AND opcodes needs at least24 gates; a raw core of size at most23 therefore needs at least six ANDs. This uses fixed40-gate completion and does not claim the shared-feature paid budget. Research import L2656. |
| verification/AppendStarSound.lean and reduction_analysis/FiveOwnerLiftSound.lean | Preserve the property that each true AND wire implies the circuit output under row appending and input reindexing. |
| algebra_strategy/AtLeastTwoJunkLeastAO.lean | Any size-at-most63 IsLeastAO circuit for the exact plane has at least two junk gates. No public Monotone2 normalization is included in this file. Research imports. |
| algebra_strategy/JunkMinimalResidual.lean | Generic normalization to a no-larger least TopForm representative minimizing junk, where each junk deletion loses at least two distinct residual edges. Includes the checked binary-repair and lost-edge/Ustar bridges; no full gate lower bound. |
| algebra_strategy/PlaneResidualCounting.lean | Under leastAO, TopForm and size at most63, proves P+1≤2|U| and4P+4≤5|U| plus conditional penalty-four equality consequences. |
| algebra_strategy/PlanePenaltyFourStar.lean | For the actual plane, leastAO+TopForm+size≤63+penalty4+four residual edges imply that the residual set is exactly one full vertex star. This identifies the case and does not exclude it. |
| algebra_strategy/SingletonMixingMarker.lean and SharedLineMarker.lean | Distinct polluted singleton wings have distinct mixing markers; a marker shared between distinct line wings has support at most one. Dynamic singleton sharing remains unresolved. |
| algebra_strategy/TightCoverGeometry.lean and TightCoverStar.lean | Generic tight-cover independence, purity of independent12-sets in13+13 parts, and residual-star identification under explicit equality assumptions. |
| algebra_strategy/ResidualCoverCounting.lean | Generic residual-cover extension and bounded-degree edge counting; no circuit lower bound alone. |
| algebra_strategy/NormalizedPenaltyFour.lean | Any exact full-graph Monotone2 circuit of size at most63 has a no-larger least TopForm representative with penalty at least four and at least two junk gates. The larger-penalty alternatives remain open. Research imports. |
| algebra_strategy/LowPenaltyGeometryFull.lean | A generic bipartite/no-C4 cover promise forces at most one residual edge; deleting one edge changes a minimum cover upper bound by at most one. No full-plane gate bound by itself. |
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

Further checked monotonicity, geometry, lifting and normalization lemmas are recorded in NOTES.md and validation.txt. Extra project imports must be inlined as required before a final single-file submission; permitted Mathlib imports are distinct from that restriction. All files here remain partial research artifacts. The fixed-feature lower bound does not automatically exclude the more general interleaved multioutput completion theorem.

## Current search and verification status

No exact circuit with at most63 gates has been found. The exact64 baseline and unrestricted13-AND lower bound are checked. No general51-OR theorem or full refutation is available. The familiar63-gate near miss computes the52 required edges plus two extra pairs and fails140 of704 maximal-negative tests; other numerical scores refer to distinct local cores and are not comparable full-target improvements.

The five-owner dirty-five-AND route now has a computational exclusion. Both the strengthened and original uncut arbitrary-OR-subset models returned UNSAT. The uncut model allows empty OR sides, unused AND nodes and any independent dirty input of at most two bits, with only commutative side ordering. Independent execution of Lean's LRAT checker accepted both exact certificates: the uncut case has2623 variables,10330 clauses and1344681 LRAT actions. Exact formulas, compressed certificates, runner, hashes and complete logs were pushed in b6db04f93bd630ea87d31bdb4048ec33b0e8cfa8. This is runtime CNF certificate validation; the circuit encoding and concrete checker result have not been turned into a kernel theorem. It is not a refutation of L-meta-650.

The redundant physical23-gate/five-AND solver was intentionally retired after three UNKNOWN checkpoints and an interrupted fourth interval. Its result is not UNSAT. The five-owner stochastic profile now explores at least six active ANDs. The four-owner weighted profile includes separately audited nonlinear multiguards. All these starts remain approximations. The active global26-input/63-gate search allows the previously fixed outside stars to change; the new continuation permits13 or more active ANDs, retaining both suppressed-error seeds and the known ordinary140-error near miss. The earlier fourteen-AND minimum was only a search profile.

The strengthened six-owner arbitrary-OR/six-AND model returned UNSAT with its reviewed guards. An independent Lean LRAT runtime check accepted the exact12127-variable/46509-clause certificate with840935 actions; the formula, compressed proof, hashes and complete logs are preserved. The uncut six-owner model ended UNKNOWN after1200 seconds. Neither result is a kernel circuit theorem or a full-target refutation. The original full thirteen-AND dirty model and the comparison with dirty-pair symmetry/minimum-AND constraints each ended UNKNOWN after1200 seconds; the orbit-only comparison ended UNKNOWN after300 seconds. A skeleton has no total gate guarantee until its OR implementation is costed and checked. The exact66-gate/fourteen-AND double-star bank supplies another phase only. The reviewed selector-budget construction profile explicitly requires nonempty cones and checks its actual assembled size; it is sufficient for a witness but does not represent every circuit with shared OR gates. The direct full14-AND/63-budget run completed900 seconds of UNKNOWN before an intentional interruption. The65→64→63 descent completed1200 seconds UNKNOWN at65 and never reached64 or63. A raw six-owner7-AND/28-budget run completed600 seconds UNKNOWN before rotation; the replacement permits42 compatible correlated OR-prefix inputs. These remain restricted construction searches, not lower bounds.

All four-, five- and six-owner prefix packets retain reviewed exact full-plane assembly and actual gate-budget checks. The five-owner packet has16 raw inputs,36 optional features and exact per-owner OR-network cost tables; a compatible23-gate core plus40 outside gates would suffice. Full-truth calibrations, source mappings, symmetry data, necessary-cut hypotheses and phase-only status are preserved. Weighted objectives are explicitly separate from ordinary boundary failure counts. SAT timeouts, local-neighborhood exclusions and interrupted searches retain their limited scope.

The direct ordinary-Circuit weighted packing theorem and its tight30-negative/five-AND corollary are Lean-checked, as are generic forced-active and saturation lemmas. The complete local five-owner cleanliness theorem now compiles and has passed independent review. Its finite geometry, weighted budget and propagation argument are included in one Defs-only file. It excludes dirty ANDs in the exact raw16 AndCountCircuit model with at most five ANDs; a tight-count conversion now also proves the ordinary-Circuit version, including constants and unary gates. The fixed-star completion corollary is also checked: any exact raw core with at most five AND opcodes has size at least24. A shared-feature paid-budget claim and global exclusion do not follow automatically.

The final construction profiles include a punctured four-owner decomposition with13raw inputs/24optional OR features,15paid core gates and47outside+1final gates; this is a focused subclass of the earlier four-owner18 model. Its243 compatible prefix configurations and exact65-gate calibration are checked. Shared-OR seven-AND profiles now allow one expression after earlier ANDs, with exact cost and topological checks; optional Kraft and output-cone conditions retain their documented scopes. All searches ended without an exact target witness. The final physical exact6 and both all-live/Kraft profiles each completed two300-second UNKNOWN intervals; both final stochastic profiles exited normally. Restart interruptions are recorded separately.

The final DNF proof body and assembler were calibrated on the exact64-gate circuit. A new63-gate candidate still must match exactly the52 required prime terms, compile in the named target file, and pass the repository checker. No target file or exact-target checker acceptance exists.

Six upstream refreshes found useful local tools but no full L650 proof or unconditional OR51 bound. Latest inspected upstream:b4b27af110a7b1d350d8a3e4c4c890d1381dec60. Refresh006 examined88 changed Lean files and a fully paginated713-open-PR census; no accepted650 file or proof/refutation PR was found. Exact signatures/provenance and limitations are preserved. New minimum-AO/topological-normalization and junk-gate counting results supplied checked necessary conditions. The compiled generic low-penalty geometry bounds the residual edge set by one under its explicit cover promise; the larger-penalty alternative remains open. Newly accepted reductions retain open hypotheses; commented source is not treated as a checked lemma. Workspace restarts, including04:48 and07:36, and interrupted processes are documented separately from solver timeouts. The07:36 restart preserved source files and the completed twelfth snapshot; the lease was renewed and final capped work resumed.

Preservation snapshots retain changed programs, datasets, seeds and complete available diagnostics. Manifests record original and stored hashes; ongoing-run logs are complete only through their freeze. Large proof certificates are stored compressed. Research imports and runtime tooling are not eligible final-PR contents without the required single-file cleanup.

## Administration

Special check L-meta-1035 returned not_open; the response did not say whether it was checked or stood down. Three initial hard-desk requests returned null with this exact note:

> no step is free that you have not already looked at and handed back in the last hour (2); new steps are posted through the day, ask again in a few minutes

L-meta-650 was assigned on 2026-11-25 at 02:14:27 UTC. Only this job's lease was renewed. The final release outcome is recorded separately in FINAL_STATUS.json after the preservation push. An optional authenticated GitHub API read returned 401; VENDOR-LIMITATION git-auth-401 was reported, and no alternate credentials were used. Git fetch and preservation pushes succeeded.

Sub-agents: algebra_strategy, circuit_search, lean_baseline, lower_bound, reduction_analysis, status_review (6 distinct agents).

TIMING total=350.0 subagents=6 (final research freeze at 2026-11-25T07:51:07.351046+00:00; final administration is recorded in FINAL_STATUS.json).

Job ID: msg-e98796d0d0ad050188abca1f.

## Recovering artifacts

ARTIFACT_INDEX.json maps 1,912 indexed research source/data/log paths to its exact committed direct file or versioned snapshot, with SHA256 hashes and any gzip encoding. It is a storage index, not a compilation claim. Reviewed Lean validation receipts and complete logs establish the listed checked results. The unresolved target has no repository-checker acceptance.

Three additional C++ review diffs are committed directly under lemmas/lower_bound/sat; the tiny LRAT proof fixture is also directly committed. These extra diagnostic extensions are outside the storage index selection.
