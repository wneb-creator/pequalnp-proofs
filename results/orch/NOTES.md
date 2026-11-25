# L-meta-1479 orchestration notes

Lease acquired: 2026-11-25T09:33:51Z after nine null desk replies. Only root holds and renews this lease.
The task asks for at most 27 normalized binary AND/OR gates computing Fano incidence on 14 inputs, with a double re-read incidence.
Exact desk statement: results/orch/statement.txt. Full assignment remains in scratch desk-assigned.json.
Lean binaries: /tmp/oec/pequalnp-pilot-81/lean-4.36.0-linux/bin. Cache, verifier and definitions are ready.
Main proof file is root-owned: lean/PEqualNP/Outside/L_meta_1479.lean.
Agents own separate files under results/orch/lemmas. No agent except root may call the desk, commit or push.

## Checked partial results

- A normalized, correct 27-gate star baseline, without the required double re-read.
- An explicit 28-gate circuit satisfying every posted clause except the 27-gate bound.
- Trace existence, finite gate/trace checks, and a 21-positive/37-negative correctness certificate.
- Fano no-four-cycle and strict Hall properties; only whole bipartition sides are vertex covers of size at most seven.
- Final AND singleton-support restriction; derivative-support and single-gate substitution lemmas.
- Complete positive-support normalization: replace unsupported gates by another incidence edge, preserving gate count, output, and both marked traces. Every resulting gate turns on for some positive edge input.

These are partials. The exact posted theorem is not yet proved. Public status at10:26UTC reports two live reductions: R824 died after its joint24 prefix premise was refuted. A new reduction slot exists, but no new premise has yet passed the plausibility review.

## Search status and scope

- Thirty-two internal 28-gate seeds are verified on all 16,384 inputs and both traces.
- Captured 27-gate near-candidates compute Fano minus one edge; none solves the task.
- C6 at eight gates is computationally UNSAT both with distinct and repeated operands. This is not a Lean certificate.
- Sequential deletion of private inputs reduces the shared-edge three-star case to repeated-input C6; a private marked edge instead leaves C6 plus one leaf. Formal elimination/certificate work remains.
- Previous focus: four-cap points {0,1,4,6}, twelve edges, ten relevant inputs. A 15-gate double-quiet witness would splice into a full 27-gate witness.
- The machine has five logical CPUs. Search workers are coordinated with Lean builds; avoid oversubscription.

Root must renew before long runs and every ten minutes, preserve all compiled progress promptly, independently review every pushed diff, and keep any eventual PR to the exact single named Lean file.

## Re-plan at 10:40 UTC

- Accepted upstream proof L-meta-6659 (PR13206) proves the ordinary Fano lower bound27 and refutes the joint24 H,N prefix. Source: https://github.com/open-goat/pequalnp-proofs/pull/13206 . Its9,506-line source is preserved in scratch and matched to the public checker artifact.
- All joint12/24 routes stopped UNKNOWN; no solver UNSAT claim. The accepted external refutation supplies the obstruction.
- Full27 SAT runs with no fixed prefix/final-gate restriction, verified support normalization, exact58 boundary rows and both derivatives. Independent known28 control passed every clause. A stronger variant uses ordinary minimality to require AND operands incomparable on negative rows and OR operands incomparable on positive rows.
- Four-cap15 reduction paused: the accepted K4 equality invariant appears to force an ineligible point and no empty-support branching, hence a single-reader path and nonzero derivative. Constructive agent is certifying the finite equality geometry; Lean agent is proving the derivative bridge.
- A joint25 G/P/L mask reduction was considered but paused: it requires all21 edges quiet, and no plausible near-bound construction is known. Do not submit a likely false premise just because a slot opened.
- Algebraic and status agents examine low/high eligible-cardinality cases for exact27 Fano circuits. Full refutation would target the exact negated twin L-meta-1480, without taking another lease.
- Current full global CSE and generic SAT searches remain complementary to the equality analysis. Machine budget: five logical CPUs, coordinate proof builds with search workers.

## Re-plan at 11:00 UTC

- Direct minimal-circuit conversion now preserves the exact size, output, wires and all derivative traces while proving StrictLive; no destructive normalization of the witness is needed.
- Compiled low equality: p7/p8 one-sided cases have Bzero=0. Compiled mixed2+2: Bplus>=13, hence Bzero<=1 at total surplus14.
- Compiled high equality: Bzero=0 for p14, canonical p13, both p12 patterns, and p11 noncollinear. The p11 collinear/mixed cases remain unresolved.
- Canonical p8 closure is in progress:14 carrier gates +7 exits +6 false OR gates exhaust27; carrier-linearity is intended to rule out quiet at the sole eligible point.
- K4 minimum no-double-quiet is compiled in the exact strict-live10-input model. Strengthening cofactor bounds using its equality case needs explicit protected-input or lost-unit/fiber-slack bookkeeping.
- Generic critical-input false-OR count is compiled: k individually critical inputs at a false base require at least k-1 false OR gates. This supplies37 new possible SAT cardinality constraints; any encoding extension needs independent review before a restart.
- Broad SAT cutoff remains12:34UTC. One variable-length stochastic worker runs640 verified28/29/31 seeds with mixed branching preferences, capped at11:17:45UTC.

## Re-plan at 11:17 UTC

- Canonical p7/p8 no-double-quiet now passes its full standalone build and independent review.
- Missing-mask saturation protects other ineligible inputs; strict cofactor slack accounts for kept units whose images stop branching. These components are compiled and reviewed.
- New proposed invariant counts surplus on wires false at the all-lines-true base. Combined with all seven neighborhood masks it may exclude any eligible point at27 gates; its generic count and branch-charge lemmas are under construction.
- Higher eligible cases still need an actual no-quiet argument. Bzero0 alone is insufficient.
- Broad SAT continues toward12:34UTC. The next single stochastic worker uses480 verified inputs, including higher-eligible quiet seeds and correct27-gate bright controls.

## Progress at 11:24 UTC

- False-wire surplus count and eligible critical-branch injection now pass standalone Lean and independent review. Their all-mask combination is being checked.
- Canonical p11 collinear now has Bzero0; this alone does not exclude quiet edges. P14 consumption/AND-support restrictions are being flattened for a standalone build.
- The cyclic posted Fano graph and accepted edgeList are related by fixing point labels and negating line labels. Standalone lemmas now transport correctness and all derivative traces through any input permutation without changing gate outputs.
- Integration is assigned: derive a StrictLive canonical double-quiet witness from the exact posted existential, conditional on the remaining structural exclusion theorem.
- Public snapshot generated11:21:13UTC still lists L-meta-1479 and L-meta-1480 as conjectures.

The all-mask combination now has a successful standalone build and independent composition review. P14 structural restrictions also have a successful standalone build. The one-sided p9 case is reduced in the active proof work to a finite residual-support predicate; its certificate and actual-circuit transfer are still being checked. The exact posted-to-canonical bridge has a reviewed cached build, with standalone recheck pending.

The exact posted-to-canonical bridge now has a successful standalone build and independent review. Its missing structural theorem remains an explicit hypothesis. A shorter direct dead-gate/trim transport is being developed to avoid the ordinary lower-bound dependency. The reviewed p14 ordinary-feasibility SAT worker is scheduled to take the stochastic slot after11:37:50, while the broad quiet27 solver continues.

## Re-plan at 11:45 UTC

- The exact-statement bridge now uses trace-preserving output trimming and dead-gate deletion, reducing its standalone source from502345 to144941 bytes. The structural no-quiet premise remains open.
- P9 one-sided: actual-circuit transfer, protected masks, cofactor closure, and the six-line all-mask contradiction are ready in the cached development. The bounded finite residual-mask certificate is still compiling; no complete p9 result is claimed yet.
- P10 one-sided line case: two independent enumerations found a two-residual-unit contradiction using generic co-label and consumption constraints. A small Boolean kernel certificate and Finset transfer are being developed; the larger residual budgets remain open.
- P14: the broad and targeted ordinary SAT workers run separately. The stochastic phase ended without a witness. Structural work now considers marked-edge routing and multi-unit cofactor loss, with K4 surplus7 eligibility as a possible refinement.
- Continue preserving every compiled reviewed component. No proof PR until the exact target or its negated twin passes the full checker.

2026-11-25T11:56:17.197695+00:00: Preserving completed p10 finite obstruction and cached circuit transfer separately, compact q5 core, and multi-unit cofactor slack. Full p9 and strengthened K4 standalone builds are pending; main target remains absent.

2026-11-25T12:03:14.846860+00:00: Full compact q5 certificate passed; original slow job stopped with exit143 after valid alternative completed. P9 standalone composition and p10 standalone bound are running. P14 targeted SAT ended UNKNOWN; structural and smaller semantic models continue.

2026-11-25T12:12:12.875241+00:00: P9 one-sided canonical case fully excluded by standalone checked theorem. P10 I0123 bound and generic maximal-negative branch-value invariant also pass standalone checks. Stronger K4 cached theorem passed; full standalone pending. Compact p14 SAT running with reviewed flattening and negative-proxy cut; no result yet.

K4 update: the full7570-line permitted-import standalone also completed exit0 and independent composition review before this checkpoint was pushed.

2026-11-25T12:23:31.745069+00:00: Preserving complete cap finite/Finset certificate, three-subset helper, carrier derivative invariant, and cached mixed-p10 analytic bound. Root mixed-p10 and algebraic full cap standalone builds are active. Compact p14 encoding and exact reconstruction controls are preserved before solver completion.

2026-11-25T12:30:58.577912+00:00: Full cap ordinary exclusion and mixed-p10 analytic bound now pass standalone builds. Missing49 finite sibling is checked, with circuit-line adaptation in progress. Main remaining routes are mixed p9, remaining line-q2 masks, and high cases; no full target claim.

2026-11-25T12:47:51.801477+00:00: Preservation checkpoint1245 collects standalone line-three missing-mask exclusion, nonedge branch, nine-free cofactor, chain-agreement and mask-closure results. The line q2 pattern, mixedp9 and high eligible cases remain open. Protected-K4/protection and related helpers are cached-checked only at this freeze; active combined standalone builds are excluded. Both completed broad/ordinary compact SAT runs ended UNKNOWN; quiet/nine-free models and completed computational research are preserved without a target outcome claim.

2026-11-25T13:01:43.528398+00:00: Preservation checkpoint1300 collects standalone mixed-p9 predicate transfer, protected K4 and protection transport, q2 semantic interface, conditional finite decoding, historical benchmark diagnostics and the completed quiet compact UNKNOWN outcome. Cached supported-eight/upper wrappers retain explicit hypotheses; running case proofs and the active nine-free SAT diagnostics are excluded. The full target and remaining canonical cases stay open.

2026-11-25T13:19:03.269765+00:00: Preservation checkpoint1320 collects the standalone218-line analytic q2 residual obstruction and both independent reviews, replacing the intentionally stopped exhaustive residual run (exit143, complete diagnostics retained). The successful standalone q2 semantic wrapper and cached actual-circuit transfer retain their explicit finite-certificate or mask-family hypotheses. The supported-eight cofactor lower bound now passes its full8425-line standalone build. Mixed-p9 exact-missing-{2,5} composition passes cached Lean with the finite certificate still explicit; the repaired finite worker and symmetry draft are excluded from this freeze. Sharp17-gate K4 controls show that the supported lower bound8 is attainable and cannot be raised from protection alone. The completed nine-free SAT run is UNKNOWN; independently audited incomparability/partition variants and fresh restored controls are preserved, while the new partition solver remains active. No full target theorem or refutation is claimed.

The first mixed-p9 finite build is archived separately with exit1: all128 decision blocks and certificate assembly checked, but its final API wrappers had elaboration/heartbeat failures. The repaired build is active and is not claimed as complete at this freeze.

2026-11-25T13:21:29.307409+00:00: Checkpoint1320 addendum: the repaired996-line mixed-p9 finite certificate completed permitted-import Lean exit0, with two unused-simp warnings and empty stderr. Its exact source and emitted backend match the finalized independent review. The unconditional finite API is now available; actual-circuit instantiation and full standalone case composition remain separate and are not claimed in this addendum.
