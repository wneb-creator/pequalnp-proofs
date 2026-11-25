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
