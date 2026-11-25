# L-meta-2583 orchestration notes

New own lease received 2026-11-25 14:52:34 UTC, expires 15:12:34 UTC.
Reductions closed. Exact statement in scratch statement-2583.txt.
Old L-meta-2592 work stopped after lease410 and preserved at commit9b9d9f1a.

## Toolchain/checker feasibility (2026-11-25 14:55 UTC)

No supported definitions-only checker mode exists: all three modes import full Mathlib unconditionally. Even a generous cleanup estimate including all unrelated scratch/results, static/editor/source toolchain files, and other Outside sources leaves 2,690,915,208 bytes short. No live cache or toolchain changes were made. The existing upstream PR authoritative workflow is the genuine remaining checker path. Details: `results/orch2583/toolchain/feasibility.txt`.

## reduction_strategy 2026-11-25T14:57:31.347851+00:00

Checked `SingleLevelChecked.lean`: for every finite simple graph G, IsAO2 n C, TopForm G C, and junk G C = empty imply ReadK.IsReadK n C 1. No leastness/correctness/no4cycle/plane assumptions required. Pure OR-only operand wires yield unit proof vectors and singleton witnesses. Every AND is below graphFun, hence cannot accept a singleton, forcing distinct leaf units. TopForm with empty junk supplies no nested AND cones. The unresolved part of L-meta-2583 remains finding a no-larger circuit with empty junk (or proving another route to read1). Copied read-vector infrastructure from checked L7684 and cone recurrence from L8385, then proved new generic bridge. Lean check exit0 with empty stdout/stderr.

## One-junk audit 2026-11-25T14:59:27.321676+00:00

L3700 handles unique dirty AND whose singleton evaluations are all false, producing no-larger single-level AO2. L3653 handles the complementary case (some singleton true), producing no-larger AO2 with all AND gates BelowF. Both assume bipartite, no4cycle, fixedpoint, no BelowF AND operands, and live gates. The extra normalization assumptions appear derivable from leastness+TopForm: L1498.main_real says every non-output BelowF gate has a unique OR reader which is also BelowF; input wires are not BelowF on loopless graph. This excludes BelowF operands of ANDs and lift sites; least_out/least_read provide liveness. L1501 normalizes while preserving junk count. No several-thousand-line assembly attempted because it would only repackage known one-junk elimination. Residual meaningful case is at least two dirty ANDs.

## Counterexample route, 2026-11-25T14:59:30.469020+00:00
ReadK audit: joint per-prime-implicant proof-tree multiplicity, not global input fanout; no semantic loophole identified. Standard stars cost N(q+2)-1. The mixed guard identity (a OR A)(b OR B)(a OR b) = ab OR aB OR bA costs one extra binary gate over two stars, and sharing its central-edge guard alone does not improve that count.
Read https://github.com/open-goat/pequalnp-proofs/discussions/12644 on 2026-11-25. Its PG(2,3) search report has no displayed gate list; code links to an excluded host and was not fetched. Reconstructed a 63-gate near miss by deleting one edge from stars64. Independent Python checks all 52 edges and704 maximal independent sets (756 exact monotone boundary rows), with exactly one failing edge row. Local SAT repair now running from results/orch2583/lemmas/counterexample/pg3_local.py. This is finite computational exploration, not a Lean proof or lower bound.

## Multi-junk audit 2026-11-25T15:01:23.212501+00:00

L5412 excludes a least lift-fixed bipartite C4-free circuit with exactly two dirty ANDs when both are flag products: each is OR(Ci) AND OR(Di), with adjacent centers z,zp, Ci contained in N(zp), Di contained in N(z), both sizes at least2. Its 7686-line argument already accounts for2,3,4 centers via surgery. No automatic derivation of this flag form was found. Concrete structural obstruction: for matching edges xy,uv, (x OR u)(y OR v)(x OR v)(y OR u) = xy OR uv. Grouping the first two and last two factors gives two dirty ANDs, both singleton-free, and a top AND. This circuit is live, top form, lift-fixed, with no BelowF AND operand, yet not flag-shaped. It costs7 versus a3-gate read1 implementation, so leastness/cost is the decisive missing ingredient. Four shared ORs would make marginal AND cost3, merely tying the read1 construction; mixed-side ORs cannot be reused in ordinary projective-plane stars. No claim that this matching example refutes the posted plane theorem.

[2026-11-25 15:01 UTC, proof_strategy] Generic semantic clamping component CHECKED: `lemmas/proof_strategy/PrimeReplacement.lean` (207 lines,9217bytes), complete empty Lean diagnostics in matching `.build.log`, SHA256634f5b221ac59ec9a809a703e7f82eb77b8a5afcea84f899a21b28eae4b5dca8. `lower_wire_preserves` permits a monotone replacement r below an old internal signal, provided equality holds on every positive edge assignment. It proves full function preservation for arbitrary AO prefixes/suffixes. This supports deleting any signal false on all prime edge inputs; actual gate-removal/count preservation is not part of this semantic lemma.

Direct-star route: checked L7684 builds read1 star-cover circuit costing|E|+|A|+|B|-1; L4897/L7639 prove corresponding lower bounds only underread1. The missing unrestricted bound forplanes is N(q+2)-1. PR13723 supplies only3N-1 and does not solve2583. No direct unrestrictedcharging proof obtained; mixed dirtyANDblocks remain the obstruction.

Research source read2026-11-25: https://github.com/open-goat/pequalnp-proofs/discussions/12644 reports previous tinyC4free graph core-cover searches withoutviolations and PG(2,3)63gate annealing reachingonewrongboundaryrow. The author explicitly marks this weak evidence because the annealer alsofailed at70gates, where witnessesexist. These reported experiments were not independently rerun here. Source gives52positiveedge+704maxfalse=756 monotone-complete rows forPG(2,3).

## SAT finite Fano route (2026-11-25 15:02 UTC)

Explicit q=2 plane is GF(2)^3 orthogonality on seven nonzero vectors, with14 incidence inputs. There are21 minimal true rows and37 maximal false rows (21 size4,14 size5,2 size7), hence58 exact monotone boundary rows. A standard star AO2 circuit has27 gates; pinned solver sanity check is SAT. A26-gate search is running with a600-second bound. No counterexample or UNSAT certificate yet. Complete source/data/CNF/log artifacts live under `results/orch2583/sat`. `FanoFinite.checked.lean` kernel-proves plane axioms and both boundary coverage directions, including all37 maximal false masks; local Lean build passes with empty output. No full task theorem claimed.

Counterexample update 2026-11-25T15:03:14.585997+00:00:
PG3 localrepair first windows of3,4,5free gates UNSAT; three9freegate windows UNKNOWN at60seconds each. Positivecontrol pinned star64 SAT on756rows. status_review independently audited encoding and boundary (via opposite-side independent-set enumeration); scope is fixed-backbone only. Complete current data/summary/control logs preserved under results/orch2583/lemmas/counterexample; raw CNFs are reproducible in scratch.
Threeclause membership audit checks729 multiplicity profiles0/1/2:54 qualifying homogeneous quadratic bipartite C4free cases,42stars and12double-stars. Fourclause presence audit checks16384 profiles:334 qualifying cases, all forests. These are explicit computational cases, not Lean proofs; data and source preserved. Toolchain agent owns symbolic proof generalization.

PG3 localrepair round complete at 2026-11-25T15:04:29.030050+00:00: {'SAT': 0, 'UNSAT': 8, 'UNKNOWN': 4} across12windows. No counterexample. Complete stdout/stderr andresult JSON preserved in results/orch2583/lemmas/counterexample; manifest records hashes. CNFs stay in scratch and reproduce from pg3_local.py.
