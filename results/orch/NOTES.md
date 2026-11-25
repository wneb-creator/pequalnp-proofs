# L-meta-2592

Exact assignment: /tmp/oec/pequalnp-pilot-101/desk-first.json
Statement: /tmp/oec/pequalnp-pilot-101/statement.txt
At least one NOT (possibly unused or multiple), at most 19 gates, Petersen graph. Allowed project module: PEqualNP.Defs only. Three live reductions already exist. All strategies append their findings here and use distinct files under results/orch/lemmas/. Only root holds lease, builds final, commits and pushes.

## Counterexample search initial
Exact brute combinatorics: Petersen minimum vertex cover 6; 5 covers, yielding 40 oriented-star 20-gate seeds. Function false on 76/1024 assignments. No semantic shortcut from invalid wire indices. Preparing truth-table local optimization to find 19 gates with NOT.

## Semantic audit (2026-11-25T13:52:27.552308+00:00)
- The posted assumption is at least one NOT anywhere, not exactly one; unused NOT gates count.
- FanInTwo restricts the gate operations to AND/OR/NOT and each argument list to length at most two. NOT ignores its second argument. Forward or missing references read false. Empty AND/NOT gates give true, at gate cost. No semantic loophole was found.
- The 15 edges in the statement match Petersen. The Boolean precedence is ordinary AND before OR.
- The naive dependency bound would only give at least nine non-NOT gates; the existing L_meta_4725 is strictly stronger and should be reused by inlining. Its proof normalizes with a non-NOT budget then minimizes total gates. Its branch-count inequality is branches.card + n + gates.length - 1 + notGateCount <= 2*gates.length. It derives six branch wires, hence 15 non-NOT gates for n=10.
- To exploit equality at 15 non-NOT gates, one must establish additional branch/read constraints. The existing theorem does not retain the original NOT count in the chosen least circuit: least_with_budget minimizes among circuits with nonNotCount <= original, and can change NOT count. Thus one cannot directly infer an equality-case normal form with exactly four NOTs from that minimizer. A total-size-and-NOT-budget preserving minimizer would need separate proof.
- R_meta_4727_53 reduces the remaining 1–4 NOT case to a signed BinaryCircuit lower bound. It compiles NOTs into polarity marks N, with N.card <= notCount and D.size + notCount <= original.size. SignedBound is still the mathematical hard part.

## Existing reductions strategy

- `R_meta_2592_271`: binary floor + circuits with 1–4 NOT gates. Binary floor is already checked in `L_meta_4725.lean` (3224 lines, 146284 bytes): `15 + NotBracket.notCount C ≤ C.size`. Its first-boundary/twin-group argument proves six branch wires. This rules out at least five NOTs under the 19-gate budget.
- `R_meta_2592_318`: last-NOT decomposition + separator. Decomposition already checked exactly as `L_meta_8295.lean` (66 lines). Remaining separator has prefix allowed arbitrary NOTs and monotone suffix.
- `R_meta_2592_408`: normalize invalid reads and trim output, then normalized lower bound.
- 1–4 NOT child is `L-meta-4727` (file absent, still unresolved). Its three reductions are R4727_1 (trivial case split; child L8021 only contradictory no-NOT case), R4727_17 (semantic signed compilation + lower bound), R4727_53 (binary signed compilation + lower bound). Both compilers already checked: `L_meta_6060.lean` and `L_meta_7227.lean`, respectively.
- Five first-gate orbits in parent `R_meta_651_1`: unary/constant, AND adjacent, OR adjacent, OR nonadjacent, AND nonadjacent. Unresolved parent first-gate children include L1888/L1890 (no main files). For OR nonadjacent (extra x0||x2), checked L5236 rules out 3–4 NOTs and checked L5238 rules out at least five; 0 and 1–2 NOT branches remain unresolved.

## Lower-bound strategy (13:58 UTC)

The generic first-branch-group theorem in L_meta_4725 gives 15 binary gates for Petersen, from n-1 plus six twin-removal groups. This does not presently strengthen to 19. A new standalone partial is at results/orch/lemmas/LowerBound.lean: normalized effective reads count NOT as unary; if every input has two reads and each nonoutput gate has one read, a NOT-containing ten-input circuit needs at least20 gates. It is not yet compiled (cache setup ongoing). Therefore a hypothetical size19 circuit must have a single-use primary input after normalization. For a single-use primary input v, merging it directly with another primary input u via AND/OR cannot compute Petersen: AND loses v-neighbor witnesses not equal u; OR loses witnesses distinguishing the unequal neighborhoods of v and u. The hard case is v first meeting an already-computed wire.

Read notes/note-1-edge-function-exact-size.md: |E|+tau-1 is proved only for forests/cycles/long-thread graphs; Petersen does not meet the long-thread hypotheses. Web search did not provide a usable generic NOT elimination theorem.

## Environment setup (2026-11-25 13:52:50 UTC)

No accessible prepared Lean or Mathlib cache existed. Downloaded official Lean 4.36.0 Linux release to scratch; verified version and pinned dependency manifest. `lake exe cache get` exited 0 and decompressed 9117 artifacts; full Mathlib.olean is present. No Mathlib source build and no lake update.

Command prefix for builds/checker: `PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/bin/lake PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-101/build-queue XDG_CACHE_HOME=/tmp/oec/pequalnp-pilot-101/cache PATH="/workspace/pequalnp-proofs/tools/bin:/tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/bin:$PATH"`. Bundled SAT solver: `/tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/bin/cadical`. Full logs are scratch files `toolchain-download.*`, `toolchain-extract.*`, `cache-help.*`, `cache-get.*`.

Reviewer reminder: the posted statement assumes at least one NOT anywhere in the gate list, not exactly one; multiple NOT and unreachable/dead NOT gates must be covered.

## Few-negations strategy 2026-11-25T13:53:46.412270+00:00

Checked partial `lemmas/FewNegations.lean`: both constant-replacement criteria compile. If the two replacements Q(x,false) and Q(x,true) are monotone in x, Q is monotone in its final bit, and Q(x,!H(x))=F(x), then (a) if every true x has a smaller true certificate y with H(y)=true, replacement false computes F; (b) if every false x has a larger false certificate y with H(y)=false, replacement true computes F. Applied to graph functions, H true on every edge input suffices for (a), H false on every maximal independent-set input suffices for (b). An essential NOT must violate both conditions. A single final AND after nonconstant monotone H fails at all-true; single final OR fails at all-false. Need further gate accounting to reach 20; no full proof yet.

## Counterexample search SAT audit
The 30-row necessary constraints (15edges+15maximal independent sets) are too weak with NOT: first-NOT SAT model has6NOT and682 wrong rows of1024; first-AND-edge and first-OR-nonedge also SAT but fail full truth-table validation. These are not counterexamples. Strengthened187-row CEGAR with1–4NOT underway in coordination with semantic_audit. Stochastic full truth-table search best current19gate approximation has9 errors and0NOT, hence also no counterexample.

## Focused hexagon construction ruled out computationally
Deleting vertex0 and neighbors1,4,5 leaves C6 on order[2,3,8,6,9,7]. Let H be its edge function and U=x2∨x6, V=x3∨x9, W=x7∨x8. Petersen f = H∨x1(U∨x0)∨x4(V∨x0)∨x5(W∨x0). Thus a10gate circuit exposing H,U,V,W would yield19 gates overall. SAT with U,V,W fixed as first3OR gates and H last, all64rows, nonconstant positive source wires, all remaining gates live: UNSAT with exactly1NOT (6.52s), and UNSAT with1–7NOT (10.67s). This is a restricted computational exclusion, not a Lean-checked lower bound or full-gap proof. Script search_hexagon.py; full artifacts scratch/counterexample/hexagon10*.

## SAT audit and CEGAR 2026-11-25T13:59:37.628224+00:00
- Minimal 30-row NOT-first SAT model is not a counterexample: independent decoder agrees on all 30 encoded rows but fails 682 of 1024 full truth assignments.
- Added unique structural selectors and at most 4 NOTs from checked binary floor. Batch NOT-first 187-row run returned UNKNOWN after 240 seconds; OR-nonedge 192-row and AND-edge 192-row runs ongoing. These constrain a full 19-gate nonpadding normal form, so no lower-bound completeness claim.
- Incremental native driver links bundled libcadical.a and libc++ archives through verified C API, freezes selectors, validates all 1024 rows, adds 16 bad rows per SAT candidate, and retains learned clauses. General first-NOT and specialized exactly-1-NOT variants running; latter includes 38 cofactor boundary rows from few_negations.
- Files: sat_validate.py, sat_cegar.py, sat_incremental.cpp under results/orch/lemmas. Full logs/models/CNFs in /tmp/oec/pequalnp-pilot-101/sat-*.

2026-11-25T14:01:13.919869+00:00 SAT log collision: counterexample agent independently launched OR-nonedge using the same scratch directory as semantic_audit. The duplicate overwrote original log/summary and was stopped. No SAT witness file exists there; original verdict is not preserved and must not be reported as UNKNOWN or UNSAT. Future jobs use agent-specific subdirectories.

## One-NOT input cofactor samples 2026-11-25T14:02:26.655364+00:00

`lemmas/OneNotSamples.lean` compiled with no warnings. For an AND/OR tail fed inputs followed by NOT x0, the full1024 truth table is equivalent to21true and17false cofactor boundarysamples. This is stronger than30global boundarysamples, which admit spuriousnonmonotone outputs. The bridge includes kernelchecked covers, monotonicity ofAND/OR folds, and the evaluation identity for an initialNOTx0gate. Exactrows are in theLeanfile; semantic_audit is usingthem in exactly1NOT SAT.

Found existing checked L_meta_8035 (490842bytes): Petersen-minus-vertex circuits ofexactly15gates with0NOT areimpossible. Padding smaller circuits withunusedOR[] establishes16lowerbound withoutcopying L1922 too. Main restriction obstruction: NOTa pluspositiveOR(a,A) andnegativeAND(!a,B) canremoveonly3gatesunder a=0 unlessadditionalstructureforcesredundancy. Ifa hasnootherdirectuses, monotonicityforcesA false oneveryindependentset containinganeighborofa; consequently independentminterms ofA mustdominate all3neighbors andhave atleast3vertices.

## Lower-bound compiler progress 2026-11-25T14:02:51.123938+00:00

Restriction.lean compiled (731 lines): root-model constant propagation now counts all binary gates reading a primary input through any chain of NOT gates. Proven `restriction_with_cutCost` produces an equivalent restricted circuit with nonNotCount(new)+cutCost<=nonNotCount(old), for an arbitrary seeded input map. The arbitrary map supports9-input Petersen vertex deletion via automorphisms. `inv_seed` and `originConstant_seed` discharge seeded input invariants. First534 lines adapted from checked L_meta_7493; original new proof starts at originStep. This is sound partial progress; it does not establish the posted19-gate lower bound. Root assembling the14-binary deletion floor, existing_reductions assembling first-binary compression contradiction to obtain16 binary globally.

## Exceptional OR/AND cut 2026-11-25T14:05:25.225517+00:00

`lemmas/OrCompanion.lean` compiled without warnings. Model the only hard three-deletion pattern as g=x0 OR A and h=(NOT x0) AND B, with no other x0 influence and monotone residual R. Its cofactors are F0=R(A,B) and F1=R(true,false). The checked lemma proves monotone A is false on every independent input of weight at most2. The finite graph ingredient: every such independent set avoiding0 extends by at least one neighbor of0 to another independent set; turning0 on then makes target true. Thus A true would make the falsecofactor at least the truecofactor there, a contradiction. This rules out all singleton minterms ofA and all nongraph pair minterms. Still missing cost or rigidity argument turning this into a20-gate lowerbound.

## Counterexample route checkpoint
Stopped stochastic search on orchestrator instruction. Independent Python validation checked43logged candidates on all1024rows: bestany9errors/noNOT; bestwithNOT10errors/unusedNOT. FullPetersenAND-edge(187explicitrows) andAND-nonedge(192explicitrows) eachUNKNOWN after300s. Hexagon10gatefree-prefix1NOT alsoUNKNOWN300s. No validcounterexample; noLeanproof fromtheseexperiments. SharedOR-nonedge logcollision excludedfromresults. Reproducible commands andlimitations: COUNTEREXAMPLE_SEARCH.md. No searchprocesses remain fromcounterexampleagent.

## Restriction and compression route (2026-11-25T14:08:39.220930+00:00)

Completed and Lean-compiled components from existing_reductions:
- PairCode.lean (128 lines): no pair of distinct primary variables can be compressed into one arbitrary Boolean code for Petersen; also explicit automorphisms sending vertex9 to any chosenvertex, inverse maps and 9-input lifts.
- FirstMerge.lean (116 lines): provenance-aware semantic agreement propagates through suffixes where neither selected input-origin enters any binary gate. NOT chains preserve ignored origins and are covered.
- FirstOrigin.lean (99 lines): every wire with a primary-variable origin computes a unary function of that variable; consequently any circuit computing Petersen has output provenance none.
- Compression.lean (86 lines): combines those facts with CutCost suffix accounting to refute a circuit whose first proper binary gate merges two distinct origins each entering at mostone binary gate in total.
All modules have compiled oleans under /tmp/oec/pequalnp-pilot-101/root-lemmas/; development-only imports are to be inlined in the single final source.

Target substantial partial: 16 binary gates for Petersen (therefore no <=19-gate circuit with >=4NOTs). Remaining assembly is the arbitrary-vertex deletionfloor14 (root CutFloor) and least-circuit firstproperbinary existence/literal form (repo_review FirstBinary).

Possible further strengthening, unproved: for a first AND of positive literals or OR of negative literals, fixing either inputfalse makes the gateconstant. If totalbinarycount<=16, deletionfloor14 permits at mosttwo removals; both inputs must have another binary consumer, and a consumer of the firstgate would have to coincide with both other consumers, requiring fanin3. PositiveOR does not admit this argument because fixingfalse only copies the otherinput.

## Toward17 binary gates 2026-11-25T14:10:15.744529+00:00

The proposed annihilator/fusion argument is valid for a first signed AND/OR gate H having an input u whose FALSE restriction makes H constant. Under binary budget16 and the14-binary Petersen-minus-vertex floor, each input literal lineage has at most2 binary consumers. If u has2 consumers and H has a downstream binary consumer outside those2, restricting u=false deletes at least3 binary gates, contradicting the floor. Otherwise its sole binary consumer K also consumes a literal of u, and H+K fuse to one signed binary gate (free NOTs). Any other consumer of H restores the third-deletion contradiction. Output cannot be only H or a NOT chain of H because Petersen depends on all10 inputs. This fusion needs minimum binary count, or the already-established16-binary floor, rather than just minimum total gates under a binary budget.

Exhaustive Boolean check: all64 choices H=AND/OR(signed u,signed v), K=AND/OR(signed u,signed H) produce one of14 functions realizable with at most1 AND/OR plus free NOTs; never XOR/XNOR. Full data: /tmp/oec/pequalnp-pilot-101/next-bound-fusion.txt.

LIMITATION: positive OR(u,v), equivalently negative AND(!u,!v) up to output complementation, has no annihilating FALSE restriction. Annihilation requires u=true or v=true, but that Petersen cofactor has an11-gate upper bound, so the14 deletion floor does not apply. Therefore this argument alone does NOT prove the full17-binary bound. The unsigned OR-first class remains a real unresolved case, not a Lean bookkeeping issue.

## First binary gate (2026-11-25T14:11:22.051732+00:00)

FirstBinary.lean now proves generic `least_first_binary`: a clean least circuit for a nonconstant function that is not any signed primary literal has a first AND/OR gate with distinct primary origins. Its preceding NOT-only wires each represent a signed primary literal matching provenance. Same-origin operands either alias an earlier wire or produce a constant, both excluded by leastness; the new no-constant lemma uses checked L7493 drop_core. Output includes all-NOT prefix, distinct u/v, both provenance reads, and an explicit Boolean code for the gate. Complete269-line source compiled in scratch; development import L7493 must be inlined for final submission.

## CutFloor compile and audit
Counterexample agent fixed two Fin.lastCases reductions in root-authored CutFloor.lean: simultaneous seed simplification, and local explicitvector equality for the nine-inputdeletedgraph. Build4exit0; CutFloor.olean readyinroot-lemmas. Axiomsauditfor allfive helperspassedwithonly propext, Classical.choice, Quot.sound. cut_floor assumesonly FanInTwo andPetersen correctness; cut_at_most_one addsnonNotCount≤15. No hiddenlowerbound premise. Forbiddenpatternscan hadnomatches. Sourceownershipreturnedtoroot; existing_reductions notifiedfor BinarySixteen assembly. Full logs under /tmp/oec/pequalnp-pilot-101/counterexample/cut-floor-*.log.

2026-11-25 14:14 UTC — existing_reductions: `BinarySixteen.lean` (61 lines) compiles, proving every FanInTwo circuit computing full 10-input Petersen has at least 16 non-NOT gates. Assembly uses L7493 least_with_budget, arbitrary-vertex CutFloor, FirstBinary.least_first_binary, and Compression.no_first_compression. Thus the original total<=19 target is impossible with four or more NOT gates. One/two/three NOT cases remain. All constituent modules are kernel-checked; final binary_floor axiom audit and independent review requested. Module is frozen for immediate checkpoint push.

2026-11-25 14:16 UTC — existing_reductions: `SixteenCorollaries.lean` (48 lines) compiles with exact canonical count corollaries: nonNotCount C.gates + PEqualNP.NotBracket.notCount C = C.size; 16 + notCount C <= C.size; size <= 19 implies notCount <= 3; four_nots_impossible. Module frozen, root/reviewer/inliner notified.

## Checked semantic classification 2026-11-25T14:22:49.822966+00:00
SemanticClassification.lean and SemanticAllInputs.lean compile with no output. The latter covers all nine inputs other than the initially negated input0, eliminating the stabilizer symmetry assumption. Each has 40 kernel-checked sensitive contexts. A first binary mate preserving that input through an AND/OR gate can only be the constant pair x0 and NOTx0, or an edge conjunction (not incident to the single-use input) combined through OR. SemanticFactorization.lean also compiles: mate_at_sensitive_input derives the needed mate value from a factorization independent of the input, and pull_absorbed_term moves an absorbed OR term to the output. These are partial lemmas, not the posted lower bound. Full validation metadata and logs are under results/orch/.

2026-11-25 14:32 UTC — existing_reductions independently reviewed frozen StrictRestriction.lean (370 lines, SHA256 2646d1c46eb3fd0a2997b06b40ac10f40ea2d93b8ab388aef7ee9ae93d7b39be): PASS. The maximum marked wire argument obtains the extra saved binary gate from liveness plus restricted-output nonconstancy; the semantic wrapper retains exact circuit evaluation and cutCost+1 budget. Six key declarations independently audited with only propext/Classical.choice/Quot.sound; complete log strict-restriction-independent-axioms.log, exit 0. Format scan found none of the forbidden patterns.

2026-11-25 14:32 UTC — existing_reductions: SignedRestriction.lean (64 lines) compiles with no warnings, frozen for review/push. signed_origin_status combines OriginConstant propagation with compiler Inv and signed wire semantics to identify the exact constant Stat under v=0. marked_of_signed_operand marks a binary output annihilated by either operand (AND with positive sign, OR with negative sign), supplying the strict-saving seed without redoing NOT-prefix compilation.
