# pequalnp-pilot-51 — L-meta-3451

Only root holds lease. Exact statement: /tmp/oec/pequalnp-pilot-51/statement.txt. Allowed project import: PEqualNP.Defs. Use separate strategy files in results/orch/lemmas; do not edit final file or git state. Read CONTRIBUTING.md.

Goal: normalize 4-cycle-free bipartite incidence AND/OR circuits so all AND gates reject one-hot and nonincident pair assignments, no size increase. Desk sketch recommends a reduction, but eligibility has not been confirmed.

## Counterexample strategy 2026-11-25T00:34:42.143926+00:00

Definitions audit: ReadsBack rules out forward inputs; empty incidence has a zero-gate constant-false output-out-of-range witness; N=0 restrictions are vacuous. No defect found. Exhaustive binary AND/OR state enumeration for all 15 C4-free incidence graphs on 2+2 inputs found identical unrestricted and clean-AND minimum sizes, all at most 4 gates. Script results/orch/lemmas/counterexample_small.py; full output /tmp/oec/pequalnp-pilot-51/counterexample_small.stdout. Constants and unary/repeated gates excluded from this finite model; standard elimination makes them unnecessary for a nonconstant monotone minimum. This is sanity evidence, not a Lean proof.

Reduction draft: results/orch/lemmas/reduction.lean. Two stages use local good/single predicates and existing EdgeOwnership.gateVal/pairInput to remain compact. Source hypothesis character counts 904, 1232; checker prettyprinting still needed. No compile yet.

## Normalization strategy 2026-11-25T00:37:12.781981+00:00

General singleton-AND hoisting remains obstructed: a gate true at singleton x may also carry useful pair terms disjoint from x, and splitting those contributions can add gates. No complete normalization found.

Useful simplification: monotone wire rejection at a point-line pair implies rejection at either singleton. Therefore the target nonincident-pair clause implies both singleton clauses whenever every point/line has a nonneighbor. Under C4-free, universal-row relations are sparse exceptional cases (all other rows have degree at most one). Candidate self-contained Lean helpers are results/orch/lemmas/normalization_false_inputs.lean; awaiting cache before compilation.

## Stronger finite census 2026-11-25T00:38:39.459593+00:00

All 334 C4-free 3×3 labeled incidence graphs were checked computationally. There are 15 nonempty graph-function isomorphism classes under all six input permutations. Exact state BFS of binary AND/OR functions, quotienting by all 720 permutations, enumerated 236249 canonical states at six gates and all their possible seventh gates. Fourteen classes first occur at the clean upper bound |E|+minimum-vertex-cover-size−1 (sizes 1–7); the 6-cycle class (representative mask 427) never occurs through seven gates and has a separately truth-table-checked clean eight-gate circuit. A separate Python constructor verified every one of the 334 labeled graphs has a clean circuit at this upper bound. Thus no counterexample exists for N≤3 in the reduced binary model. Unary/repeated-input gates, constants, and duplicate Boolean functions can be eliminated in any least circuit for a nonconstant graph function, so this covers the original small cases mathematically, but is NOT a Lean certificate.

Search: results/orch/lemmas/counterexample_three.cpp. Full logs: /tmp/oec/pequalnp-pilot-51/counterexample_three_cpp.stdout and .stderr. Clean constructors: results/orch/lemmas/counterexample_clean_upper.py; all explicit witnesses: /tmp/oec/pequalnp-pilot-51/counterexample_clean_witnesses.json. Runtime for final C++ search: about 9.5s. Completeness: a function-state set records all available wire functions; every minimal useful next gate combines two distinct available functions. Function-equivalent duplicated wires can be deleted. Canonicalizing the entire set under input permutations preserves all extension possibilities.

## Toolchain environment — 2026-11-25T00:38:54.610353+00:00
- Kit toolchain/cache were absent. Official Lean v4.36.0 installed in `/tmp/oec/pequalnp-pilot-51/lean-4.36.0-linux`; use its `bin/lake` directly or set `PEQUALNP_REAL_LAKE` for tools queue.
- `lake exe cache get` fetched 3233 prebuilt modules covering 67 direct Mathlib imports from Defs plus Mathlib.Tactic; no Mathlib source build, no lake update. Full diagnostics: scratch `cache-deps.stdout` and `cache-deps.stderr`. Compressed download archives cleaned with cache clean! after extraction.
- `lake build PEqualNP.Defs` PASSED (scratch `build-defs.stdout`/`build-defs.stderr`). Agents may compile now.
- Whole filesystem only 7.9GB. Toolchain ~3.4GB, current partial Mathlib closure ~3GB. Full Mathlib required by checker cannot currently fit. Lean source confirms `.olean.private` is required for non-module imports; do not delete required private/IR files.
- Standard FUSE compressed filesystem under allowed scratch was capability-tested using libfuse hello example. Denied: `fusermount3: mount failed: Operation not permitted`. No mount bypass attempted.

2026-11-25T00:39:20.870549+00:00 Normalization helpers CHECKED by lake env lean, exit 0, empty diagnostic output. The final helper singleton_clean_of_nonedge matches the target singleton conjunction exactly, given Monotone2 and no universal rows/columns.

2026-11-25T00:40:05.468800+00:00 reduction/base worker: results/orch/lemmas/reduction_base.lean COMPILES cleanly with `lake env lean`. Proves empty incidence normalization, positive size for any nonempty incidence, N=1 normalization, and arbitrary single-incidence normalization via one AND gate. Full logs reduction-base-final.stdout/stderr under scratch; no full statement proof.

2026-11-25T00:43:30.852568+00:00 restriction worker: results/orch/lemmas/restriction.lean COMPILES cleanly (restriction-build4 stdout/stderr empty). Generic restriction of old m inputs to new n via Fin m→Option(Fin n); None means false. Exact size preserved, Monotone2 and ReadsBack preserved, full output semantics and per-gate value semantics, and AND-origin/rejection transfer. Namespace PEqualNP.Outside.L_meta_3451.Restriction. This supports isolated-vertex padding route reducing full theorem to pair-only cleaning.

## SMT and cycle exploration 2026-11-25T00:44:25.251726+00:00

Downloaded official Z3 5.3.3 wheel from GitHub release, extracted package into task scratch and removed own download archive. Retained one library copy, about29MB. counterexample_sat.py uses exact full truth tables, binary AND/OR, bounded earlier-wire selectors, duplicate operands/OR self-copy padding, essential-input and later-consumer constraints. Supports nonempty targets N≥1,k≥1 only. Independent encoding review passed; external normalizations for constants/unary/dead gates remain mathematical and no result is a Lean certificate. P4 threshold3 UNSAT /clean4 SAT; C6 threshold7 UNSAT11.5s /clean8 SAT3.8s corroborate independent BFS. Five paired N4 classes launched with90s timeout each. Unknown/timeouts give no lowerbound.

Two120s heuristic cycle searches completed without exact candidates: see counterexample_cycles.stdout; they are nonfindings only.

## Global substitution obstruction 2026-11-25T00:44:26.305937+00:00

Checked file results/orch/lemmas/global_obstruction.lean refutes a tempting local rule, not the posted statement. On six inputs let a=p0 OR p1, b=l0 OR l1, g=a AND b, r=p2 AND l2, t=g OR r, h1=t AND p0, h2=t AND l1, output=h1 OR h2 OR r. This 9-gate circuit computes the C4-free four-edge relation {(0,0),(0,1),(1,1),(2,2)}. The shared OR reader of g cannot select either factor uniformly: replacing g by a creates singleton p0, replacing by b creates singleton l1. A 6-gate clean circuit computes the same relation, so this is not a counterexample to L-meta-3451. Lean kernel decide checked the exact semantics, circuit model, sizes, dirty pair, both failed substitutions, and clean witness. Command lake env lean succeeded; full diagnostics scratch global-obstruction-004.stdout/stderr. Global proof needs absorption/OR-sharing analysis beyond arbitrary uniform factor selection; minimality may still force a suitable alternate gate or rewrite.

## Checked padding equivalence 2026-11-25T00:47:10.040757+00:00

The singleton condition is redundant at the global theorem level: PairNormalizes (posted claim with singleton conjunct omitted) is equivalent to the exact posted statement. Proof pads an isolated point and line, applies pair-only normalization, gets singleton rejection by monotonicity, then restricts dummy inputs to false using the generic Restriction package.

Checked source components: normalization_false_inputs.lean (179 lines), normalization_padding.lean (202 lines), normalization_bridge_fragment.lean (194 lines), plus reduction agent restriction.lean. Namespace aux.Restriction used in final bridge, and restriction source mechanically rewritten for combined check. Scratch normalization_bridge_check.lean compiles with exit 0 and no diagnostics. This is a proved equivalence, not a proof of PairNormalizes itself.

Global follow-up 2026-11-25T00:47:33.719884+00:00: the shared-OR obstruction has a cost-neutral repair: replace g=a AND b and t=g OR r by tA=a OR r and tB=b OR r; feed p0-filter from tB and l1-filter from tA. A smaller five-gate obstruction uses output=((p0 OR p1) AND (l0 OR l1)) AND (p0 OR l1), computing C4-free P4; neither factor substitution works, but distributing the two-centre filter uses the same three replacement gates. Thus filter OR gates can pay for factor splitting. Under C4-free, a rectangle with at least two points and two lines has at most one universal row centre and one universal column centre. A global proof still must handle other dirty AND outputs in frontier filters/operands; singleton-support geometry alone misses higher-order false minterms.

## Checked mixed-centre suffix surgery 2026-11-25T00:51:17.353938+00:00

results/orch/lemmas/global_surgery.lean proves a generic exact-cost local rewrite. For any prefix and earlier operand wires a,b,c,d, replace the three-gate suffix AND(a,b), OR(c,d), AND(last two) by AND(c,b), AND(d,a), OR(last two). Under pointwise prefix-wire dominance c≤a and d≤b, both circuits compute the same Boolean function. Both have exactly three extra gates; Monotone2 and ReadsBack are preserved from prefix hypotheses. The suffix OR gate pays for splitting a mixed-centre filter, so no single factor choice is required. No C4 assumption is used in this primitive. Command lake env lean succeeded with no diagnostics; logs scratch global-surgery-003.stdout/stderr. Both new ANDs are below the final OR output mathematically, giving a local cleanliness corollary; that corollary is not yet a separate Lean lemma.

## N=2 canonical witnesses 2026-11-25T00:53:55.055169+00:00

normalization_n2.lean compiles cleanly. Explicit clean circuits for all16 relations on Fin2×Fin2 have sizes [0,1,1,2,1,2,3,4,1,3,2,4,2,4,4,3] under bit order I00,I01,I10,I11. Kernel-checked decide verifies semantics, Monotone2, ReadsBack, and both AND-rejection conditions. from_size translates their size lower bound to the exact N=2 normalization conclusion; large_enough proves the result for every C with size≥4. The lowerbound agent is certifying the remaining size≤3 cases.

## Checked SAT boundary theorem 2026-11-25T00:53:55.627908+00:00

`results/orch/lemmas/boundary.lean` (123 lines) compiles with exit 0 and empty diagnostics (`boundary-003.stdout`/`.stderr`). Namespace `PEqualNP.Outside.L_meta_3451_aux.Boundary`. Every finite independent set extends to a maximal one. A coordinatewise monotone Boolean function equals the edge-existence function if it accepts every edge pair and rejects every maximal independent assignment. `maximal_iff_single_extensions` proves maximality iff inserting any absent vertex creates an edge. `boundary_complete_tests` matches SAT directly: test false assignments whose every one-bit extension is true. No symmetry/irreflexivity restriction on relation E is needed.

## Stronger checked surgery corollaries 2026-11-25T00:54:52.415773+00:00

Final standalone source: results/orch/lemmas/global_surgery_mod_false.lean (371 lines), a superset of global_surgery.lean and global_surgery_corollaries.lean; merge only one copy. New AND gates feed the final OR and are pointwise below the unchanged output; all prefix wire values are preserved. normalizes_suffix packages exact size/function, Monotone2/ReadsBack, and rejection of every output-false input by every AND, assuming the prefix already has that rejection property. normalizes_suffix_on_false weakens the two wire domination premises to assignments where original output is false, equivalently domination modulo the target function; this permits absorbed clean terms. All Lean checks passed without diagnostics, log global-surgery-mod-001.stdout/stderr. The global step still needs a theorem that arbitrary least C4-free incidence circuits expose such a pattern (or another no-cost surgery).

2026-11-25T00:56:33.413645+00:00 Four-input enumeration: finite_four_cert.lean and finite_four_sound.lean both Lean-check cleanly. Certificate kernel-decides absence from all AND/OR circuit truth-mask searches below minima [0,1,1,2,1,2,3,4,1,3,2,4,2,4,4,3] for the sixteen 2×2 incidence matrices. Soundness handles arbitrary Monotone2 ReadsBack circuits, all arities0/1/2, constants, copies, duplicate operands, and all outputs including out-of-range false. API Four.lower_bound_with_certificate; combined finite_four.lean adds actual certificate and wrapper lower_bound. Normalization agent uses this for N=2 full normalization.

## Boundary solver revision 2026-11-25T00:56:56.920881+00:00

Initial full-table N4 run: all five hardest graph classes, both unrestricted and clean at upper−1, timed out90s. No lower bound or counterexample follows from those results. Complete logs are mirrored in results/orch/lemmas/counterexample_sat_n4_*.

New exact encoding in counterexample_sat_boundary.py checks positive edge assignments and maximal independent negative assignments, plus all singleton/nonincident tests used by AND-clean conditions. All assignments are still checked independently for each SAT model. Input-automorphism lex leaders and boundary indexing independently reviewed. Boundary completeness has now also been Lean checked separately by toolchain agent (boundary.lean). Full25 essential N4 class paired census is in progress with90s percase, automatic smaller budget search after SAT, full solver statistics, no UNSAT claim for timeout. The revised C6 benchmark proves solverUNSAT at7 in3.3s, while separately verified clean8 supplies its upper bound.

2026-11-25T01:02:01.399393+00:00 BV tactic feasibility audit: pinned Lean4.36 bv_decide always calls nativeEqTrue in Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean, creating compiler-trust axiom; BVDecideConfig has no kernel alternative. Builtin tactic also demands direct Std.Tactic.BVDecide module, which no pinned Mathlib module imports; direct Std imports disallowed for this gap. Therefore direct bv_decide is inadmissible and no heavy compile was started. Kernel-safe repo LRAT.Checker/Link exist but are outside allowed project imports, so would require substantial vendoring plus certificates under512KiB. Counterexample agent supplied 17 C6 sample assignments and SAT benchmark; retained separately.

## Arbitrary-N support theorem 2026-11-25T01:03:11.225823+00:00

Support.normalize_supported proves the exact normalization conclusion for arbitrary N whenever all incidences lie in the images of two embeddings Fin2↪FinN, one for points and one for lines. No C4 assumption is required. Restricting original C to the four selected variables gives the certified N2 lowerbound. Renaming the optimal explicit N2 witness gives D of no larger size. Every AND of the canonical witness is pointwise below the output (new finite kernel-checked invariant witness_below), so all required rejection conditions follow from the alreadychecked false-input semantics.

Frozen fragments normalization_support_fragment.lean and normalization_support_final_fragment.lean compiled against the named module in scratch with exit0 and empty diagnostics.

## Checked singleton normalization without sharing 2026-11-25T01:08:01.763049+00:00

`results/orch/lemmas/singleton_formula.lean` (165 lines) compiles with exit 0 and empty final diagnostics (`singleton-formula-005.stdout`/`.stderr`). Namespace `PEqualNP.Outside.L_meta_3451_aux.SingletonFormula`; uses library `DMFormula`, no custom datatype. `normalize` proves every positive formula has an equivalent positive formula with no more leaves in which every AND node rejects every singleton. No graph/C4 assumptions are needed. `extract` exposes a singleton input through OR-only paths in a clean formula and removes one occurrence with exact leaf saving. The rewrite `(x∨A)∧(x∨B)=x∨(A∧B)` strictly reduces leaves and strong induction closes. This is a generic no-sharing theorem, not the posted circuit theorem. Shared OR DAG residual extraction remains the unproved cost-accounting step. See singleton_strategy.md for the failed bypass and ownership route.

2026-11-25T01:08:02.797610+00:00 Dependency support route COMPILES cleanly: results/orch/lemmas/dependency.lean. Self-contained Support.lean closure with only Defs+Mathlib.Tactic imports. Generic essential_card_le: any finite set of essential inputs has card≤C.size+1 for any fan-in≤2 circuit, no operation or ReadsBack assumption. Incidence activePoints.card+activeLines.card≤C.size+1, and each side separately≤C.size. Namespace aux.Dependency. Normalization agent uses active_sides_bound for stars and root uses total bound for all C.size≤3.

## Arbitrary-size star normalization 2026-11-25T01:10:11.112742+00:00

Star.construct builds a fan-in-two monotone ReadsBack circuit of at most xs.length gates for z(center) AND OR(xs), with every AND globally below the output. Star.point_star and Star.line_star use the checked active-side cardinality lower bound to prove the full normalization conclusion whenever all incidences share one point or one line, for arbitrary N. Original C needs only fan-in≤2 and exact semantics; C4-free, monotonicity and ReadsBack are unnecessary for this special case.

Frozen sources normalization_star.lean and normalization_star_final_fragment.lean, plus dependency.lean, compiled cleanly against namedmodule; logs normalization-star-final.stdout/stderr empty.

## Global strategy: contextual mixed-centre surgery checked

`results/orch/lemmas/global_context.lean` is a standalone 573-line superset of the prior surgery fragments. It compiled with exit 0 and empty diagnostics in `/tmp/oec/pequalnp-pilot-51/global-context-003.stdout` and `.stderr`. Do not combine standalone supersets without removing duplicate declarations.

The new `contextual_same_function` theorem permits an arbitrary monotone continuation after the three replacement gates, provided that the continuation and chosen final output do not directly read the two changed internal wires. The two domination implications c implies a and d implies b need hold only on assignments where the original global output is false. On those assignments all usable wires remain equal; on other assignments the replacement final wire increases and monotonicity preserves the true output. `context_equal_size`, `context_monotone_models`, and `context_back` preserve the circuit invariants. `bool_mass_nonincrease` and `bool_mass_strict` verify the local true-AND-count potential: on negative assignments the sum decreases strictly when ab was true but ab(c or d) was false. Full global exposure of such contexts remains unproved.

Primary research read 2026-11-25: Stasys Jukna, *Disproving the Single Level Conjecture*, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf . Section 3.5 discusses the |E| lower bound for SINGLE-LEVEL circuits on K2,2-free graphs. Section 8 records superlinear explicit lower bounds for unrestricted monotone quadratic circuits as an open problem at publication. Thus proposing a general exact m+vertex-cover-size-1 bound would require substantial new reasoning. Present-day status of that historical open question is UNVERIFIED. No claim here refutes L-meta-3451.

## All incidence circuits with at most three gates 2026-11-25T01:12:20.048943+00:00

Small.normalize_three proves the entire posted normalization conclusion for arbitrary N and any incidence relation when original C.size≤3, with Monotone2/ReadsBack/exact semantics. No C4-free hypothesis is needed in this finite frontier. The generic dependency bound gives activePoints.card+activeLines.card≤4; empty sides use false circuit, singleton sides use optimal stars, otherwise both active sides have exactly two vertices and the checked Support theorem applies.

Frozen normalization_small_fragment.lean compiled against cached namedmodule+Dependency+Stars, exit0 and empty diagnostics.

### Exact-output obstruction to pair-only contextual domination

Let a = p0 OR p1, b = l0 OR l1, c = p0 OR (p2 AND p3), d = l1. Take local h = (a AND b) AND (c OR d), then global output h AND (p0 OR l1). The original output is exactly p0l0 OR p0l1 OR p1l1, a C4-free P4 incidence function, by absorption. The domination c implies a and d implies b holds on every singleton and every crosspair; the prefix AND p2 AND p3 is weak-clean. But replacing h by (c AND b) OR (d AND a) makes the independent assignment {p2,p3,l0,l1} true. Therefore the checked context theorem must not weaken its full-global-negative domination premises to the posted singleton/nonedge tests. This concrete argument is mathematical, not yet a Lean-checked instance.

A safe general observation is that a wire false on every positive incidence-edge assignment can be replaced by false without changing the exact quadratic output: substitution only decreases the global output, positive edge certificates survive, and monotonicity recovers every positive assignment. This removes fully edge-inert residues, but does not cheaply extract a linear part from a wire that mixes useful linear terms and independent higher-degree terms.

Independent status_review review of global_context.lean: PASS, 573 lines, SHA-256 f193409f75138f594c4733cefdb942e0d7a501e62abe33948816a71728d86cbd. Scope of contextual semantics, read-back, excluded wires, and Boolean mass lemmas confirmed. No forbidden syntax or hidden full-normalization claim.

## Global strategy: edge-inert AND elimination, checked

`results/orch/lemmas/global_prune_fragment.lean` is a frozen imports-free 207-line fragment in namespace `PEqualNP.Outside.L_meta_3451_aux.Prune`. `global_prune.lean` is a standalone 272-line verification wrapper copying the final module's frozen wire-mono helpers because its `.olean` was temporarily absent. Compile `global-prune-007` exited 0, with empty complete stdout/stderr logs.

Main theorem `edge_active_normalization` applies for arbitrary N and arbitrary incidence relation, with no C4-free hypothesis. It constructs a circuit of exactly the same size preserving Monotone2, ReadsBack and exact incidence semantics, in which every AND accepts at least one positive incidence pair. The construction simultaneously replaces every original edge-inert AND with an empty OR. All new wire values are below the originals globally (`zero_fold_le`). On each positive pair, the entire wire vector is unchanged (`zero_fold_eq`), because every masked gate was already false on that assignment. Monotonicity then preserves every positive assignment; global decrease rules out new false positives. One simultaneous pass suffices, since every retained AND keeps its original positive-pair values. Independent review has been requested.

## N4 census completion and longer trials 2026-11-25T01:20:01.579431+00:00

The full25 essential 4×4 class unrestricted census completed:14 solverUNSAT at one gate below explicitly verified clean construction;11UNKNOWN at90s;zeroSAT. counterexample_n4_summary.json lists all cases. The clean-mode batch was stopped to respect the two-coreCPU quota:14 completed answers retained, class34097/budget8 marked unfinished (interruption is no solver verdict). Clean synthesis is unnecessary unless unrestricted finds a smaller circuit.

Extra optimum-dirt queries for P4, P4+edge, P6, C6 all returnedUNSAT for existence of any AND accepting a singleton, and separately for existence of any AND accepting a nonincident crosspair. These exact finite reduced-model results support but do not prove a general every-minimum-clean claim. Complete logs are in counterexample_sat_dirty* and counterexample_sat_dirtycross*.

CaDiCaL on ordered boundary CNFs reachedUNKNOWN90s for C8≤10 and9edge N4≤11 after over800k conflicts; sequential300s retries started after root renewed lease. SAT decoding validates CNF assignments, original SMT assertions, then the complete truth table independently. Binary LRAT for knownUNSAT C6 already4.84MB, larger than512KiB source cap even under ordinary compression; no kernel proof pipeline claimed.

## Compiled axiom audit 2026-11-25T01:23:06.974087+00:00

Independent `#print axioms` audit of all 277 source declarations in the frozen 3540-line compiled main passed. Complete stdout/stderr, wrapper, declaration names, source SHA256, and machine-readable summary are mirrored under results/orch/axiom-*. Every reported dependency is in {propext, Classical.choice, Quot.sound}; no sorryAx or custom axiom. Source SHA256 84d7fdba8950569d0e042945a623b1c18a69fb012574578f3f1f6b38209ffa60. This audit is not the repository checker and does not establish the posted statement.
Full-cache feasibility rechecked read-only: 494MB free; existing 3233-module closure uses 1.46GB private oleans plus790MB ordinary oleans. Full Mathlib aggregate directly imports8714modules; optional C/ilean/server cleanup cannot supply space for the missing required closure. No build outputs removed, no fake aggregate, no checker modifications. Official checker infrastructure fault remains.

Independent pruning review: PASS. Reviewer checked the exact 3540-line integrated main checkpoint and recorded `results/orch/review-partial-012.md`.

### Post-pruning structural route

Edge activity alone still does not promote small-test domination to full semantic domination: for a relation containing the edge p4-l0 and with p3 a different point, the gate e = p4 AND (l0 OR p3) accepts a real edge and is weak-clean, but e implies l0 only on singleton/crosspair tests, not on the same-side independent assignment {p4,p3}. Mixed useful terms and larger independent terms remain possible after edge-inert pruning.

A stronger invariant follows by choosing, among equivalent circuits under the original gate budget, one with the minimum number of ANDs. Every AND must then have a positive incidence edge whose GLOBAL output becomes false when that one gate is zeroed. Otherwise the downward edit preserves all positive edges and therefore the exact quadratic function, while strictly lowering the number of ANDs. This supplies an actual downstream sensitivity witness rather than mere edge activity. Global exposure through shared ORs remains unproved. A separate tight fragment is being checked for this invariant.

## Structural normalization attempt — 2026-11-25T01:29:30.419097+00:00

The rank-two / edge-trace route can safely use downward circuit edits: if the edited monotone circuit is pointwise below the old circuit and preserves every positive edge assignment, it preserves the full incidence function. This avoids the stronger false-input-context domination required by upward bypass rewrites. However, AND edge-essentiality does not itself give clean gates. Concrete P4 obstruction: points p,r and lines q,s; compute g=(p OR r) AND (q OR s), then F=g AND (p OR q). This uses five gates and computes exactly pq OR ps OR rq, a C4-free graph. Both ANDs are essential on every positive edge (zeroing either kills the entire output), but g accepts the forbidden pair r,s. Bypassing g with either child also creates a false singleton. The clean factorization p AND (q OR s), OR r AND q uses four gates, so a coordinated rewrite exists but cannot follow by deleting a nonessential AND.

A general proof still needs an accounting or simultaneous rewrite for shared mixed rectangles. The candidate exact lower bound |E| + vertex-cover-number - 1 would imply the target via clean star-cover circuits; it is substantially stronger than the checked dependency bound, and no proof was found. Repository note notes/note-1-edge-function-exact-size.md explicitly limits its checked exact lower bounds to forests, cycles, and long-thread graphs. Its cited lower bound for general K2,2-free graphs concerns single-level circuits, not arbitrary circuits. No literature claim beyond that repository text was established.

First-AND OR-only operands remain a possible tractable frontier: linear operand domination violations have singleton witnesses, and pure cross-bilinear operand violations have crosspair witnesses. Mixed OR operands can create same-side pairs and the P4 example shows why a complete induction must coordinate downstream filters.

## Global counting research

Research time: 2026-11-25T01:31:05.907073+00:00. No full proof or counterexample to the posted statement found.

A genuine three-part route to the stronger exact bound |E|+tau-1 is:
1. OR accounting: every fan-in-two monotone circuit for a C4-free incidence relation has at least |E|-1 OR gates.
2. AND cover extraction: its AND gates can pay for a vertex cover, equivalently at least tau AND gates.
3. Given a vertex cover T, construct the usual OR of assigned stars using at most |E|+|T|-1 gates and with every AND globally below the output.
The third part is constructive and already matches the repository's published general upper-bound discussion (notes/note-1-edge-function-exact-size.md, L-meta-105/L-meta-154). The first two are independent, smaller resource inequalities, not proved here. The repository's Defs/AndCountCircuit.lean shows the second is already an explicit research family. A nonminimal circuit could trade fewer ORs for extra ANDs (or vice versa), so neither individual inequality may be assumed merely from a total-size conjecture. Counterexample agent is testing both directions on C6 with at most10 gates; retain eventual exact SAT status separately.

Concrete obstruction to a rank shortcut: the C8 bipartite adjacency matrix with rows1100,0110,0011,1001 is C4-free and has matching/cover number4, but real rank3: (1,-1,1,-1) is a nullvector and its leading3x3 minor has determinant1. Thus ordinary adjacency rank cannot recover tau even on cycles. Nonnegative rank would recover the C4-free star-cover quantity, but deriving a nonnegative decomposition from arbitrary circuits is the unproved normalization issue.

Concrete obstruction to earliest-join star ownership, even after all ANDs are edge-active and singleton-clean: let g1=(a OR c) AND (b OR d), g2=(a OR d) AND (b OR c), output=g1 AND g2. The output is ab OR cd. Every AND accepts both positive pairs; neither g1 nor g2 is pair-clean, and the first join g1 owns two disjoint edges. Thus edge-inert pruning does not imply star ownership. The extra cleanup gates pay for this example, but a global disjoint charging rule is still needed when cleanup is shared.

The known selector-family single-level counterexample shape in Defs/SingleLevel.lean has a universal x0 row and columns indexed by graph edges adjacent to both endpoints. Every degree>=2 vertex creates a4-cycle with x0. Hence it does not directly refute the C4-free exact-count conjecture except in its trivial matching case.

## Global strategy: positive-edge sensitivity at minimum size, checked

`results/orch/lemmas/global_sensitive_min_fragment.lean` is the frozen imports-free stronger fragment, verified by `global_sensitive_min.lean` importing the current compiled module. `global-sensitive-min-001` exited 0 with empty full stdout and stderr. It reuses the existing `Prune` zeroing construction. The earlier `global_sensitive_fragment.lean` is superseded; do not integrate both because their declarations coincide.

Main theorem `Prune.edge_sensitive_normalization` chooses a globally minimum-size Monotone2/ReadsBack circuit computing the incidence function, then minimizes its number of ANDs. It returns the original size bound, model invariants and exact incidence semantics, explicit minimum size among all circuits of the model computing that relation, and the following sensitivity property: zeroing any AND destroys the global output on at least one positive incidence edge. A zeroed gate cannot introduce false positives. If all positive edges survived, monotonicity would preserve the exact quadratic function, and the AND count would strictly decrease at the same gate size, contradicting its choice. No C4-free condition is used.

This still does not prove the posted rejection clauses. As the normalization agent noted, the five-gate P4 circuit ((p OR r) AND (q OR s)) AND (p OR q) has both ANDs sensitive on positive edges while its first AND accepts forbidden pair {r,s}. A coordinated rewrite is necessary; a four-gate clean alternative exists. Thus sensitivity by itself does not imply cleanliness, although explicit global size-minimality rules out that particular nonoptimal circuit.

Independent sensitivity review: PASS for the frozen 119-line minimum-size fragment, SHA-256 d75fb4430943629662b9020989cbf26bc838fa0bc137c77cdff503f4b1c55ea3. Reviewer confirmed both Nat.find scopes, strict AND decrement, full exact-semantics argument, and absence of hidden C4/cleanliness assumptions.

The remaining exposure argument must make essential use of the original output rejecting every independent set. Pair-value graph operations alone lose higher-degree independent-set behavior. The checked context theorem therefore retains full-negative domination, and the exact incidence hypothesis remains essential when promoting preserved positive edges plus pointwise decrease to semantic equality.

Counting-query results (native Z3 evidence only, not Lean checked): C6 incidence mask427 with at most10 total binary gates and at most4 OR gates returned UNKNOWN after60.020 seconds (timeout). The same relation with at most10 total gates and at most2 AND gates returned UNSAT after57.429 seconds. Full stdout/stderr are in /tmp/oec/pequalnp-pilot-51/counterexample_sat_counts.stdout and .stderr; source is results/orch/lemmas/counterexample_sat_counts.py. The bounded AND result does not prove the unrestricted AND inequality, and the OR query establishes no lower bound.

2026-11-25T01:33:41.224999+00:00 Final frozen 3662-line main axiom audit PASSED for all 282 source declarations, including new Prune sensitivity/minimality lemmas. Only propext/Classical.choice/Quot.sound. Updated complete results/orch/axiom-* evidence; source SHA256 4a0687272d92a47f45a32d19edf41cf9ecee5a89eb59af23dfc54e0b471f7a2f. This remains an axiom audit, not the official checker or a proof of the posted statement.

## Counterexample worker 2026-11-25T01:34:33.304636+00:00

C6 gate-count experiments at total budget10: with at most2AND gates, Z3 reports UNSAT after57.43s; with at most4OR gates, UNKNOWN(timeout60s). These are bounded-total computational checks, not Lean theorems or general gate-count lower bounds. Complete logs retained in results/orch/lemmas/counterexample_sat_counts.stdout/.stderr. C6 CaDiCaL UNSAT CNF+binaryLRAT retained losslessly compressed in results/orch/certificates, with exact hashes/version/commands. Proof is not independently certificate-checked or Lean-checked; compressed pair totals2,099,772bytes.

## Counterexample worker 2026-11-25T01:35:05.546087+00:00

C8 (N4 mask43365) ≤10 binary monotone gates: CaDiCaL2.1.2 UNSAT exit20 after268.96s (allowance1200s). Verified clean11 upper bound already retained; hence reduced-model computational minimum11. This adds one settled class to the previous14/25 N4 classes, leaving10 unresolved after earlier90s timeouts. Complete solver/wrapper logs retained, exact CNF compressed in certificates/c8-ten.cnf.xz; no LRAT proof generated and no Lean-checked lower bound. N3-cycle CEGIS smoke found an initial falsepositive candidate, added maximal-negative tests7 and56, then produced a fulltruth-verified clean8 circuit. Starting N5-cycle≤13 CEGIS and nine-edge N4 mask51863≤11 CaDiCaL1200s concurrently.

## Global strategy: L-meta-3760 audit

See `results/orch/lemmas/global_3760_audit.md` for the inspected API and exact obstruction. Its general TopForm transform preserves strong-junk count; its general count retains an uncovered-edge defect; the stronger routing and budgets all assume a unique strong junk. Earliest strong junk in TopForm does have pure OR operands, but later junk filters remain uncontrolled. No large proof copy or import was made.

## Future finite target from reduction worker (2026-11-25T01:40:27.898599+00:00)

A colored selector lift replaces a universal selector row by one row per proper edge color of a simple graph H. Column e=uv has neighbors {u,v,color(e)}; proper coloring makes the incidence relation C4-free. For K4 with its three perfect-matching colors this gives the Fano-minus-one-line relation (7 rows, 6 columns, 18 edges), with clean star-cover upper bound23. No smaller circuit or transfer of a selector-family advantage is established. This target was suggested structurally and has not been synthesized in this job; current long searches retain priority.

## Global strategy: component/separator attempt

See `global_separator_audit.md` and complete 16-mask truth-table output `global_separator_restrictions.json`. A minimum P4 circuit restricts to a nonminimum star circuit; a two-junk matching circuit has separate junk-ancestry components coupled by a clean top, and abstracting one boundary produces a cubic function. Its nonempty input-zero restrictions have either two junk gates or zero, never one. This does not refute an optimal-counterexample isolation theorem, but no such theorem was derived.

## Subdivision and colored-selector lift review

Reviewed only repository definitions and the existing task computations. No historical circuit-size claim is assumed. Source definitions: lean/PEqualNP/Defs/SingleLevel.lean defines f_H = OR_e z_e AND (x0 OR x_u OR x_v). lean/PEqualNP/Defs/Subdivision.lean replaces each edge by a path of length2k+1; the cover accounting appears in MetaComplexity/Helpers/SubdivPlan.lean and SubdivFwd.lean. The repository note notes/note-1-edge-function-exact-size.md reports its checked cycle exact-size result (L-meta-106).

1. Uniform odd subdivision does not give a generic saving-preserving circuit lift. For m old edges and cover number tau, replacing each edge by length2k+1 gives m_new=(2k+1)m and tau_new=km+tau, so the star-cover benchmark increases by3km. But K2,2 has a3-gate product-of-sums circuit while its odd subdivision is C_(8k+4), for which repository theorem L106 states optimum 12k+5 for k>=1. A hypothetical old-circuit-plus3km construction would cost12k+3, two too few. Thus it loses exactly the original two-gate saving against the star-cover benchmark. This example is already single-level, so it is an obstruction to a universal transfer bound, not proof that every genuine multi-level advantage disappears.

2. There is a structural reason a black-box old output cannot help. In any proper edge subdivision (path length>=2), every positive pair has at most one old vertex. Therefore the old quadratic edge-function output is false on every new positive pair. In any monotone circuit computing the new quadratic function, zeroing such a wire preserves all positive pairs and cannot introduce a false positive; monotonicity then preserves the entire new function. The same observation applies to the ordinary vertex-edge incidence lift. A successful lift must reuse internal singleton behavior, not merely the old computed output. This is mathematical reasoning, not a new Lean declaration.

3. A less destructive alternative is to split x0 into one independent input per proper edge color of H, keeping column e=uv adjacent to rows u,v,color(e). For simple H this incidence relation is C4-free exactly when the coloring is proper: the only possible repeated intersection is between an old vertex row and a color row. Consequently at least maximum-degree(H) copies are needed. Original-vertex pairs share at most their own edge; distinct color rows share none.

4. For H=K4 with its3 perfect-matching colors, this colored lift is Fano-plane incidence with one line removed:7 rows,6 columns,18 incidences. Padding one isolated column yields N7 mask211519409853589. Counterexample agent independently checked C4-freeness, exhaustive cover number6, and a clean23-gate circuit on all16384 assignments; its artifact is results/orch/lemmas/counterexample_colored_lift.json. This is a future target, not a counterexample. No smaller circuit or advantage-preserving transformation was found. The simpler H=C4 with2 colors gives ordinary K4 vertex-edge incidence (up to transposition), with12 incidences and a15-gate clean construction.

5. A graph-cover lift has the same budget obstruction in a different form. In a2-lift, edge(p,l) connects channel t to t XOR sigma(p,l). Twist exactly one edge of K2,2: the lift is C8, for which repository theorem L106 states optimum 11; this job also obtained external solver evidence for that value. Replicating the3-gate base circuit in two channels and ORing costs7, but computes two disconnected C4 copies, not this twisted lift. Per-input channel renaming has sigma(p,l)=alpha(p) XOR beta(l), so the XOR of signs around every4-cycle is0 and cannot break it. Eliminating4-cycles therefore needs genuine edge-dependent routing; cheap input renaming/replication cannot preserve the original saving. This does not exclude a more sophisticated lift.

## Singleton-hoisting audit and a verified bypass rule — 2026-11-25T01:43:44.255355+00:00

Read the public meta map and per-lemma JSON records on 2026-11-25. The desk sketch says only that one clause of a singleton-hoisting move has a ten-gate counterexample; it does not claim that L-meta-3451 is false. The exact ten-gate clause witness remains UNVERIFIED: no row number is supplied by the sketch, and searches of nearby accepted rows and public singleton/one-hot titles did not identify it. In particular, L-meta-5393 is a different ten-gate example: it proves an explicit nested circuit has an equivalent SIX-gate circuit, not a normalization counterexample (source lean/PEqualNP/Outside/L_meta_5393.lean; https://pequalnp.com/lemma#L-meta-5393). L-meta-3451 and its singleton-only variant L-meta-3456 remain public conjectures.

A sound alternative is accepted L-meta-3710, source lean/PEqualNP/Outside/L_meta_3710.lean and https://pequalnp.com/lemma#L-meta-3710 (public JSON cached as normalization-node-3710.json in task scratch). For any graph edge function computed by an IsAO2 circuit (backward-reading AND/OR with exactly two inputs per gate), AND g=a AND b may have every read bypassed to a if b is true at singleton v and every singleton neighbor of v. The output wire is left unchanged. No C4-free assumption is needed. Reason: a new false positive x must have b(x)=0, hence contains neither v nor any neighbor of v. Adding v activates b and makes the old circuit true, while it cannot create a graph edge, contradiction.

This is only a sufficient condition. For a globally minimum IsAO2 circuit with singleton-true g, the condition must FAIL for both operands: g cannot itself be the output, and a successful bypass would make it dead and removable. Consequently every accepted singleton v has a neighbor missed by each operand. Deriving the condition for some earliest dirty AND would require a new structural contradiction; global minimality alone supplies its negation. The five-gate singleton-dirty P4 example ((p OR q) AND (p OR r)) AND (s OR q), computing ps OR pq OR rq, already defeats the condition under C4-free semantics and earliest-dirty ordering, but is not globally minimum (the clean optimum is four).

Counterexample worker reports prior SAT tests requiring a singleton-true AND at the known optimum were UNSAT for P4, P4 plus a disjoint edge, P6, and C6; those are computational evidence only, not a proof of the general assertion. Accepted L-meta-3653 handles one dirty AND under its stated normal-form conditions; L-meta-5280 handles an uncoupled singleton-dirty AND with additional operand/partner hypotheses. Neither closes the arbitrary shared/coupled case.

Cycle-source qualification: the subdivision/lift paragraphs cite `lean/PEqualNP/MetaComplexity/L106.lean` and `HasCircuitSize` in `lean/PEqualNP/Defs/MetaComplexity.lean`. The model permits arbitrary fan-in-at-most-two AND/OR/NOT circuits, so the theorem is not restricted to single-level circuits. We inspected those sources but did not rebuild or axiom-audit that dependency chain in this job. The general odd-subdivision cover formula is supported here by the mathematical argument in the independent research review, not by treating a statement definition as a completed proof.

## Counterexample worker 2026-11-25T01:55:13.262718+00:00

The N4 nine-edge target (mask51863) at budget11 remained UNKNOWN after the full1200-second CaDiCaL trial (exit0,1200.02s). Full stdout/stderr and compressed exact CNF are preserved, with hashes in lemmas/counterexample_n4_nine_extended.json. This result supplies no lower bound; verified clean12 remains an upper bound only. The stronger C8 singleton-dirty optimum query will use the freed core for at most300seconds. Colored K4/Fano-minus-line at22 gates continues on the other core.
