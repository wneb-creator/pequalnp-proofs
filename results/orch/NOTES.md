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
