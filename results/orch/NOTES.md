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
