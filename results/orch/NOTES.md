L-meta-670 orchestration notes

Each agent appends a section with UTC timestamp, name, result and evidence. Root holds and renews the only lease for this session. Do not call the desk.

Assigned statement: no circuit with at most 15 gates computes the 9-input Petersen-minus-vertex edge function.

2026-11-25T04:39:24.450817+00:00 counterexample_search: Exhaustive enumeration of all 512 vertex subsets confirms alpha=4, vertex-cover number=5. Star cover yields 16 gates (12 internal star gates + 4 OR gates), consistent with posted lower bound. Exactly 12 automorphisms (all 9! permutations checked). Circuit-size lower bound for general AND/OR/NOT remains unproved.

2026-11-25T04:40:19.422591+00:00 case_decomposition: all 14 first-gate cases L_meta_1665..1678 exist, each 200--520KiB. L_meta_2440 is exactly the 584-line normal-form statement required by R_meta_670_713. Adapted its namespace to PEqualNP.Outside.L_meta_670_aux.Cases in results/orch/lemmas/Cases.lean, awaiting toolchain for compilation. L2442 bundles both NOT cases (511700 bytes), L2444 bundles all AND cases (379693 bytes). OR bundle L2446 absent; individual OR cases L1673..1678 present.

## Structural strategy, recorded 2026-11-25T04:40:53.123703+00:00
Existing L_meta_1001 proves the exact 16-gate upper bound. Graph has 12 edges, minimum vertex cover 5, and girth at least 5. Degree-two vertices are 4,6,7. Setting vertex 4 to false leaves an 8-vertex 10-edge graph with monotone expected complexity 13. Setting 4 true simplifies to x0 OR x3 OR the 6-cycle on vertices 1,2,7,5,8,6. These restrictions explain the reader cases in existing R_meta_670_718. General monotone bound would be 12+5-1=16; handling NOT is unresolved. Structural.lean drafted finite graph/restriction facts, not compiled yet while root restores toolchain.

2026-11-25T04:40:40.321667+00:00 toolchain_setup: Warm Lean/Mathlib state promised by kit was absent. Installed official Lean 4.36.0 release under /tmp/oec/pequalnp-pilot-67/toolchain/lean-4.36.0-linux. Verified release commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9. Mandatory lake exe cache get running; no tracked build configs changed.

## Structural literature check, 2026-11-25T04:41:13.351660+00:00
Read primary author manuscript: Stasys Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf (read 2026-11-25). Its introduction and Theorem 2.1 establish that arbitrary monotone circuits for quadratic functions need not normalize to single-level circuits at equal cost. Thus the star-cover expression |E|+tau-1 is an upper bound/conjectured exact value for this concrete graph, not a proved universal lower bound. A graph-specific normal form remains necessary.

2026-11-25T04:41:57.051965+00:00 optimize_existing: fetched PR12184 source (516536 bytes/5222 lines); exact theorem and allowed imports. Upstream build actually succeeded, then overall20min budget expired during kernel recheck (status_review evidence). PR12203 differs with KWRooms/single-factor pruning, more dense table encodings,523482bytes/6864lines, also timed out. Initial conservative dead-code pruning removes12unused declarations/60lines; Optimized.lean now513315bytes/5162lines but not compiled. Case agent produced forceBatch candidate to avoid repeated lazily computed packed fields; awaiting cache to baseline profile.

2026-11-25T04:42:04.086342+00:00 toolchain_setup: Setup complete. lake exe cache get exited 0, downloaded/decompressed all 9,117 prebuilt artifacts. Mathlib.olean present; pinned config diff clean. Build env PATH=/workspace/pequalnp-proofs/tools/bin:/tmp/oec/pequalnp-pilot-67/toolchain/lean-4.36.0-linux/bin:$PATH, PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-67/toolchain/lean-4.36.0-linux/bin/lake, PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-67/pnp-build. Full cache logs in /tmp/oec/pequalnp-pilot-67/cache-get.stdout and cache-get.stderr.

2026-11-25T04:42:33.532365+00:00 case_decomposition: BatchForce.lean compiled with Lean4.36.0 (exit0,0.057s), no imports needed. This proves CPS forcePacked/forcePackedList/forceBatch preserve values, candidate to force makeBatch packed Nat values once before rowCut checks. Not yet benchmarked against main certificate.

2026-11-25T04:42:37.621367+00:00 counterexample_search: Z3 full512-row synthesis of15-gate normalized AND/OR/NOT circuits with first gate NOT x0 timed out at120s (unknown), so no counterexample or lower bound obtained. Script and entire diagnostics in scratch/counterexample. Pivoting to evaluator-cost analysis of complete existing PR12184.

## Structural partial checked, 2026-11-25T04:43:52.013365+00:00
Structural.lean passed lake env lean (exit0, about5seconds, empty diagnostic log). It proves the graph facts and a partial lower bound8 using the general support lemma adapted from Helpers/Support.lean inside the permitted auxiliary namespace. This does not establish the target lower bound16.

2026-11-25T04:44:35.120031+00:00 case_decomposition: Cases.lean PASSED Lean4.36.0 via lake env lean, exit0,14.261s. Complete output results/orch/Cases-validation.txt. The normal-form component renames vertices by12 automorphisms and removes first constants/copies until first gate matches one of14 representative pair/NOT cases.

2026-11-25T04:44:43.235532+00:00 counterexample_search: LookupForcing.lean compiles in0.146s with Lean4.36.0; proves eagerNat lookupFast equals old lookupBase for all parameters. Source and complete empty output preserved in results/orch for immediatepush.

2026-11-25T04:45:51.320290+00:00 counterexample_search:3000-call checked lookup microbenchmark: original3.707s vs forced3.632s, same checksum10491. Difference only2%, no convincing major speedup. Both standalone Lean benchmark files and complete emptylogs preserved forpush. maxrss_kib field is cumulative child peak and should not be read as per-variant measurement.

## FastCost guard checked, 2026-11-25T04:46:17.334063+00:00
FastCostGuard.lean passed lake env lean (exit0). The optimization is an early test that total unavailable wire count is at most2, before fetching operands or scanning available wires. Initial fastCost equality compares this count to sum of two0/1 values, so count>2 must fail. guardedFastCost_eq proves exact equivalence for all QS values. Main source unchanged; optimizer owns integration and benchmarking.

2026-11-25T04:46:17.530397+00:00 case_decomposition: forceBatch optimization rejected by measurement. Definitions-only kernel benchmark for rootM depth12,start476,batch16,arity12: row0 original2.45s vs forced2.57s; all12rows original4.71s vs forced6.04s. Both versions check. Logs retained /tmp/oec/pequalnp-pilot-67/bench-force-defs.log and bench-force-rows.log. Next test lazy lanes avoids computing all bound pools before bitmask rejection.

2026-11-25T04:47:04.124321+00:00 case_decomposition: lazy-lanes experiment also rejected. Replacing forceLanes xs by xs.map laneOf preserves semantics (rowCutLazy_eq checked) but full12row benchmark original5.05s kernel versus lazy6.81s (+35%), exit0. Original evaluator retained. Definitions-only harness shared with structural_proof and counterexample_search for independent optimization tests.

2026-11-25T04:47:23.612406+00:00 counterexample_search: batchMove maskforce checked benchmark passes but offers no meaningfulgain. Kernel typechecking5.09s original vs5.01s forced; totalprocess15.233s vs15.876s. Rejectedperformancechange; copied bothchecked Lean benchmarks andcompleteoutputs into results/orch forpreservation.

2026-11-25T04:48:25.034669+00:00 optimize_existing: original named proof profiling in progress (Lean PID5449, -j2). Safe optimization benchmarks: forcing packed batch regressed full-row kernel time4.71s→6.04s; lazy lanes regressed5.05s→6.81s; forcing lookup hash/table values improved only~2%; forcing batch coverage mask improved only~1.6%, both noise. Keep baseline unchanged. Independent #12203 source has1471 monotone+698signed root states vs2736+761; upstream build~11m40 then verifier~7m57 timeout (status_review), compared#12184~15m build then4m38 verifier timeout. Testing noncomputable data to avoid generated code declarations next.

## FastCost benchmark complete, 2026-11-25T04:50:31.385046+00:00
Ten isolated runs of rootM level12/start476/16states/arity12/all12rows all passed. Static count≤2 guard and dynamic count≤deleted operand count guard showed no clear improvement within variability. Availability flags cached once in forcePool regressed. Full stdout/stderr, timing/source hashes, baseline and variant diffs are in results/orch/fastcost-benchmark; summary.json records exact results. Neither optimization was integrated.

## Independent noncomputable review, 2026-11-25T04:52:00.712929+00:00
Full candidate SHAaea723b22e0c is exactly PR12184 plus noncomputable markers on532 plain defs. Posted statement exact; only PEqualNP.Defs import; no forbidden root identifier, strings, axiom/sorry/native command, attributes. All17 hash symbols are array literals, no hash commands. Source523984bytes leaves304bytes under512KiB limit. Source review approved; full candidate build and checker remain pending.

2026-11-25T04:52:13.974760+00:00 case_decomposition: noncomputable-all-defs reduces olean11.63MB->1.72MB and compile19.48s->15.34s, but safe replay count remains680 and replay4.939s->5.295s. Both checked, allowed axioms only. Full candidate523984bytes; structural agent reviewing. Complete data/logs results/orch/compiler-bench/. No unsupported kernel-speed claim.

2026-11-25T04:52:44.624305+00:00 counterexample_search: Discarded initial batchwidth harness because one BooleanList.all wrapped96states into one kernel computation. Width16 and32 hit6500MiB; those failures are explicitly UNREPRESENTATIVE of separate-declaration checks and preserved with caveat. Corrected suite has one theorem per batch and is running.

## Sample width experiments, 2026-11-25T04:54:57.545757+00:00
Independent literal parser confirms all17sample arrays preserve every row pair in first278 positions. Generic source transform touches only27sample-dimension literals768 and25lane literals769 beforeg15d3; Sig512 and certificate suffix untouched. Width278 and320 passed representative rowCut benchmarks but showed no robust speed gain for16states. Full logs/diffs/timings retained; main source unchanged.

2026-11-25T04:55:30.114072+00:00 counterexample_search: Batch size comparison, same96 certificate states (rootM, level12, start476, arity12), separate declarations, all12 rows. Lean4.36 -j1 -M6500.
width16: PASS,46.587s process,35.8s kernel type checking, peak4185120KiB.
width32: PASS,42.160s process,30.5s kernel type checking, peak4804900KiB.
width48: PASS,39.918s process,29.9s kernel type checking, peak5402716KiB.
width96: FAULT at6500MiB kernel memory cap,70.831s process, peak6657016KiB.
Recommendation:48 is fastest measured,32 gives more memory margin.96 is unsuitable at6500MiB. These are local certificate checks, not the final theorem checker.
The earlier single-List.all harness was unrepresentative and is labeled separately.


2026-11-25T04:55:34.426940+00:00 root re-plan: focus full proof performance. Counterexample search returned unknown; structural partials and normalization are checked. Guards, forced batches and lazy lanes gave no consistent gain. Batches of48 checked the same96 states about14.3% faster than batches of16. Noncomputable declarations reduce compiler payload. Testing sample width320 as a possible memory reduction; no established standalone speed gain. Preparing full candidate while original baseline finishes.
