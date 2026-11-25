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
