# pequalnp-pilot-72: L-meta-6349

Exact cost 10 for the Fin 4 by Fin 4 bipartite graph with mask 5805. Only project import permitted: PEqualNP.Defs. Root owns target file and desk.

Strategies: upper explicit circuit (toolchain agent); SAT/Promise lower (lower_certificate); structural lower (lower_combinatorial); independent counterexample/review (status_and_review); root integrates and manages lease.

2026-11-25T06:09:44.313885+00:00 upper: Complete formula DP over 16-bit promise tables has minimum formula cost 11; a 10-gate witness needs sharing. Synthesizing 10-gate binary AND/OR DAG with SAT (868 variables, 11538 clauses); outputs independently checked before Lean.

2026-11-25T06:10:13.145430+00:00 upper DONE: SAT found a 10-gate DAG; independently evaluated all16 promise pairs, mask5805. Lean upper lemma compiles cleanly at /tmp/oec/pequalnp-pilot-72/upper.lean, 13 lines, sole import PEqualNP.Defs. Root notified for immediate review/push.

- 2026-11-25T06:10:26.591241+00:00 lower_certificate: public Promise.rep_lower44 is unavailable through allowed Defs import; precedent L_meta_5531 inlines 2282 lines of checker/link and a 5-gate LRAT proof, total427428 bytes. Bundled Lean bin/cadical supports LRAT. Exact enc2 Python translation generated m5805-s9.cnf (18274clauses21373nominal variables), 120-second independent SAT check underway. No target file changes.

## Independent review and finite search (2026-11-25T06:10:47.113737+00:00)

Upper component PASS: independently evaluated its ten binary gates on all 16 oneEach inputs; resulting mask is 5805, all references earlier, output wire 17. Import and format constraints pass. Partial only, full exact conjunction still pending.

C++ live-frontier search found no circuit of at most 9 gates for mask5805. It examines all256 initial subsets; only full8 input set passes complete positive-negative separation. Memoized search:165524 calls and4077 dead states. Without memo but excluding generated existing values:1756347 calls. Closest existing optimized routine (allowing generated existing values, singleton-only termination):3300198 calls, completes in seconds. Exploratory only; Lean proof remains required. Source and full outputs under /tmp/oec/pequalnp-pilot-72/status/live_search.cpp and live-search*.out.

After monolithic kernel OOM, independent first-step profiling: 82 op/retention branches pass separation. Largest has299077 C++ recursive calls (left0 OR right1, retain neither), 9% of monolithic. Next223909 calls (left3 AND right0, retain right0), then208393 each for left1 OR right2 and left2 OR right3, retain neither. Splitting by unordered input pair yields worst554593 calls (left0/right1),17% monolithic. All branches return false. Complete branch counts in /tmp/oec/pequalnp-pilot-72/status/branch-counts.out.

## Lower combinatorial update 2026-11-25T06:12:59.004715+00:00

Adapted checked finite live-frontier framework from L_meta_6350 to mask5805, exact bound9. All constants independently audited by reviewer. Monolithic all_front kernel decision hit cgroup OOM (8GiB). Existing L_meta_6347 chunk approach adapted in scratch lower-combinatorial/LowerSplit.lean: seven groups of four initial pairs; -j1 compile in progress. No certificate import required.

2026-11-25T06:14:44.323904+00:00 lower combinatorial: seven4pair chunks also hit8GiB OOM. Framework-only proof with sole import PEqualNP.Defs PASSED at scratch lower-combinatorial/FrameworkDefs.lean (no search), so Mathlib.Tactic can be removed entirely. Lower_certificate now prepares fine perop/perkeep branch facts; reviewer profiling smaller subtrees.

Adaptive C++ search splitting profiles (exactordered states): threshold10k:2169leaves,102splitnodes,178unique W values,max9891calls; threshold25k:1267leaves,38splitnodes,139values,max24575; threshold50k:878leaves,22splitnodes,95values,max39049. Raw128-bit literals estimate732KB/434KB/305KB respectively before options/reassembly; common W aliases can make all fit512KiB. Profiles status/adapt-*.out under job scratch. With valid guard excluding generated values already in frontier, threshold10k reduces to1468leaves,55splitnodes,159values,max9780,total1.70Mleafcalls.

2026-11-25T06:16:59.069832+00:00 guard strategy: scratch guarded-framework.lean now excludes dispatch output already in current frontier; completeness adds freshness from first_live.hout via frontier permutation. Edit ready, waiting on lower_certificate for low-memory compile slot.

2026-11-25T06:17:36.833237+00:00 guard DONE: guarded-framework.lean compiles exit0. Fresh-output pruning is justified by first_live.hout and perm.mem_iff; only helper proof uses deprecated if_neg (harmless warning). Root and certificate agent notified; no heavy tests running here.

2026-11-25T06:22:29.934824+00:00 Boolean guard DONE: guarded-bool-framework.lean (528 lines) compiles exit0; both dispatch and nextStates use List.contains instead of Prop membership, preserving completeness with List.contains_iff_mem. Includes all GenericGuard expansion helpers. Heavy benchmark delegated to lower_certificate; no active Lean process here.

- 2026-11-25T06:23:13.645456+00:00 lower_certificate: direct public enc2 SAT encoding validated on mask359/s5 (UNSAT) but mask5805/s9 timed out UNKNOWN after120s. Pivoted to finite live-frontier split. Proved nextStates/expand equality framework, combined checked Boolean freshness guard with reviewer adaptive10k DAG. Full candidate delivered in scratch lower-certificate/Candidate.lean (421456bytes,10098lines; SHA256546fe00661dc854d0103bb673e4fcdd52768b22c10aca2e0d1b35db6b1d6f181). Largest unguarded39k-call leaf passed; guarded40k leaf passed defaultthreads in21.69s but5.4GiB RSS, so final uses1468leaves each≤10k calls. Root owns full named build/check/push.

## Full independent red-team review 2026-11-25T06:24:30.116339+00:00

PASS candidate SHA256546fe00661dc854d0103bb673e4fcdd52768b22c10aca2e0d1b35db6b1d6f181 (421456bytes,10098lines). Exact mainstatement equals postedstatement. OnlyDefs import; format/namespace/scopedoptions clean; plainfile below512KiB. Branchdiff from initialbase adds only namedLeanfile; results untracked. Independently parsed actualsource and verified all1523states against separateC++profile, all55split childlists against freshPythonBooleanexpansion includingorder/budgets, all1523reachable,1468leaves,159validWaliases. Initialseparation forcesfull8inputlist. Semantic normalization/guard/expansion/final lower glue/upper sound. Actualkernelbuild and checker still required. Review script and full outputs: status/review_full.py and status/full-review.out under jobscratch.

2026-11-25T06:49:08.107659+00:00 checker environment audit: official CheckLemma.lean:355 imports full Mathlib regardless of proof imports. Installed cache has3233 modules versus8712 Mathlib source modules; missing full-root closure causes CHECKERFAULT, not proof rejection. Lean4.36 Environment.lean2443–2456 requires .olean/.olean.server/.olean.private for module-system modules. Current free260MiB; safely disposable cached .c341MB +.ilean118MB totals459MB. Reversible .ilean removal probe retained all5147 build targets up-to-date, then restored original file. Remaining full uncompressed closure size UNVERIFIED (official cache metadata gives compressed blobs only). SquashFS tiny test failed with fusermount3 Operation not permitted; no bypass attempted, no real artifact moved/pruned. CleanPR with explicit localcheckerfault and authoritative remote check is supported fallback.
