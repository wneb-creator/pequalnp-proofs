# L-meta-1768 shared research notes

Only root holds and renews the lease. Read gap.json and repository instructions first. Each strategy owns its own file under lemmas; report findings to root for inclusion here.

Goal: count top-side/junk-OR-reachable pairs in Ustar, bounded by a universal constant times circuit size plus one. Full proof preferred; reductions allowed after at least 20 minutes of real effort.

## 21:50 UTC findings
- Existing R_meta_1768_1 already splits exposed junk witnesses (27 times size) and residual nested junk. Avoid duplicating it.
- L_meta_1876 proves junk empty implies Ustar empty. L_meta_1878 (952 lines) proves a one-junk bound with constant 12; its trace relies on the unique junk gate.
- A target endpoint is in wmax of its junk gate; L_meta_1878 has reusable semantic argument. R_meta_1880_311 contains topContact and contactBound for junk antichains.
- Setup claim was inaccurate: no Lean/elan or warm cache is present. Toolchain agent installing pinned 4.36.0 into scratch; only 7 GiB free may constrain cache.
- Lease renewed 21:49:55Z; expiry 22:09:54Z. Root alone handles renewals.

## Target-specific core reduction under development
- direct_bound is implementing results/orch/lemmas/reduction_core.lean, theorem R_meta_1768_45.
- Hypothesis 1: essential support of graph has cardinality at most circuit size plus one (known independent result). existing_results will extract a checked proof.
- Hypothesis 2: selected-edge subgraphs with no degree1/2 vertices satisfy a universal linear edge bound.
- Peeling low-degree vertices pays at most2 per supported input, leaving a minimum-degree3 core. Borrow generic proof from R_meta_1735_5; no duplicate of prior exposed/residual split.
- reduction_design independently checks smaller hypotheses and plausibility.
- counterexample exhaustive finite cases through4 vertices found no junk in any least circuits; Python evidence only.

## Candidate prepared at21:52Z
- Final candidate lean/PEqualNP/Outside/R_meta_1768_45.lean (98 lines) is the target-specific3-core reduction. Source/import/namespace guard passes. Build and checker pending toolchain/cache.
- Essential-input premise already checked verbatim in L_meta_2074; extracted support_bound.lean has222 lines and stronger fan-in-only local lemma.
- Exhaustive peeling validation on all32768 six-vertex labeled graphs passed; Petersen remains a genuine core test with15 edges.
- No submission before22:08:40Z (20min real effort). Direct agent continues investigating whether core can be eliminated/bounded directly.

## Independent direct-proof conclusion
Singleton restriction at anchor u propagates neighbors through ORs and AND gates whose other operand is true at singleton u. Girth prevents two anchors sharing multiple neighbors but does not bound how their selected propagation paths differ. The missing global accounting is exactly the part retained by the3-core premise. Formula lower bounds do not imply this unrestricted-circuit result.

The reduction has passed independent source review by repository_review and reduction_design. Final exact conclusion confirmed against gap.json. No Lean build or checker success is claimed yet.

Delivery archive plan: preserve notes, experiments and complete validation outputs in an early commit on pnp/pilot-45, then remove results from the final PR tree. The PR diff will add exactly the reduction Lean file, while earlier branch commits keep all results accessible.

## Validation status
- Named module build PASSED (18421 jobs); source guard PASSED. First checked-build archive pushed to2854ee5909896fdd245a696790a45c9c83d50790.
- Initial reduction checker built verifier, then FAULT with exit137 during import/verification. This is not a proof rejection. Full logs retained.
- Toolchain setup has exact complete cached artifacts; Mathlib --no-build freshness check passed. Files backed by4GiB anonymousRAM cause memory pressure; transitioning to compressed disk storage is under investigation, checker unchanged.
- Publicdesk22:01Z showed2 checked reductions (1,417), leavingone slot; pending233 differs from our graph3core cut. Recheck immediately beforePR submission.

FUSE capability was refused by the environment, and no bypass was attempted. Native toolchain artifacts are being archived reversibly to free disk and reduce anonymousRAM. Actual checklemma binary confirms mimalloc3.4.5 accepts MIMALLOC_PURGE_DELAY=0 and MIMALLOC_ALLOW_THP=0; these runtime-only allocator settings will be used for retry. No proof,checker,or importedlibrary bytes are changed by them.

## Checker resource investigation
The third and fourth original-checker attempts also ended with native exit137 before a verdict. Storage was restored exactly after each. The enlarged phase passed independent auditing of102019 files/2306968399 bytes. The fourth attempt reduced pinned storage to2133220976 bytes but still exhausted8GiB memory. The next bounded approaches are retiring redundant RAM-holder processes and encouraging the Node launcher to collect its temporary verifier-binary hash buffer. Neither changes the proof, verifier, library data or sanitized Lean environment.

## Narrow proof imports
Deleting only `import Mathlib` preserves the full proof and exact statement. The named97-line module built successfully (5147 jobs), and the import/source guard passed. Its dependency closure is4069 modules instead of11096, removing7027 modules from the checker's separately loaded proof environment. The statement environment still loads the full pinned Mathlib. The compiled candidate is pushed at9b502f64bcc2eab6dbfccf0b32442467dd1ae270. Checker005 will use the previously tested storage wrapper; the new core-offload prototype remains inactive.

Checker005 also ended with native137 before a verdict. Full restoration and independent byte audit passed. The resource monitor now reads only128 journal bytes instead of parsing the full journal; whether earlier monitoring contributed to memory pressure is unverified. The reserved reviewed process handoff and unused-core offload remain the next attempt; no checker logic or Lean settings are changed.


## Checker006 and compiled-header evidence (2026-11-25 00:16 UTC)
The sixth original-checker attempt again ended without a verdict. Its exact report is `CHECKER FAULT: the verifier ended without a verdict (exit null).` The cgroup `oom_kill` counter rose from 5 to 7 during the attempt. Base storage and core storage restoration audits both passed. Full checker stdout, stderr and resource observations are archived under `validation/checker-sixth-*`; no checker acceptance is claimed.

The combined storage smoke reached the unchanged verifier's usage message and restored both storage phases; it was a launcher/storage test, not a proof check. The independent base audit covered 102,019 files and 2,302,175,326 logical bytes, and the core audit covered 655 files and 117,399,848 bytes. Complete small smoke logs and the successful no-build freshness output are archived.

The compiled-header reader and independent review found 11,211 modules and 61,249 import edges for Mathlib, PEqualNP.Defs, the candidate module and Init. All import flags were followed; all 68 third-import roots were retained. The separate source-based storage candidate estimate lists 417 modules, 1,667 artifact files and 397,385,544 bytes. None of those 417 names occurs in the compiled closure. This remains only a candidate estimate: native runtime tracing and fresh candidate-file identity checks are pending, and this evidence does not authorize excluding artifacts. Large graph/journal files stay in scratch; the compact summary records their hashes and full small-log hashes.

Current proof: 97 lines, SHA256 `191b2cda8c5f17e7b401f9a3b17a1678ba2c456ea294db429667d46d3b757983`. Named build and source guard passed; all six local checker attempts have faulted before acceptance. Baseline job start was 2026-11-24 21:47:32 UTC; this checkpoint is 149.42 minutes after that baseline.

The public desk snapshot at 2026-11-25 00:16:24 UTC still listed L-meta-1768 as open with two live reductions and an unchanged statement. Two competing reduction PRs remained pending in that snapshot; this historical capacity observation is not a reservation. The compact public snapshot is archived in validation/public-gap-1768-004-summary.json.


## Native trace diagnostic001 (2026-11-25 00:32 UTC)
The traced native verifier was killed by SIGKILL and produced no verdict. This was a diagnostic run only; it does not satisfy the original local-checker prerequisite. Both storage phases restored, and independent exact restoration audits passed: 102,019 base files/2,302,175,326 logical bytes and 655 core files/117,399,848 bytes.

The complete compressed file-access trace is preserved with native stdout/stderr, status, compressor streams, the five-second resource log and independent review outputs in `validation/native-trace-run001/`. The compressed trace is 1,267,325 bytes, SHA256 `f67618c8a9c0f421218b1339ac16dab21c79979b745e67ca8573d952d91c0fb5`. It decompresses completely to 129,299 records across three traced IDs, with no malformed/truncated records or working-directory changes found by independent review. The candidate .olean is opened at record 78,560; the review infers that the initial Mathlib+Defs import with loadExts=true returned before that point. Later loading ended in SIGKILL.

Extra-module and shared-library trace joins remain pending review; no new artifact exclusions are authorized by this checkpoint. Proof source remains 97 lines with SHA256 `191b2cda8c5f17e7b401f9a3b17a1678ba2c456ea294db429667d46d3b757983`. The preservation summary records hashes of every copied file and of the full decompressed trace.


## 00:34 UTC resource strategy
At 00:34 UTC, the full trace/header review supported a reversible exclusion of 583 modules, and root approved preparation. Setup is preparing a sealed backup of about 119 MB using unchanged phase code; the projected net memory saving is about 278 MB. Later execution paths were not all observed in the killed diagnostic run. Original checker007 is next after independent storage review. The alternate scratch whitelist/cache-compaction approach remains inactive.


## Checker007 preservation (2026-11-25 00:49 UTC)
Original checker007 returned exit 3 with the exact result `CHECKER FAULT: the verifier ended without a verdict (exit null).` The cgroup oom_kill counter rose from 8 to 9. Both storage phases were restored by the final resource observation at 00:48:04 UTC. Independent exact restoration audits now pass for 102,019 base files/2,302,175,326 logical bytes and 2,322 core files/514,785,392 bytes, totaling 104,341 files/2,816,960,718 logical bytes. No acceptance verdict was produced.

Complete stdout, stderr, exit status, five-second resource observations, monitor streams and review outputs are preserved in `validation/checker-007/`. Compact sealed-pack readiness/integrity metadata records the 119,486,056-byte backup and its hash; the backup itself and runtime manifests are not copied. The proof remains 97 lines, SHA256 `191b2cda8c5f17e7b401f9a3b17a1678ba2c456ea294db429667d46d3b757983`. The next resource candidates are exact evacuation of shared libraries and retained core artifacts, plus compaction of unrelated build backups; all remain inactive pending independent review.

Diagnostic precision: the earlier traced run used `results/orch/statement.txt`, while the original Node checker uses a private temporary statement copy. Statement bytes, module and kind matched; the literal statement pathname and complete argv differed. The diagnostic remains evidence about imports and storage, not original-checker acceptance.


## Checker008 and machinery preservation (2026-11-25 01:33 UTC)
Original checker008 returned exit 3 with `CHECKER FAULT: the verifier ended without a verdict (exit null).` The cgroup oom_kill counter rose from 9 to 10. Both storage phases were restored by the final resource observation at 01:31:27 UTC. Independent exact audits passed for 30,369 base files/2,366,053,928 logical bytes and 2,322 core files/514,785,392 bytes: 32,691 files/2,880,839,320 bytes total. The base audit includes both shared libraries and 112 retained-core files. There is still no local checker acceptance.

The reviewed allowlist preserved 115 exact small files (425,432 source bytes), with source/configuration/test/provenance files under `machinery/checkpoint-008/` and completed checker/smoke/audit logs under `validation/checker-008/`. All 104 originally hashed entries were unchanged; completed run outputs and the newly discovered readiness snapshot were hashed at copy time. The copy manifest records exact source and archive paths, sizes, hashes and purposes. No packs, large prepared/runtime journals, credentials or lease responses were copied.

Smoke001 remains a usage-only exit-3 result, not acceptance; its full stderr and all checker008 warnings are preserved verbatim. The readiness JSON is an exact historical snapshot and retains its pending-final-budget-confirmation label. The candidate remains 97 lines, SHA256 `191b2cda8c5f17e7b401f9a3b17a1678ba2c456ea294db429667d46d3b757983`.


## Reproducible Node GC probe (2026-11-25 01:44 UTC)
Five faithful probe seeds all completed with exit 0. The measured anonymous-memory reduction was 239,386,624 to 239,427,584 bytes (about 239.4 MB decimal) relative to the probe baseline. The candidate CLI settings are `--gc-global --stress-scavenge=1 --fuzzer-random-seed=1`; this is a reproducible launcher/hash-buffer probe result, not a measurement of checker009. Actual checker009 has not run at this checkpoint, and checker008 remains FAULT/OOM without acceptance. The checker source and 97-line proof hashes are unchanged.

Exact probe sources, observer, all small probe logs/argv summaries, Node flag-help evidence and the updated small checker monitor are preserved under `validation/node-gc-probe-001/`, with a complete copy-hash manifest. No binary, heap dump or snapshot was copied. The same checkpoint retains the no-lease gap-status response, complete compressed GitHub response evidence and the fresh public feed. The public feed updated at 01:42:03 UTC still lists L-meta-1768, two live reductions, the exact statement and Defs import, with pending PRs 10649 and 10907. The earlier GitHub summary's freshness limitation remains verbatim and is supplemented by this newer feed. Status/capacity observations are snapshots, not a reservation.


## Checker009 and generation002 preservation (2026-11-25 02:09 UTC)
Actual checker009 confirmed the Node buffer release: observed Node RssAnon fell from 246,184 KiB after hashing to 13,120 KiB later in the run. The 13,120 KiB figure is residual anonymous memory, not the saving. Native verification nevertheless ended with `CHECKER FAULT: the verifier ended without a verdict (exit null).` The original checker returned exit 3 and the cgroup oom_kill counter rose from 10 to 11. No acceptance verdict was produced.

Both storage phases were restored by 02:05:03 UTC. Independent exact audits passed for 32,691 files/2,880,839,320 logical bytes. Smoke002 had returned the expected usage-only exit 3 and is preserved as a smoke test, not acceptance. Full checker stdout/stderr/exit/PID/resource/monitor logs and full smoke diagnostics are archived in `validation/checker-009/`, alongside exact small source/monitor snapshots, active generation002/disk-core configurations, cutover/helper/recovery/reserve audit sources and complete small reports/tests. Historical metadata recovery records and hashes are retained; packs, large prepared/index/journal files and compressed historical bodies are excluded.

The checkpoint preserves 166 exact files totaling 590,037 source bytes; including manifests, the archive is 668,948 bytes (1,036,288 allocated bytes). The proof remains 97 lines, SHA256 `191b2cda8c5f17e7b401f9a3b17a1678ba2c456ea294db429667d46d3b757983`, and the original checker source hash is unchanged.


## Original checker010 accepted (2026-11-25 02:43 UTC)
The unchanged 97-line reduction `PEqualNP.Outside.R_meta_1768_45` passed the original local checker with exit 0 and `ACCEPTED (reduce)`. It emitted two children, used only `propext`, `Quot.sound`, and `Classical.choice`, and kernel re-checked 1,654 constants. The exit artifact was written at 02:43:05.898166 UTC; root observed success at 02:43:56 UTC. This is local acceptance; no PR has been opened at this checkpoint.

Complete checker stdout/stderr/exit/PID and resource/monitor logs, the exact source/statement/import snapshots, independent review and exact restoration audit streams are preserved in `validation/checker-010/`, with byte hashes and existing successful build/source-guard references. The auxiliary sampler was intentionally stopped at 02:39:25 UTC to release memory, so its resource stream ends before checker completion. Both storage phases were restored; independent exact audits passed for 32,748 files/2,990,839,320 logical bytes. Proof SHA256 remains `191b2cda8c5f17e7b401f9a3b17a1678ba2c456ea294db429667d46d3b757983`. Large machinery and packs are excluded from this immediate acceptance checkpoint.
