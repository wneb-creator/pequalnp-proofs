# S06 solver performance and certified finite subcases

Owner: Mencius/S06. Updated2026-11-24 03:34UTC. Concrete results delivered within10minutes. Scratch root for every artifact below: `/tmp/oec/pequalnp-pilot-18/orch/S06/`.

## Outcome and scope

**3,692 unit-based RUP additions have been independently replay-checked against the unchanged original DAG CNF.** The unchanged DSR checker returned exit0/`s VALID` with `--forward --rup-only`. These clauses preserve the CNF's satisfying assignments. They do not refute the full CNF.

The work also supplies replayable UNSAT certificates for16 overlapping prefix-selector subcases,12 source choices inside theAAAA case, and one furtherAAAA source choice found by a single bounded solver control. No complete suffix-operation case, assigned shard, or global Lean statement has been refuted. No Lean source was written or compiled. No S01 normalization is assumed in any clause or certificate here.

Parent CNF SHA256: `38d93ec59a86378a8434b232d19b2b53e8cbc3c715e81432ee94db59ca6ace08` (11968variables,114566clauses). All checks use DSR SHA256 `e6894b5b74ac2c09b494344f397ec5111547aaa782cdb399f1a8b6835ecef84b`.

## Recommendation for the coordinator

After S08 reviews the final RUP package and the coordinator authorizes a launch, use the two available CPUs for **one serial solver/checker pair over17 unsolved exactAAAA fanin cubes,20seconds per cube**, at most340seconds of requested search wall time plus startup/checking overhead. Keep original supervisor19723 running.

`AAAA-right17-partition/manifest.json` contains each exact CNF/metadata hash and a complete proposed online-runner command as a JSON argument array. No command in this manifest has been executed. Use the unchanged CaDiCaL `--unsat` and online runner; solver/checker address-space caps are1024/2048MiB. The abort-file path is passed only as a sentinel; no lease operation is performed.

The suggested order is source wires14,15,16,17, then18..29, then12. Wire13 is already refuted by the retained direct certificate below. This prioritizes nearby cases where scalar propagation fixed over10400 of11968variables and an actual adjacent control completed in0.22s. Runtime for the unsolved cases remains unknown;20seconds is a budget choice, not a solve-time prediction. A timeout is UNKNOWN/ABORTED and leaves that cube open. A result for all18cubes would exhaust onlyAAAA; AOAA/AAOA/AAAO remain separate.

This is the most concrete capped second-search recommendation from the measured evidence. No new long solver or portfolio has been launched. After the coordinator's latest hold instruction, all further solver launches were held.

## Replayable preprocessing packages

Earlier stages remain unchanged so S08 can review the initially reported569-clause package independently of later stages.

| Stage | Added clauses | Proof path / SHA256 | Result CNF path / SHA256 |
|---|---:|---|---|
| First-level |569|`combined.drat` / `dad278648ab57d19bc4af884261eba40c0931c6f234ceb6485f998c50cf3991b`|`augmented.cnf` / `459714296e1b81ca589d3ad1f020606812e4cb29a1ad0cdf3273a94c0b702f0c`|
| Prefix lookahead |994|`strong.drat` / `b26cafe87463ab3b6a806275f67bbf146e2945fbf5e637aa3775a2c2f6fca992`|`strong.cnf` / `7eed87fcaa73613b91fecd7a56ede475679860012323ca5a3a37b2868cd5c1a4`|
| Suffix fanin lookahead |3692|`suffix-fanin/lifted-all.drat` / `f319ae4b04ce7c6910389dc7f60ed61c353417192c47a44def9b35cc784683c8`|`suffix-fanin/augmented.cnf` / `2d20f5647012ed07af999643828cd3ac7916d4f61417d966579a49862b05e879`|

The final replayable proof is119955bytes. The final CNF has118258clauses, unchanged variable numbering, and exactly the original clause body followed by these3692clauses. Metadata preserves the original decoding arrays and explicitly records parent/proof hashes. A future SAT model can use the unchanged original-model/all2048-input validator. A future UNSAT result for an augmented CNF must retain its preprocessing provenance; production online proof digests are still not replayable artifacts.

`probe.cpp`, SHA256 `2deef9ec207f5225f4d31c25351998733f3b39e533d2234d02c99b0cf11a09a6`, implements deterministic occurrence-list unit propagation and bounded exhaustive failed-literal probing. It is not trusted for soundness: every emitted clause sequence is checked independently by DSR. `build_probe_package.py`, `second_level.py`, and `suffix_fanin.py` reproduce the respective stages. Build/generation/full checker logs remain in this directory; stage manifests are `package.json`, `second-level.json`, `suffix-fanin/manifest.json`, and `suffix-fanin-summary.json`.

Initial root propagation fixes130variables. Probing derives195unit clauses and fixes379variables. Under the four existing operation cubes, further probing derives231/77/29/37units respectively forAAAA/AOAA/AAOA/AAAO. A local unit under cubeC is lifted to the clause `not C OR unit`; all lifted clauses are checked directly against the original CNF. The first five scalar jobs took under2s aggregate. Prefix-selector and suffix-fanin probing add425 and2698further clauses. These are implication consequences, not new normalizations.

Exact replay command for the final package:

```sh
/tmp/oec/pequalnp-pilot-18/solver/dsr-trim/bin/dsr-trim --forward --rup-only \
  /tmp/oec/pequalnp-pilot-18/original-dag-strong/original.cnf \
  /tmp/oec/pequalnp-pilot-18/orch/S06/suffix-fanin/lifted-all.drat
```

Expected verdict: `s VALID`, not `s VERIFIED UNSAT`. Full logs: `combined-check.*`, `strong-check.*`, `suffix-fanin-check.*`. Actual CDCL speedup from these additions has not been benchmarked.

## Exact certified subcases and partition

**Prefix family.** For every zero-based gate g in1..16, the original CNF plus the unit `rights[g][1]` is UNSAT: no model can select input wire1 as that gate's right operand. Sixteen fresh DSR RUP-only checks returned exit0/`s VERIFIED UNSAT`. `certified-subcases/manifest.json` gives exact variable IDs, exact statements, commands and every log/CNF hash. The shared995-line proof is18105bytes, SHA256 `5965d6717c76455b052dc1e6309d52c6c8253dc53e9d47a43f4270c07c8b39e4`. These subcases overlap and are not an exhaustive family. The same proof's final empty-clause claim is correctly rejected against the original CNF without a subcase unit: `negative-control.json`, `negative-empty-check.*`.

**AAAA partition.** Set operation variables2807,3072,3341,3614TRUE. Exactly-one right17 selectors partition this case by source wire0..29. The RUP package excludes0..11; twelve explicit empty-clause RUP checks verify those exclusions. Eighteen cases12..29 remain. A further coverage check adds the negation of every remaining selector and derives a unit-propagation contradiction. Thus the18cases coverAAAA. They are pairwise disjoint because the original exactly-one encoding forbids selecting two right operands. `prepare_partition.py` generates all inputs and performs these checker-only controls; it never invokes a solver. Full checks and hashes are in `AAAA-right17-partition/manifest.json` and its adjacent stdout/stderr files.

**One measured solver control.** Before the coordinator's latest hold message, one announced isolated run tested the original CNF plusAAAA and `rights[17][13]`, exactly the five units `[2807,3072,3341,3614,2851]`. CaDiCaL exited20/`s UNSATISFIABLE` in0.2206seconds; DSR independently replayed the retained proof and exited0/`s VERIFIED UNSAT`. This is a direct original-CNF subcase certificate, with no preprocessing or S01 consequence assumed.

- Exact input SHA256: `8cd01c32fc548d1457990d27ecdf83adcee657fc213963092caf72edfcf5641b`.
- Retained ASCII DRAT proof: `bounded-control/proof.drat`,1243473bytes, SHA256 `3e15055185b8fa99377cbda2b77ca7a5631cb22886665f7c23e461d2ed1920fe`.
- Solver SHA256: `2a0137451efde370d67b88aec26f1e902870f095b1204b07049a103bc6bbd647`.
- Full result, commands, all source/input/proof/log hashes: `bounded-control/result.json`; all four full solver/checker logs are adjacent.
- Limits were10000conflicts,5solver seconds,7supervisor seconds,1GiB address space and32MiB retained-proof file size. No limit was hit.

This control certificate is separate from the unit-based RUP packages. No further solver has been launched. No entire operation case is claimed checked UNSAT.

## Active-run measurements and remaining obstruction

At03:33:34, recovery2 elapsed811.6s, emitted309.0MB/7.64million proof records, and had peak RSS105.8MiB solver/399.5MiB checker. The relay had393216bytes pending, below its1MiB bound. The earlier03:25:49snapshot had164.1MB/4.84million records and80.2MB/229.6MB peak RSS. Full snapshots and a window calculation are `live-snapshot-1.json`, `live-snapshot-2.json`, `live-rate-analysis.json`.

The465.995s window averaged5993records/s, which would take another15411s to the100million-record guard if maintained. This is only a measured-window extrapolation, not a forecast or remaining-search estimate. The earlier startup-average118minute extrapolation was substantially faster and should not be used as a deadline. No current record/memory/relay guard warrants restarting supervisor19723. Continue observing checker address space because its3GB limit concerns virtual allocation, not only RSS.

The precise obstruction is unchanged: all four broad operation cases survived scalar probing, and the checked subcases do not exhaust any broad case. Their conditional fixed points and CNF hashes are preserved for further search. S01's pending existence normalization could removeAOAA from a new search, but it is not an implication of the existing CNF and was not mixed into this work. S04 found no original-DAG completeness blocker, and S03's40-row sufficiency proof now supports candidate verification. The next useful S06 step is the coordinated capped exact-cube sweep above, not further unaudited encoding restrictions.

Only this report, S06 scratch artifacts and flock-protected NOTES appends were written. No active worker, named Lean file, other agent output, lease, credentials, git history or remote service was modified.

## Completed serial wave and archival handoff,03:47UTC

Main independently reviewed the frozen282-line controller SHA256 `bd2366dc9770fe35268092f06cbdbec0511a90585fee54bbd5fbb0b72cfc3e98`, including the exact four-log-key/byte-count/SHA256 checks. Nine bounded control groups passed using simulated processes; preflight passed all17pinned cases. Main launched the sole production wave at03:40:01. It completed at03:44:07: five new online-checked UNSAT cases, right-source wires14..18; twelve time limits, wires12 and19..29; no SAT indication. The queue's exit0 means completion, not exhaustion. The source and original worker were untouched throughout S06 read-only monitoring.

The production runner retains proof hashes/full logs, not replayable production proof streams. The earlier wire13 DRAT and all RUP consequences remain retained replayable evidence. S08's final package/partition review PASS is bound to SHA256 `6a5daee23ed457fecf8c280e23dea6a42bfbd4eb98eb3f0fb9ff012ac748efad`.

`orch/S06/archive-wave1/` is prepared for main's review/copy/push. It includes reproduction sources, full original and independent checker logs, retained RUP/direct DRAT proofs, partition metadata, all completed controller/runner records and logs, and controller controls. No raw CNF or compiled binary is included. `cnf-recipes.json` plus archived clause deltas reconstruct126exact parent-derived CNFs, including all production input/snapshot copies; reconstruction was verified in memory against every recorded byte count and SHA256. `omitted-files.json` records omitted CNF/binary/TSV hashes. `manifest.json` binds the archive contents. Full archival generation/reconstruction diagnostics remain alongside the archive. An initial packaging-only failure on a deliberately malformed controller-test CNF was corrected; the failed archive and complete diagnostics were retained separately, and no proof or controller source changed.

Next authorized direction: after S04's independent chain-normalization review passes, perform bounded unit/failed-literal consequence generation and exact cubing against each distinct S01chain parent. Every added clause must receive a checker replay against that exact parent. Do not rerun the twelve timed-out old cubes or launch a new production solver from S06.

## AAAO-chain follow-up: checked absorption cuts and exact two-case split

After S04's chain review PASS (`299f6bdc23ac20e8f9b54cae7eb3a787c1aacf951ab08b8314be212c67f1472d`), main launched AAAA-chain separately. S06 worked only on copies of AAAO-chain parent `a8e94b6cfeaafb8b6c4e01d33e6f552a984e395d224dc3d6281d99cc49850753`,115946clauses/11968variables. The active AAAA and original solver inputs were untouched.

The chain computes `P OR (((a AND b) AND c) AND d)`, with prefix-wire leaves and the reviewed order `a<=b<c<d`. Replaying the old3692RUP clauses against this stronger parent is sound and was independently checked again. Bounded probing then derived67rootunits and12conditional units in about one second aggregate. All four broad operation cases from earlier work remain separate; this is only AAAO-chain.

A further5.94second scalar job refuted all68cubes `P=w AND factor=w`, for prefix-gate wires `w=13..29` and each factor `a,b,c,d`. Each local unit proof ends in the empty clause; lifting it emits the binary exclusion of that pair. The complete lifted proof was independently checked against the exact AAAO-chain parent by unchanged DSR `--forward --rup-only`, exit0/`s VALID`. This is the encoded form of absorption: if P were also a product factor, the entire output would be P, requiring the clean prefix alone to compute the target. Soundness of the delivered CNF consequences rests on the replayed proof, not on this informal explanation.

The accumulated3895-clause proof also contains `[3644,3371]` and `[-3644,-3371]`. Variable3644 selects the last prefix wire29 for final OR operand P; variable3371 selects wire29 as product factor d. Liveness and sorted-factor restrictions force one, and the checked absorption cut forbids both. Thus there is an exact two-case XOR partition:

| Case | Unit cube | CNF SHA256 |
|---|---|---|
| Last prefix is P | `[3644,-3371]` | `433a5667dbf600990410a6579b5c332a1738fbe78777bcf5ebec2220ab4638c3` |
| Last prefix is d | `[-3644,3371]` | `e0021fcf9b3e6c014763f7f6f5b3378b0fec386019944966bbc519da254f9c74` |

Both excluded Boolean assignments, `[3644,3371]` and `[-3644,-3371]`, have separate replay-checked RUP refutations directly on the chain parent plus their two units. Neither remaining case has been solved. No production solver was launched, and no Lean or full-shard claim is made.

Artifacts are in `orch/S06/AAAO-chain-absorption-family/`. Global proof `combined.drat` SHA256 `8e937b00f88bc1b24b1dec5586c774af36215fc8f2ddbb7397bcdba55a3dcdc8`; augmented CNF SHA256 `2c7d3f950b6f8b6093b78b36369a0f675b01aa4b2878583b8fc04aa101245682`; excluded-pair proof SHA256 `8c3d367d53fe64dc016141a0f8c20d2d14b1cbe79337963a288979ec5c12e4e3`. `AAAO-chain-handoff.json` inventories every source, CNF, metadata file and full diagnostic. Reproduction sources are `probe_AAAO_chain.py`, `split_AAAO_chain.py`, and `probe_AAAO_absorption.py`, reusing the unchanged reviewed scalar probe. Source hashes are recorded in the handoff.

Recommendation: review this exact parent-bound RUP package and two-case split as a future AAAO-chain search input. Do not add its clauses to the active original input without their chain premise. Both current production pairs remain under main's sole control.


## 2026-11-24T04:07:25.411448+00:00 — bounded retained-DRAT runner ready for review

Status: code ready for independent S08/main review; no production launch and no real solver/checker/validator executed by this adapter. Source frozen at SHA256 `aa5d13bb83ab79e47b9794809c3c06dc153544975cd1131afbdeaef7c18d484a`.

`offline_checked_cadical.py` runs one pinned child at a time. CaDiCaL retains binary DRAT under 600-second wall, 1536-MiB address-space and 512-MiB per-file limits. A completed solver exit20 with the sole verdict `s UNSATISFIABLE` is necessary before the independent pinned DSR checker starts. The checker has a separate 600-second wall, 3072-MiB address-space and 64-MiB per-log cap. Only checker exit0 plus the sole verdict `s VERIFIED UNSAT`, unchanged pinned inputs/binaries/proof, and no abort/limit yield runner exit0 `VERIFIED_UNSAT`. A SAT exit10/verdict invokes the pinned full2048-input validator with30-second wall; exact provenance and <=21 gate limit are required for exit10 `VALIDATED_SAT`. Other outcomes are exit2 `UNKNOWN`.

Fresh output directories, immutable CNF/metadata snapshots, before/after hash checks, abort sentinel, SIGINT/SIGTERM handling, child process-group cleanup and parent-death SIGKILL are implemented. Full attempted-stage stdout/stderr, commands, phase exits/limits/CPU/RSS, proof bytes/hash and atomic progress/result are retained. Partial proofs remain explicitly unaccepted. Each controller slot must be held through checking or validation: filling a newly freed solver position while its checker still runs would exceed the intended child count. There is no scheduler or global disk reservation in this adapter.

Nine simulated subprocess control groups passed with actual test-process exit0 (5.275s): sequential acceptance; UNKNOWN/crash/exit-verdict mismatch/missing or malformed proof; file/record caps; bad checker verdict/exit/proof mutation; full SAT validation including size22 and provenance rejection; abort/hash/disk guards; fresh-directory refusal; solver/checker timeout escalation; active-child abort. All complete fake-process fixtures/logs are retained under offline-controls/. The test summary and exact source/log hashes are in offline-controls-final-result.json. These tests exercise plumbing with fake executables; they do not verify real binary-DRAT compatibility. A production-input preflight passed, hashing the real pinned binaries and AAAO input/metadata without starting any child or creating its output directory. Independent review remains pending at handoff time; any real compatibility control or launch is for main to coordinate.

The 64.580-second sample ending04:04:28UTC measured original solver/checker0.465/0.993 average CPU cores and AAAA solver/checker0.603/0.990. Total checker CPU1.983, solver CPU1.068. Original relay held its full1MiB buffer, consistent with checker backpressure; this is an inference, not a profiling result. Retained mode removes checker work on UNKNOWN cases but may increase unthrottled proof growth and adds later checking latency. A complete pipeline can take600+600 seconds plus snapshot/hashing overhead (or600+30 for SAT), rather than600 seconds total. No throughput improvement has yet been measured.

Free scratch was12.534GiB at04:04:28UTC. Four proofs at512MiB consume at most2GiB per wave; incomplete proofs are also retained. The solver per-file cap also bounds each stdout/stderr separately, so proof storage is not the full worst-case disk bound. Reserve additional log/snapshot space and the default1GiB free-space floor. Admission checks one proof cap plus the floor per process; main must budget the whole batch before launch. A four-slot batch may temporarily run four checkers, each capped3GiB address space. Current active pairs remain untouched.

For04:12, if main frees two slots and runtime review/control passes, the two independently reviewed AAAO chain cases are a concrete capped portfolio. They are an exact partition of that normalized parent, not global exhaustion: [3644,-3371] and [-3644,3371]. The former uses last-prefix wire29 in P, the latter in d. Avoid repeating the broad old20-second cubes. Recommended initial retained cap is600seconds/512MiB each, then decide from actual proof rate and search statistics; no automatic resubmission. Main alone chooses whether to replace the older online pair.

Archive2 should include the AAAO handoff and source generators, exact parent/generator/hash bindings, all3895-clause RUP evidence and full checks, both excluded-assignment proofs/checks, exact2-case manifest, S08 AAAO independent review/full replay logs, this runner plus final controls/full fixtures/preflight/resource samples, and the pending independent runner review. Preserve old and final control records under distinct filenames; old source hashes describe historical tests. Large raw CNFs may be represented by checked parent/delta reconstruction. No archive2 completion or independent runner PASS is claimed here.

Handoff `orch/S06/offline-runner-handoff.json` SHA256 `19192c58c5a4075e92e6744b1f2052eda7afa5db01973db2e220c8c74e4459ca` inventories 614 full source/control/log artifacts and two proposed commands (not executed). S08 AAAO review now PASS: `orch/S08/aaao-chain-review-v2/review.json`, SHA256 `5ce1515a74ede401f5324f2940a08e4276e069887f960a080f14c038891cbe97`.


## 2026-11-24T04:12:41.235166+00:00 — archive2 ready for independent packaging review

Final package is `orch/S06/archive2-final.tar.gz` (3,239,216 bytes), SHA256 `de4ba452cf2b996aa8fe89987bf4c61711eca8e8c92175cb6df1be5586e2b373`. Internal manifest SHA256 `005189a6921f0d52b442d5e26703b05b86482010e7ab5dc0247a77297fe98519` binds1783 files; tar has1784 regular members including the manifest. All file/tar hashes and95 reconstructed large CNFs passed local validation. There are137 tiny raw CNF fixtures, no bulk raw CNFs and no compiled binaries. All probing statistics and full diagnostics are retained.

Included: AAAO3895RUP plus exact two-case partition, all local proofs/checks, S01 chain source/input recipes and S04 normalization review, S08 AAAO review/full replay logs; frozen offline runner aa5d13... with9 S06 and14 S08 simulated controls/full fixtures; main's actual wire13 compatibility run (0.669s,417878-byte binary DRAT SHA8125b968b7872be6b0c65d3d9fce9231364fd6e1e06a19c951b7752d730c320d), exact input recipe/full solver and checker logs, and S08 independent replay review c1a224.../full logs. The current P/d production jobs are outside this snapshot. This is no global/shard/chain exhaustion or Lean claim.

The first packaging pass rejected a compiled checker snapshot; its source and full failure diagnostics are retained. The final packager omits that binary with exact size/hash, retains its pin/source provenance, and passes the no-binary scan. The intermediate archive2 snapshot lacks the later independent real-control replay; use archive2-final for delivery. `archive2-final-handoff.json` SHA256 `adb6a85c3c83fa6b1b5cb58c544b91f717ed755f9c2a73dd81b9649f966b4b25` binds tar, build/validation records, complete outer logs and read-only validation source. Packaging/reconstruction launched no worker and changed no active file. Main/S08 may review/copy/push this concrete package.


## 2026-11-24T04:16:55.691982+00:00 — unchanged four AAOA offline commands ready

`orch/S06/AAOA-offline-plan/commands-manifest.json` SHA256 `adabaea68e23813da23a98eeba453040930adddc570e02ff4bb1eedbe1df4175` binds exact argv arrays for T1..T4, fresh output directories, the unchanged aa5d13... runner, S04 mathematics and exact-delta reviews, S08 runner review and real compatibility review. Four real-input/tool-hash preflights passed without launching any solver/checker/validator or creating case output directories. Parent bodies, clause deltas, metadata and review hashes match; no cut or input changed.

| Case | Clauses | CNF SHA256 | Metadata SHA256 |
|---|---:|---|---|
| T1 | 115450 | `422b20c5d9fd5c7eff0ec8a4d7283c70750686da38e3bc3e1dc68e7a1dd5353c` | `8925809ed282165430b24ff29d0dfe855a8a201caee9f4f89d644460b1644b43` |
| T2 | 115884 | `a295babc305737a921da6bb5c0e990f6c91b2a4c200544d57bcd3abc3e574c3b` | `32645cb4ecbf1930eac6a4d472de4c3894e72c68ee73c29193030ec06a5ca91a` |
| T3 | 115448 | `0ab8fcacbcfe9fa8e094d8db4d0a52eb5d885a032313992ac7c02f312eaffbdf` | `e52df0ccce39250ad98e3d9053d0585ae1cdcab85a330db75e7596de6f4a058a` |
| T4 | 115884 | `661f44876da7e7f8d24d9a06f64ae3708037fc19048e9e20153c47e6a49ea5e3` | `b5471b3ac9514a8b02dd6090d8329c6eddbfd012914875dcd47e973d06c5e9b7` |

Per case: solver600s/1536MiB AS, checker600s/3072MiB AS after completed UNSAT, SAT validator30s/1536MiB AS,512MiB proof cap and default1GiB free-space floor. One active child per controller; retain its slot until the entire checker/validator pipeline completes. Proposed T1/T2 allocation waits for BOTH AAAA online children to exit; T3/T4 wait for completed P/d pipelines, subject to main candidate-pin priorities. No timers or launch controller were installed. Four forms still require the separate AAAA fallback for existence coverage. All full preflight outputs, exact metadata/deltas and review snapshots are in AAOA-offline-plan; outer source/results/logs are bound by `AAOA-offline-handoff.json` SHA256 `660a4f994c06f38d68638f19ed077252c8c12de6ada2faee4aba3874661b2db3`. Frozen archive2-final is unchanged and remains the priority review package.


2026-11-24T04:19:27.220628+00:00 — Archive2 independent delivery review now PASS `c7af9386a329d8af7c4049167ff5b0b7a087f417e939d772c1ec9d55e279d329`. Initial failure was S08 harness requiring a local __pycache__ file absent by design from payload, manifest and source map. S08 corrected that expectation in v2 and preserved the historical failure. Tar de4ba452... unchanged; all95 recipes and full evidence pass. Resolution record: `orch/S06/archive2-review-resolution.json`. No repackaging or worker action.


## 2026-11-24T04:23:15.457679+00:00 — bounded AAOA static consequences and exact partitions

Both sequential static passes completed in5.253514seconds aggregate, below the10second budget. No SAT solver ran. Child jobs ran sequentially at lowered priority,768MiBAS/2CPU-second caps; all full probe/checker outputs and statistics are retained. Parent CNFs/metadata were hashed before and after; no active or source input changed.

The exact-parent DSR --forward --rup-only checks all exit0/s VALID. Added245rootunits across templates, five absorption exclusions, sorted-port implications, coverage clauses and conditional units. Per-template full proofs include the prior3692 original-RUP clauses:

| Case | New root units | Full proof clauses | Remaining partition cases | Proof SHA256 |
|---|---:|---:|---:|---|
| T1 | 40 | 3872 | 3 | `c7e73b1cfad4d4df10e323ff3b9637c37f0f691cba0d79dd0d666ec82869f021` |
| T2 | 86 | 3960 | 3 | `b5a7267a68a289cf1f48c3a74fbad32a39efaebd0eb3f1c07a97fd9dad7f34b6` |
| T3 | 55 | 3867 | 3 | `0287d3e61224d2af864307c9df2b94beb2574f01685d49f68075b0e1e1264cca` |
| T4 | 64 | 3873 | 2 | `4c926bf0ad8f9367f3a719caf98715332373f493ca625a9e0e0d272f97a50c25` |

The five checked absorption clauses are T1 `[-3644,-3102]`; T2 `[-3644,-2867]` and `[-3644,-3133]`; T3 `[-3371,-2867]`; T4 `[-3102,-3403]`. Direct root propagation initially found no conflict; the bounded failed-literal pass derived the local unit conflicts and lifted each clause. These are now replay-checked implications, not unverified algebraic cuts. No whole remaining case was refuted.

Exact disjoint partitions (all selectors refer to wire29):

- T1: `[3644,-3102]`, `[-3644,3371]`, `[-3644,-3371,3102]`.
- T2: `[3644,-2867,-3133]`, `[-3644,2867]`, `[-3644,-2867,3133]`.
- T3: `[3371,-2867]`, `[-3371,2867]`, `[-3371,-2867,3133]`.
- T4: `[3102,-3403]`, `[-3102,3403]`.

T4 is an exact XOR between factorc (left18wire29) and OROperande (right19wire29). Coverage follows liveness and sorted ports; absorption forbids both. Exhaustive Boolean checks over the2/3representative selectors confirm each partition covers exactly the replay-checked coverage/absorption formula and is disjoint. No root-probe fixed-point claim is used.

Handoff `orch/S06/AAOA-static-handoff.json` SHA256 `9fbf54e91191c177abfb18d526973dd8f468f84952ae5e71a0eb378677160be6` inventories226 complete artifacts plus exact parent/source/proof/metadata bindings. Final result `AAOA-static-v2/result.json` SHA256 `2e9e964342c09add959bb3cd225e89b9e0b45f03ba222384568f7cae49c7aaa2`. Review T4 first as the smallest future split. Keep active T1/T2 inputs and prior pending command manifest unchanged; main chooses any later use after independent review. Archive2 remains unchanged and independentlyPASS.


## 2026-11-24T04:31:49.407189+00:00 — reusable +1 ancestor-cost encoding ready for actual-delta review

Ready for independent actual-delta review; no solver/checker/Lean or active-input mutation. Generator SHA256 `56da4e9f313a18cabbcb582dffd999b212f8858e110c43c9f5dd7fb2c778b27d`. All ten fresh inputs append the identical3553-clause delta SHA256 `2c69ea99739a06d291dbbc9ee3a26d1f4411f25645bc07a04805bb860ee279dc`. Old variables1..11968 and all old clause bytes are unchanged. New penalty bits11969..11985 are the only additional variables.

For prefix gate g, let A count strict gate ancestors and M=A+1. The old signed counter counts T=|S|+|H|+selected_cover+g-A. Its old proper-support bound T<=g+2 is the ancestor lower bound M>=|S|+|H|+selected_cover-1. The proposed extra charge requires T+p<=g+2. When p=true this is T<=g+1, so threshold T>=g+2 must be forbidden. The source-pinned exact reverse totalizer stores this threshold as overflow_flag-1. Every one of17 complete counter clause blocks, adjacent full-support guards and root allocations is regenerated and checked byte-for-byte in each actual parent before use. No counter is rebuilt in the child and no existing index changes.

There are3366 trigger implications: for each root g, reader h<=g, rawinput v, and left/right operand, p OR S[v] OR any missing neighbor OR not ancestor(g,h) OR not selected(h,v). For h=g the ancestor condition is omitted. Raw inputs occupy existing selector positions0..10; free constants11/12 are excluded. The trigger uses actual syntactic ancestry, not singleton support as reachability. One bit charges at most once even if multiple irrelevant inputs trigger it.

The remaining187 clauses are `[-p_g,-threshold_g,S_g[v]]`, one for each of11 support bits/output. For any proper support, at least one is `[-p_g,-threshold_g]`; for full support every clause is true. S04's compact alternative uses17 unguarded links and3383 total clauses. Both variants are sound under existential penalty choice; ours intentionally leaves full support exempt for either penalty value, adding170 clauses. S08's prep review explicitly accepts this guarded treatment. No change is needed merely to save those clauses.

S04 mathematics/trigger/counter-spec review is PASS `73ae23f8a5df0ba581d85ffbbd0572424e522dd8672d8c2dc348a15f2c8b5bf6`, for math951fd... including arbitrary accepted residual H, empty H, empty/full support, constants and productive clean-prefix assumptions. S08 counter-spec/boundary prep PASS is `d3684badea28b22aeff35bf353a8fdf72a4400bf56e956db6dd89d121b569d14`. These are not yet an independent review of the final generated child deltas. Historical generated metadata says review pending; this handoff updates the mathematical/spec status while keeping all tested bytes frozen.

This is a mathematical restriction with auxiliary existential choices, not an RUP proof that every old CNF model implies the new clauses. In particular an old model can have an unnecessarily large selected cover; completeness chooses a minimum cover afresh and canonical exact thresholds. Do not claim preservation of every old auxiliary assignment. Circuit-level existential completeness is the reviewed mathematical claim. Full support can choose p=false even in the compact unguarded formulation.

The first seven fresh parents are original, AAAA-chain, AAAO-chain and T1..T4 under irrelevant-charge-v1/. Controls passed in0.919793seconds:180224 trigger rows,8704 syntactic input-path checks,1538 small signed-counter assignments/77468 clause evaluations,85 actual-counter boundary assignments/106225 clause evaluations,3196 bound arithmetic checks,3366 independent trigger-shape checks, five negative-control groups, and seven exact parent-delta/metadata checks. Full stdout/stderr and execution caps/exit0 are retained. The test driver never invokes a SAT solver, checker or generator main process; generation is a Python API call.

Three additional fresh parents under irrelevant-charge-AAAO-v1/ are the reviewed3895-RUP-augmented AAAO parent and its P/d partition children. Preparation took0.305558seconds; each has exactly the same3553-clause suffix, unchanged old metadata except count/hash fields, and unchanged parent bytes. Their parent hashes are checked against S08 AAAO review5ce151...; all old RUP literals remain<=11968. Old RUP implications remain valid after adding clauses by monotonicity; no new replay was needed or performed. These three deltas also await independent actual-delta review before launch.

Reproduction uses the frozen generator CLI with a parent path, a fresh output directory beneath S06scratch, and exact --parent-sha256/--metadata-sha256 from the handoff/generation record. It writes instance.cnf, instance.json, delta.clauses, thresholds.json and generation.json. Original and normalized input paths remain untouched. The generic interface supports the three RUP parents without special handling because their original counter blocks and variable IDs are intact.

All full control logs, exact family/metadata/threshold bindings, sources and copied mathematical/spec review evidence are inventoried in irrelevant-charge-handoff.json. Main/S08 should review the actual3553-clause shared delta and all10 fresh parent suffixes. No resource admission or production launch is authorized by this package.

Handoff SHA256 `9b9adf9f84a8e1321f55d936b5c9d091ee80edf0347750d0aefda7020b9084f2`; all71 source/control/provenance/input artifacts are bound.


## 2026-11-24T04:40:14.594221+00:00 — reviewed charge archive and four completed AAOA runs

Final S08 actual-delta review PASS `b0af769b67da5f0b2f42aa1d4e341e217556b56cf17ea3a7a7aa5ffe9a0a2d7b` covers all10 frozen strengthened inputs, parent bodies/old indices and prior AAAO RUP compatibility. Main independently rechecked107bindings and launched two strengthened runs; those running directories were not read or modified by S06. Pinned validator metadata-parser/decoder-shape checks pass for all10 inputs, recorded in charge-metadata-compatibility.json; this is structural compatibility, not a SAT model validation.

Archive `orch/S06/charge-archive-v1.tar.gz` is3,753,740bytes, SHA256 `aeb918872f1a57b4ab4e3fb9afd48176dfe5022718b639063a4fd3f40d1ed0fd`; internalmanifest SHA256 `149bcc57286b9f3af38f505c5deb407727ea303ef98534f670e6027e7c7f23ac`. It retains693boundpayloads/694regularmembers including all10cuts source/delta/metadata/thresholds, full controls and S04/S08 reviews/sources/fulloutputs. Portable standard-library reconstruction passed for55 exact CNFs, including11968/11985variable headers, with no rawbulkCNFs or compiledbinarypayloads. All tarfile/hash bindings passed. Original generator dependencies and normalized-parent provenance are included.

All four completed AAOA T1..T4 runs are UNKNOWN/solverwalllimit, exit2, with full result/progress/inputmetadata/solverstdoutstderr/outerstdoutstderr and launch records. No checker phase ran. Four incomplete DRAT streams remain in scratch, omitted from archive with independently recomputed sizes/hashes totaling1,278,861,312bytes; none is an accepted certificate. No exhaustion claim follows.

First packaging attempt rejected a historical checker executable snapshot; its full source/diagnostics are retained. Final package omits it with exact size/hash. Cached bytecode is excluded from payload and selection expectations. No reviewed producer source or input was edited. Final build/restore/log records are bound by `charge-archive-v1-handoff.json` SHA256 `29be436c4c78c47632e987d0df17f5b25357e00f407067f2933817c6bfae4677`. Package is ready for main/S08 independent delivery review and preservation; no solver/checker/Lean/git/desk activity by S06.


## 2026-11-24T04:48:01.088634+00:00 — +2/+3 hitting-charge children ready for actual review

S04 mathematical/finite review PASS `e4df03fa7c9077847bf16e2850b67b0a0331b79559dd0ca718829c3cb8b50609` supersedes the planning-only status. On main's implementation instruction, prepared10 fresh children of the independently reviewed +1 inputs, prioritizing AAAO-RUP and T1..T4. No old source/input or running directory was changed. No running directory was read; no solver, checker or Lean was launched.

Generator `orch/S06/add_hitting_input_charge.py` SHA256 `58bc217a57c3bb8a7819925e17f86b4c13435e006b9f3028731e4d1e10533398`; control source `93f2feed9d2f3effbcc1bda0f08ac0305833acaf2e684f4588dcf26b1998c4f7`. Every child appends221 variables11986..12206 and4233 clauses:3366 actual-raw-ancestor witness implications,408 rank2 pattern implications,85 rank3 pattern implications and374 full-support guarded threshold clauses. Shared delta SHA256 `3f5cc4b71971641479dfb1e6c418fd7dfbd26c375421f0047e732cf2a5eb6a5d`. All old variable meanings/metadata fields and clause bytes are preserved, including +1 and any old RUP additions.

For rank k, T<=g+2-k forbids the old totalizer root threshold g+3-k. The literal is old_overflow-k except gate0/rank3, which explicitly emits11 clauses (-p3 OR support[v]) and has no threshold literal. Both +2/+3 retain the same full-support exemption as +1. Ranks constrain separate absolute bounds; they are never added. The generator pins S04 mathematics/coverage, the prior S08 parent review and old source, and reconstructs the old counter blocks/+1 suffix before appending. All ten CNF/metadata pairs must match the prior actual review.

Bounded controls exited0 in1.920338s under10CPU/30wall seconds and1GiBAS. Passed4233 independent clause-shape comparisons,8192 actual rank-clause truth checks,113 signed-counter boundary models/146039 counter-clause evaluations,38352 guard truth checks,34 wrong-threshold negative checks, the summed-rank negative control and7 rejection controls. All10 fresh-child body/hash/metadata checks passed the pinned validator parser and decoder-shape checks. These parser checks are not full SAT validation.

Actual implementation review remains pending; minimum-cover/counter reselection is existential, with no every-old-auxiliary-assignment extension or RUP claim for the new math restriction. Parent +1/RUP compatibility review is retained and new restrictions preserve parent clause bytes. Main owns review admission and any launch.

Handoff `orch/S06/hitting-charge-handoff.json` SHA256 `88556b6479b8b1ab2676ba63d376df475eab7d6401692af7516a30fe59391351` binds89 artifacts,20 frozen math/source/review snapshots, all full controls/logs and10 portable CNF recipes. Each recipe replaces the parent's header and appends the shared ASCII delta; the frozen charge archive supplies exact +1 parent recipes. No large CNF needs repository storage. See hitting-charge-v1-README.md for source/dependency pins, boundary details and reproduction interface.

Priority input hashes:

- AAAO-RUP: `d47a48153e4b268587b8c3330c2e57d1756c554848f4cdfe50c2337cb0be5ec2`; metadata `0508fb3946c969a243ec5160ad9caed77839360a1c2f87ca63aa4cad398832ca`.
- T1: `d3c29af1b433b79402dc57029a6ccc57b2f501760f4dbb8ac0e419dcb825a0f6`; metadata `c66909b3acf118ba604d0221bc2625afb67e4181d8c2f6ef583545ed3010a6ed`.
- T2: `4f87858e5c68842218222a7afbebc292cc7dc1a797477701bfbb3586d8ae78b3`; metadata `3cbde9b1599a21a55cc31dda07fc4307213d8a155b8060a2cbe13952c5bc100b`.
- T3: `056b756b54c21093cbbedb4f64694593987e502ce4d7e14594266c605a0521dc`; metadata `54f5aeaf0fc83bd3ba00f40cf25481848a4d21710e61321450fb02ff917ed4b5`.
- T4: `d3a169889af5938186c02e44453679abf8f856aa3d0f57b927deb6b0e5e56fbe`; metadata `163bee95f8eb66773e987cb0b990d60a87fe0a76348e4d8c05fc6acdcdc07b10`.


## 2026-11-24T04:53:16.235194+00:00 — hitting command manifest and compact preservation complete

Four commands are ready, ordered AAAO-RUP,T2,T3,T4, in `hitting-offline-plan/commands-manifest.json`, SHA256 `948ac6c2a8d186f1bfdc1b2e8473bb41df28bf6922a6e291bdf005a618454a06`. All input/metadata/tool/runner pins were independently read and checked; no runner preflight or production command was executed. The unchanged retained-proof runner is `aa5d13bb83ab79e47b9794809c3c06dc153544975cd1131afbdeaef7c18d484a`; each proposed case uses600s solver plus600s checker,512MiB proof cap,1536MiB solver/3072MiB checkerAS. Hold each slot through checking/validation/finalization; stop further admissions on any SAT indication. Fresh output names are offline-hitting-CASE-wave1. Free disk at preparation was9,748,189,184bytes; no reservation is made.

S08 actual-code/delta review nowPASS `0ed0ac84baea1a88bf665fea4e6b78aff41b41c3993f1044d84f3665537a417d` covers all10children and controls. Historical pending-review metadata/command fields remain unchanged; this final review supersedes them. Main owns resource admission and any launches.

Compact archive `hitting-archive-v1.tar.gz` is2,471,021bytes, SHA256 `1b35774d63977b6e9f6660d2e011ab47316c690d1f0ff61585b85141b27af0ec`; manifest `b13a156feccad31add4704016d8f6f93e415545b0f83c5ee162746ca6736280a`. It contains264boundpayloads/265regularmembers and30portableCNFrecipes: ten +1parents, tennewchildren and tenindependentreview snapshots. Allpayload/tarhashes and allrecipe reconstructions passed using the unchanged standard-library restorer. Full S04disjoint/hitting math preservation, S08actualcode/review/snapshots/fulloutputs, allnewproducercontrols/source/logs/metadata, pinnedrunner+fourcommands, and originalgenerator dependencies are retained. There are no raw CNFs, compiled payloads or runtime outputs. No active output directory was read. Previouschargearchiveaeb918... remainsunchanged as older normalization/RUP/runner-control provenance.

Package generation exited0 in3.026088s under10CPU/30wall/1GiB caps. Fullbuild/restore stdout/stderr, execution and package records are external delivery artifacts to avoid self-referential manifests. Handoff `hitting-archive-v1-handoff.json` SHA256 `d6d8e539b18ed7368c54052f35785300f7e481399d040281e4f9ee4d9a0584ec` binds all8 delivery files. Main/S08 independent delivery review and preservation are the remaining step; no solver/checker/Lean/production/git/desk action by S06.


## 2026-11-24T05:11:55.016687+00:00 — one stable-mode route independently audited

Recommend exactly one 600-second retained-proof run of the unchanged, reviewed hitting AAAO-RUP CNF using S05's CaDiCaL --sat preset runner. This enables stable-only search and the default random-walk machinery; it also lowers elimination/subsumption effort. Keep the same pinned solver, exact CNF, DRAT checker and full SAT validator. Allow the checker its separate600-second cap only after a complete solver UNSAT; keep one CPU slot through checker/validator/finalization. Main/S08 review and main admission remain required. Do not repeat all four cases before assessing this one result.

The completed three runs all explicitly selected --stabilize=false and --walk=false through --unsat. Independent full-log parsing agrees with S05's counts:

| Case | Conflicts | Restarts | Conflicts/restart | Unstable CPU | Peak RSS MiB | Retained partial proof MiB |
|---|---:|---:|---:|---:|---:|---:|
| AAAO-RUP | 2912372 | 274314 | 10.62 | 95.87% | 112.79 | 316.40 |
| T2 | 2908346 | 251139 | 11.58 | 95.13% | 112.91 | 308.01 |
| T3 | 2831325 | 253115 | 11.19 | 95.09% | 113.36 | 324.31 |

Each completed run was UNKNOWN at its wall limit, with only the solver phase present. Peak RSS is about7.4% of the1536MiB address-space cap; incomplete DRAT occupies60–64% of the512MiB file cap. Thus more memory or a larger proof cap does not address the observed termination. The statistics establish an untried mode, not that short restarts caused the difficulty or that stable mode will finish. New CEGAR/decomposition would require additional projection/coverage and proof integration; the one preset experiment fits the remaining deadline with an already checked acceptance path.

The supplied runner is byte-exactly the reviewed S06 runner after three unique replacements: OWN S06→S05, --unsat→--sat, and the output-ownership error label. No lifecycle, abort, pin, memory, proof, checker, SAT validation or acceptance logic changes. Independent audit rehashed all50 S05 handoff artifacts and verified the supplied toy solver20/checker0 result, exactlyfour full log keys/byte counts/hashes, input/proof/tool pins, and the intended preset options. The toy was not rerun and does not predict performance on the real CNF. Large incomplete proof files were not rehashed or replayed here; their recorded sizes are used only for performance analysis and remain unaccepted.

Use the exact command already in S05's solver-mode-review/recommendation.json, bound by its stable-mode-handoff.json SHA c2a1358bb7f0c1090fb1e36ad6d1916c8525a4148228e9c2a5369c9ee84c1015. Runner SHA64958a6d0ef8eaa1e072547ade244cdb2de156815fca6545b4fcf829d331f7da; CNF d47a48153e4b268587b8c3330c2e57d1756c554848f4cdfe50c2337cb0be5ec2; metadata0508fb3946c969a243ec5160ad9caed77839360a1c2f87ca63aa4cad398832ca. Fresh output/admission is main's responsibility; this audit did not inspect any proposed/active output directory.

S06 independent review stable-route-review/review.json SHA b75936e6798fc79508b451888bd612c1d21b9f89ae863f468740723fbbf9bbf4, source review_stable_route.py SHA bf7686c2036049fcd526ea5418b66920a7a9f397d520e5668327d28bf040e849. Full source, frozen evidence copies and stdout/stderr/execution records are retained. The audit exited0 in0.115471s; no solver/checker/Lean, production, or active-directory read/mutation.

S06 durable handoff stable-route-handoff.json SHA `9203f9e9819d44df01121e5f44404d67394a7453e6e176522cd00a193c1a10d9` binds all6 own result/source/full-log/recommendation files and the unexecuted command. The existing S05 implementation is reused; no duplicate runner/portfolio was created.


## 2026-11-24T05:15:52.027720+00:00 — stable route frozen preservation complete

Archive `stable-route-archive-v1.tar.gz`, SHA256 `cd26624aad04e41af18bd4480ea3e031a21c44644486b7a28f21d3384230e1c2`, is297495bytes/141regularmembers/140payloads. Manifest `000362199926cc613ec98ef60d1820980cebeda84f7ea67a775ca7e11dccaafd` binds exact S05stable runner/source/diff/full50-artifact handoff, alltoycontrol logs/eight-byte proof and historicalfailedcontrol, independentS06audit/fullfrozencopies/logs and originalgenerator dependencies. OneportableCNFrecipe reconstructs exact reviewedhittingAAAO-RUP. Allpayload/tarhashes and standard-library reconstruction passed; packageexecution0/0.470315s. Handoff `stable-route-archive-v1-handoff.json` SHA `dc50a32bad234162af0b0156f941f114dd4907c811ce1695e36047e1570ee182` binds8externaldeliveryfiles includingfullbuild/restorelogs. Noactive stable/T4output was read or copied; inputs/runner unchanged. Main separately preserves launchmanifest andfinalruntime. No newsolver/checker/Lean/productionrun byS06.


## 2026-11-24T05:25:58.233158+00:00 — generic 8-input/12-gate construction package ready

Main's new gadget target is prepared in `orch/S06/gadget8-v1/`. Generic12 has996 variables,14093 clauses,189611bytes; CNF `dae54c6f20435a53be3a34b09da9310e85df61823b382caa2837817a441b8bfb`, metadata `20ca64f5caae894c1b144c8f4de2ab5e7905ce0044447c326272d3c218f5022d`. It encodes ten positive edge rows and seven maximal negative rows. A256-entry completeness map verifies every positive contains an edge and every negative is contained in an encoded negative; monotonicity makes these17rows exact for every AND/OR circuit. The two generic instances allow free FALSE/TRUE and repeated ports, with only commutative operand ordering and output-last/copy padding. No shard/first-junk, cleanliness, liveness, template or distance condition is imposed.

Generator `build_gadget8.py` SHA `3ca5274e1a394aff25e8f633bfc07ca5dd9ed2163b43db321dfba218e6b1ac17`; independent decoder/validator `validate_gadget8.py` SHA `60e877fd3bdb11d134633519482b67ca82478c55a00350e34a935ddd194054cb`. The validator requires pinned CNF/metadata and soleSAT plus a complete consistent model, checks all clauses and intermediate encoded-row assignments, and evaluates all256 gadget inputs. It builds the explicit full11 extension and checks all2048 inputs. Acceptance flags separately require<=12gadget gates and<=21full gates; the positive13 control is exact but NOT a21gate witness.

The clean13 positive fixture consists of stars9(0+5+8),8(4+5),2*5,10(0+2+4+6), with three OR unions. AllfourANDs are productive/ambient-clean on256rows. Its full1092-variable model satisfies every clause and passes independent API+CLI validation; extension22gates exact on2048, both requestedlimitflags false. The bad12 fixture is exactly gadgetTarget ORx0*x2*x4; its explicit21gate extension has only falsepositives[21,29,85,149]. Fully pinned bad12 is BCPcontradictory with984derivedunits; independent DSR --forward --rup-only replay of proof `b3396378431d05464519a893cc3d70f58b2ccfeb97b0244d7b108a651a2724c6` returned0/soleVERIFIED_UNSAT in0.00932s. This result applies ONLYto the pinned bad12, never generic12/global/shard.

Full scalarcontrols exited0 in1.170058s: all16Boolean gate-relation assignments,64randomunrestrictedcircuits/allstructuralclauses/full256 agreement, all256rowcoveragewitnesses and6negativevalidatorcontrols. Positive/negative validator CLI exits0/2, fullstdoutstderr/results retained. No production SAT solver was run. Generic12 verdict remainsUNSOLVED.

The extension uses8gates for7*(3+6+9) OR3*6 OR1*(4+8), coveringmissing14,18,36,37,67,79, and onefinalOR. Avalid12gadget therefore yields full21. Generic12UNSAT would onlyexclude this construction decomposition, notany21circuit or assignedshard.

Handoff `gadget8-handoff.json` SHA `680c4d01926307c859940f8b1ac2f1247b74d878302ff8a2c0e04cd5d26889ed` binds36artifacts/fullsources/logs/proof/models/fourinstances/metadata. `gadget8-search-plan.json` SHA `652591c4dc2e571d8b6454b5fd18fd4d177e95bd38e0872d466a905f99ed1e6f` gives unexecuted pinned solver/validator commands and requested main supervision/caps. Existingretainedrunner's11inputvalidator is incompatible; main must use/adapt to the supplied gadgetvalidator and requirebothgate-limitflags. Main/S08review precedes production. Allpriorrunners/inputs unchanged.

Separately completed before this priorityshift: support-input-and-charge.md SHA637e7feb65840de8d401efe987f332bea884cb714c0a8ece07f28cc5d93945c5 proposes p1 whenanactualancestralANDdirectlyreadsrawv inroot supportS. RestrictingSzero deletes thatAND inadditionto originalORcharges. Proposed2992five-literal implications,zeroextra variables; doNOTstacknumericallyonexistinghittingcharges.64smallcleanDAGcontrols/nooldneighborhoodtrigger pass2048rows each (source6ac430...ed31,elapsed0.065s); NOindependentmathPASS/CNF/redundancy/performanceclaim. Deferredbehindgadgettask.


## 2026-11-24T05:30:54.620971+00:00 — gadget8 runner independent review PASS

S06 PASS_GADGET8_RUNNER_ADAPTATION: actual MAIN runner SHA5c196750473896225cb414458a150bccfc5dff3d68ecbeceec2aaf1c7f088b34; exact7 unique literal replacements fromaa5d13...84a independently reconstructed byte-exact; source.diff/derivation/pinnedvalidator60e877...54cb allagree. Full retained-proof/DSR/lifecycle/hash/abort/caps unchanged. orch/S06/gadget8-runner-controls/review.json SHAb7f773d1c2e2bc5a651a562875989d1027f37b1c6b744b676da12f10a6870744; handoff gadget8-runner-review-handoff.json SHA4b24936c148500cfd88d2d43a0232b4ad22c383d78844d88959f22a284fd5b89 binds172full artifacts. Real pinnedbad12 runner0 VERIFIED_UNSAT,solver20/soleUNSAT thenchecker0/soleVERIFIED_UNSAT, retainedDRAT 4198bytes SHAd30c629d500b1e3d6b3b907f7078ff00716e2dce9946d749c15fde52ce1284f5; appliesONLYpinnedfixture. Real positive13 solver10/validator0/full256+full2048/13->22gates; runner2UNKNOWN exactoverlimit rejection,bothflagsfalse. 15syntheticfailclosed controls allrejected includingrealpinnedvalidator incomplete-model, wrong/missingcounts/limits,integer1booleans,allfourwrongprovenances/missing/extra andvalidatornonzero. Eachrealcase15souter cap/5ssolver+checker,entireaudit0.723s; exact4logkeys+bytes/hash/progress/snapshot checksPASS. No generic12 orproductionrun; input/runnerunchanged. Mainencodingreview+resourceadmission separate; readyforhandoff.

The synthetic decision-path records are explicitly labeled and reject in every case; only the two pinned fixtures run the real solver. The incomplete-model control runs the actual pinned validator. No generic12 UNSAT, full21 candidate, or Lean acceptance is claimed. Fresh control trees and source snapshots are immutable for main preservation.


## 2026-11-24T05:34:39.035305+00:00 — compact gadget8 preservation delivered

Archive `orch/S06/gadget8-preservation-v1.tar.gz` SHA `a261356299baa8fc7f987a4fb89d96c03e742c0ea7f4fd30ee573768bb9f1b2b` is163023bytes,198regularmembers/197payloads. Handoff `gadget8-preservation-handoff.json` SHA `9c1aeafad3facf190b6fda2fc7b9eb326c3c43768c9e994df1fbba30c0772a15` binds15deliveryfiles. It preserves all frozen generator/validator/control sources, four portable CNF recipes, full fixture proofs/logs, main encoder review, actual gadget runner plus parent/diff/derivation and S06 independent review. Raw CNFs are omitted and reconstructed by the byte-identical generator APIs; the standalone standard-library restore verifies allmetadata and all208historicalhandoffbindings. Fresh delivery verification additionally checks216originalsource mappings, allpayloads,4unique recipes/21CNF aliases and both proof hashes. Deliveryreview SHA `3b754569dfe2f06c8680abfc6b2ce9fa3f5767d9e18f9bfdea9b902a43ff1072`. Build0.320s, freshverification0.365s, no solver/checker run.

Active generic12 production/launch/runtime was excluded and unread; originalsource/inputs/runner remain unchanged. Historical scope statements remain verbatim with timestamp clarification in archiveREADME. Only pinnedbad12 has checked UNSAT certificates; positive13 is exact22and rejected, synthetic controls allreject. No generic12/global/Lean verdict is asserted. Main owns final runtime preservation and publication. Awaiting newfindings; no additionalsearch planned.


## 2026-11-24T05:39:55.850515+00:00 — SAT-only Kissat gadget wrapper ready

S06 SAT_ONLY_KISSAT_FINAL_HANDOFF READY_MAIN/S05: orch/S06/sat-only-gadget-handoff.json SHA2a00340c4181f01e3c9a705cfe1871b33639ef208402dcbcf72016b02f578567 binds72sources/fullcontrols/reviews/inputpins. Runnerfd05c03210c7d815ec81f0f3a292ef5d7eeb92f4380c8f4c5fde18d10aaa6bcd FROZEN; commands sat-only-gadget-commands.json SHAa8e237e872f0430f7f6ae094bdafb9b04a5e80a4b1293cebefd6bb9583562e9c twoUNEXECUTEDfresh600s casesgeneric8/12and7/11,1536MiB,64MiBperlog,1CPUeach,defaultabort. BothrealbadfixturesKissat20/soleUNSAT=>runner2UNKNOWN reasonUNCERTIFIED_UNSAT_NO_PROOF, no proof/checker. BothrealpositivefixturesKissat10/validator0/full256or128+full2048=>runner2overlimit22gates. Wronghash/abort pre-solver failclosed;24schema/provenance/boolean/countrejectionsPASS. Fullcontrols0.867s, exactlogsets/hash/progress checked, controlsSHA7123c4f2c68436553c3f80aac7d98fbd625821dae454b0100e3e3a23995acb33. PinnedKissat21da5d...93a1; parentlifecycleaa5dunchanged; mainencoderreviews bothincluded. Main+S05 independentreviewneededbeforelaunch; noS06genericproduction. Archive8a261...1b2b staysunchanged; completedold8runtime preservationnext.


## 2026-11-24T05:41:22.638907+00:00 — completed generic8 runtime preservation

S06 GADGET8_COMPLETED_RUNTIME_PACKAGE READY_MAIN/S08: orch/S06/gadget8-completed-preservation-v1.tar.gz SHA9ea054d743bb224e6d4b1044a224a40974b0ad0f1196953982413394964d0fda,175553bytes/28regularmembers/27payloads. Handoff gadget8-completed-preservation-handoff.json SHAa231de4ffe96260ae9792863e155652969128610845dbe7f8b5953b214c58cf3 binds7full deliveryfiles. EmbedsUNCHANGED originalpreparationarchivea261...1b2b plusall15externaldeliveryfiles+handoff. Includescompletedoldrun result/progress/metadata/fullsolverstdoutstderr/fullsupervisorstdoutstderr/launch. Runtime74.366824s,file_size_limit/SIGXFSZ,solver_verdictsEMPTY,statusUNKNOWN,noSAT/UNSAT/checker/certificate. Omittedproof268435456bytes independentlystreamhashed d88e7c5f643b95d14152199f18e3b45a59f16b27b8565a0d6e5a0eb77f139131; clearlyincomplete/unaccepted,originalscratchretained. OmittedCNFexactrecipeboundtooriginalfour-CNFrestoration. All25sourcecopies/loghashes/tarroundtrip PASS0.265s. Noactive/newSAT-onlyruntimeread; original8archive/sat-onlyrunner/inputsfrozen. SAT-onlyhandoff2a0034...8567 alreadyready05:39:55; pendingmain/S05review.
