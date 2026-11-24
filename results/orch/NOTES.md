# L-meta-1024 orchestration notes

Updated 2026-11-24 03:23 UTC. Owner: root. Branch: pnp/pilot-21.

## Read before starting

Read this file and `lemmas/README.md` before each new assignment. Append findings here with UTC timestamps and your agent name. Use an exclusive file lock for concurrent append operations; do not overwrite another agent's notes. Record only verified results as checked. Keep counterexamples to auxiliary conjectures distinct from counterexamples to the posted statement.

Only root controls the single L-meta-1024 lease and publication. Do not acquire, release, or submit any gap. The existing exclusive-lock renewal timer is root's automation; request a renewal from root before a long build or search. Never record authentication material.

## Goal and current status

Prove the exact posted theorem in `lean/PEqualNP/Outside/L_meta_1024.lean`: a fan-in-at-most-two monotone circuit producing the thirteen projective-line ORs on inputs with five or six false coordinates needs at least 39 gates. The line at w is `{0,1,3,9}+w` modulo 13. There are 3,003 required input rows.

The 4,455-line integrated module builds and is pushed at `4f2bed9`. It contains partial results, not the exact named theorem. The local checker previously rejected it with `REJECTED (no-theorem)`; the fresh retry faulted without a verdict after an OOM kill (verifier exit137). No proof PR exists. No valid counterexample to the posted statement has been found.

## Checked results

- Arbitrary band-correct circuits require at least 13 gates.
- OR-only circuits, globally correct circuits, and circuits with at most one AND gate require 39 gates.
- Any globally nonordinary output has at least eight essential raw inputs. Ordinary means globally equal to its line OR, beyond the required band.
- The 39-gate bound holds when at most three outputs are nonordinary. Thus a sub-39-gate counterexample must have at least four nonordinary outputs.
- Nonordinary outputs have finite witnesses among line complements and line singletons. These witnesses support independently reviewed SAT constraints.
- Paid-gate charging, cut semantics, component/source counting, Clamp and Clamp9, and prefix lemmas are available in the main module.
- `Sink.lean` compiles and has independent approval. It replaces valid earlier output references by true, preserving length, permitted gate operations, fan-in, band correctness, and ordinary outputs. It does not erase invalid future references syntactically. This source is preserved in the lemmas folder.

## Active strategies and ownership

1. **formal_baseline — compiler and decomposition.** Connect Sink transformation to cut semantics, delete paid gates with correct index remapping, and formalize the four-exotic reduction. Preserve invalid/forward reads as false.
2. **fresh_proof — high-gate structural proof.** Formalize the reduced four-output, eleven-gate contradiction: four OR sink outputs, seven internal gates, each output with at least eight essential raw inputs. Three low partners force three triples requiring six gates among the first five internal gates.
3. **lower_bound — independent mathematics and extension.** Review the four-output proof and seek a route for five or more nonordinary outputs. Four-output success alone does not prove the posted statement.
4. **counterexample_search — finite search.** Five detached 90-minute SAT searches restarted after the external interruption: three low-fanout cases, the full 3,003-row problem, and a normalized dual problem. Preserve complete logs and proof streams. Only a fully checked assignment is a counterexample; interrupted/UNKNOWN runs prove nothing.
5. **special_status — independent red-team review.** Review every proposed push, semantic normalization, solver restriction, and exact theorem claim. Sink currently approved. Review orchestration records before their first push.
6. **lease_timer, reassigned — build performance and resilience.** Root now owns renewal control. Inspect build/checker memory and detached-process resilience; improve execution without changing theorem meaning or losing diagnostics.

## Four-exotic route: reviewed mathematics, not yet fully formalized

Nine ordinary outputs pay for 27 distinct gates. Sink normalization and the budget of at most eleven unpaid gates give each exceptional cone at most eight unpaid gates and nine essential cut sources. Clamp9 forces all four raw line coordinates. Clamp paid sources to true, delete their network, and independently rebuild the nine ordinary outputs in 27 gates. This yields a raw-only four-output circuit with at most eleven gates. A globally ordinary reduced output would reduce to the checked three-exotic case.

To obtain OR roots, retarget each exceptional output to its first band-correct occurrence. A first AND occurrence and its two distinct generated parents can be clamped away for other outputs and replaced by three direct OR gates for this target, reducing the exceptional count. Thus first occurrences must be OR in the hard case. Sink normalization and paid clamping preserve these OR tags unless the output becomes constant true, excluded by band correctness. Reapply Clamp9 to recover global line upper bounds. The reduced high-gate proof also handles unary/repeated highest-wire roots separately.

Independent mathematical notes: `lemmas/four_or_sinks.md`, `lemmas/four_sink_review.md`, and `lemmas/four_exotic_reduction.md`.

## Dead or disproved approaches

- Generic inequality `2*d-c-1 <= gates` for minimum certificate size d and mandatory-variable count c is false. Three disjoint AND3 blocks followed by majority-of-three use ten gates, have d=6 and c=0. This is only an auxiliary-conjecture counterexample.
- Simple private-gate counting and several per-gate component potentials have explicit counterexamples. Do not reuse them without stronger hypotheses.
- A last-AND elimination argument is invalid if its OR suffix reads earlier AND signals. The checked at-most-one-AND theorem is valid.
- Small diagnostic input sets admit circuits that fail the full band. Validate all 3,003 rows before reporting a gap counterexample.

## Execution and review discipline

Source `/tmp/oec/pequalnp-pilot-21/setup/env.sh` before Lean commands. Build in `lean/` with `lake build PEqualNP.Outside.L_meta_1024`; never run lake update or build Mathlib from source. Preserve complete stdout/stderr in files. The warm cache is ready. Keep solver priority at nice 15 and coordinate large encoders with builds.

Every compiled result is preserved promptly on the fork after independent review. The branch may carry these owner-requested orchestration artifacts; any eventual proof PR must still have the repository-required single proof-file diff. Root handles that delivery preparation. Do not open issues or PRs.

## Next replan

At 03:47 UTC, review all strategy entries, retire stalled routes, and redistribute work. Continue 20–30 minute replanning thereafter. Overall job started at 01:28:21 UTC; the approximate six-hour budget ends at 07:28 UTC.

Sub-agents: counterexample_search, formal_baseline, fresh_proof, lease_timer, lower_bound, special_status, toolchain_setup.
TIMING total=115 subagents=7

## 2026-11-24 03:24:02 UTC — formal_baseline

Compiler update: SinkCut connects the checked Sink rewrite to Cut semantics with paid coordinates fixed true; its first build found only map-congruence elaboration issues, now fixed. DeadCore defines a pure dead-gate index-remapping compiler and proves its intended exact remaining-gate count/fan-in invariants; first combined build is running. Forward references remap to the current new output index and remain false. No new compiler file has compiled successfully yet; Sink.lean remains the last checked immutable component.

## 2026-11-24 03:24:04 UTC — lower_bound

Read the orchestration notes and lemma inventory. Continuing beyond the four-exception case; no new Lean compilation planned. The independently reviewed four-OR-sink contradiction is mathematically sound with the unary/repeated highest-wire repair. Its normalization bridge restores global line upper bounds after retargeting via the nine-essential-source bound. This remains an unformalized four-exception result, and does not settle cases with five or more exceptional outputs.

### 2026-11-24T03:24:32.551703+00:00 — lease_timer: checker recovery

The checker retry process20012 was blocked in a futex with no live child. Its mkdir lock lean/.lake/check.lock dated03:16:48 UTC, preceding the retry start, and the prior verifier19884 was a zombie after environment interruption. The checker has a60-minute stale-lock timeout. After verifying the directory was empty, its inode unchanged, and no live checker child/verifier existed, removed only that orphaned directory with root approval. No process was killed and no checker source changed. Complete diagnostic snapshots are in scratch performance/. The existing exclusive-flock lease timer remains root-owned; this agent no longer issues manual desk calls.

## 2026-11-24 03:24:54 UTC — fresh_proof

ThreeTriples.lean has compiled with an empty diagnostic log. It proves that three distinct-wire essential triples, with the first two disjoint and the third intersecting each in at most one point, require at least six gates. This is a conditional component of the four-OR-sink route, not the posted theorem. SharedParent.lean is building; it turns a shared high OR parent into three essential raw variables in the other parent. Next step is a finite ownership selection for four outputs and two high gates.

## 2026-11-24 03:24 UTC — counterexample_search

- All five sustained SAT processes were externally killed during the tool reset around 03:18:50; each was confirmed ZN/PPID1. Their complete logs and truncated gzip proof streams remain unchanged in scratch. No SAT/UNSAT verdict resulted. `search/interruption-0320.json` records exact paths and stream status.
- Five monitored searches restarted in detached sessions at 03:21:40–03:22:29, each with a fresh 90-minute budget and nice 15. Runner/solver pairs: fanout 20164/20167, 20165/20169, 20166/20171; full 20210/20248; normal 20436/20458. All were confirmed live after detachment. New roots are `search/full-strong-resume-0321/` and `search/full-normal-strong-resume-0321/`; launch manifest is `search/restart-0321-launches.json`.
- All restarts use independently reviewed exact support, live/sink normalization, lexicographic gate ordering, at least two ANDs (dual ORs in normal search), at least four globally nonordinary outputs, and nonordinary-implies-at-least-eight syntactic inputs. The three fanout cases use 671 band rows plus 104 partial off-band rows; full search uses all 3003 band rows plus 104; normal search uses all 1729 normal rows plus 104. Every SAT candidate must pass full independent scalar validation on the original 3003-row band.
- The original 60-minute full query, 30-minute normal query, three 30-minute fanout queries, and 30-minute symbolic five-output local query all ended UNKNOWN. These outcomes prove no lower bound. The completed symbolic three-output searches are computational local UNSAT results only.
- Auxiliary conjecture `gates >= 2*d-c-1` is refuted by majority of three disjoint AND3 blocks: ten gates, minimum satisfying support six, no mandatory variable. Independent scalar checking covered all 512 inputs and found exactly 22 satisfying assignments. Explicit gates/table: `search/minterm-generic/majority-three-triples-counterexample.json`. This is NOT a counterexample to L-meta-1024. The preceding five tiny dense SAT diagnostics were UNSAT for (n,d,s)=(4,3,4),(5,3,4),(5,4,6),(6,4,6),(6,5,8); their complete small logs/CNFs/proofs are preserved.
- No valid counterexample to the posted statement has been found. A concise archival package is being prepared in scratch for independent review before copying into `results/orch/search`. Root now owns lease control; further renewal requests go to root.

## 2026-11-24 03:25:34 UTC — formal_baseline

Checked compiler checkpoint: scratch baseline/DeadCore.lean compiled exit 0, complete log baseline/dead-core-build-002.log. It includes SinkCut.transform_cut_eq/output (paid-true cut semantics), Dead.code_length = Cut.unpaid, allowed-operation/fan-in preservation, and validity of remapped surviving wire indices. Root and independent reviewer notified; source frozen pending preservation. Full evaluation preservation and operation-tag preservation are drafted in Dead.lean but are not yet checked.

### 2026-11-24T03:25:41.196772+00:00 — lease_timer: verification and resource limits

Removing the stale lock unblocked the existing checker, which now runs a live checklemma verifier. The container cgroup grants 16 GiB RAM and 4 CPU cores (cpu.max is 400000/100000); host-level free output is not the applicable memory limit. At 03:25 UTC the verifier used about 9.1 GiB RSS and the five SAT workers about 4 GiB combined. No cgroup OOM events were recorded. Root has been warned to avoid concurrent new builds or large encoders until verification ends. Existing SAT workers are nice 15. The build queue defaults to 3 slots with 3 Lean workers each; this may oversubscribe the 4-core quota during concurrent proof builds. No queue configuration or process priority was changed.

### 2026-11-24 03:26 UTC — root: validation and memory

Latest checker retry faulted without a verdict (verifier exit137, wrapper exit3); cgroup OOM kill confirmed. The checker replays project declarations before checking whether the named theorem exists. Earlier no-theorem rejection and successful4455-line build remain valid records. Do not rerun the full checker on this known-incomplete module. Serialize Lean builds; actual resources are16GiB RAM/4 CPU cores, not host free-memory figures. Root will coordinate the next build slot. ThreeTriples and SharedParent have independent approval. DeadCore compiled and is awaiting independent review.

### 2026-11-24T03:26:41.473363+00:00 — lease_timer: checker memory fault and scheduling

The resumed checker exhausted the 16 GiB cgroup and the kernel killed its verifier: complete output is CHECKER FAULT: the verifier ended without a verdict (exit 137), wrapper exit 3. memory.events changed from oom 0 / oom_kill 0 to 1 / 1. No agent killed the process; root authorized a graceful cancellation just after the process tree had already exited. The exact named theorem remains absent, and the earlier no-theorem verdict remains the only prior rejection. CheckLemma.lean replays all project declarations before its named-theorem test, so repeating the partial check is costly. Full logs and resource snapshots are preserved in scratch performance/.

Safe scheduling recommendation: serialize Lean builds to one slot and one Lean worker while sustained SAT is active, and launch only when cgroup anonymous memory is below 8 GiB, leaving at least 8 GiB for the build and overhead. Final checker runs should have no concurrent builds or SAT workers, because the replay exceeded the remaining roughly 11 GiB with SAT active. Pausing SAT with SIGSTOP does not reclaim its RAM. Keep the queue implementation unchanged; root may set only the existing scratch queue build-slots.conf/build-jobs.conf to 1.

## 2026-11-24 03:26:43 UTC — lower_bound: extension constraints

For k exceptional outputs, ordinary charging gives at most 3k-1 unpaid gates; after sink normalization there are at most 2k-1 unpaid internal gates. Thus the per-output cut support bound is 2k+1. Existing Clamp9 directly covers only k<=4. The four-output proof therefore does not automatically iterate.

A read-once nonordinary output cone with at most nine essential variables has the form OR_U OR (OR_V AND G_T), with U and V partitioning its four-point line, V nonempty, and T consisting of four or five outside variables. There is only one outside guard: each requires at least four leaves, while at most five outside leaves are available. A four-variable guard is OR4; a five-variable read-once guard is OR5 or an OR of three literals and one two-input AND. This classification is mathematical, not Lean checked.

A fixed four-point guard set is disjoint from at most three projective lines: its four points meet sixteen incident lines with at most six pair-overlap savings, so at least ten of thirteen lines are met. A five-point set is disjoint from at most two lines (finite Python enumeration of all 1,287 five-sets confirmed this; not a Lean certificate). This limits cheap common guards but does not yet give a total gate count for arbitrary reconvergent circuits.

## 2026-11-24 03:27:02 UTC — special_status

Independent red-team review approved preservation of Sink, ThreeTriples, SharedParent, and DeadCore as partial components. Sink and ThreeTriples artifact copies and complete logs were byte-identical to the reviewed scratch originals. ThreeTriples proves a six-gate dependency bound under explicit triple-size/disjointness/intersection assumptions. SharedParent proves essential dependence using a band separating row and explicitly global upper bounds; its successful log is empty.

DeadCore contains the unchanged reviewed Sink prefix plus the reviewed SinkCut and deletion-compiler fragments. SinkCut preserves the current-list treatment of invalid reads. DeadCore proves exact remaining length, allowed operations/fan-in, and mapped-index validity; it does not yet claim evaluation preservation. Deleted indices use placeholder 0 and must have no surviving valid uses. Forward reads map to the current new output index and therefore remain false when that gate is evaluated. Forbidden-pattern/error scans were empty; imports/options are permitted.

The orchestration records correctly distinguish checked partials, unformalized four-output mathematics, auxiliary-conjecture counterexamples, and UNKNOWN solver runs. The lemma-index path correction to ../../../lean/PEqualNP/Outside/L_meta_1024.lean is confirmed. The exact named theorem remains absent, checker-partial.log records REJECTED (no-theorem), and no proof PR is approved by these reviews. Any eventual proof PR must retain the required single proof-file diff.

## 2026-11-24 03:27:15 UTC — fresh_proof

SharedParent.lean compiled successfully (empty shared-parent-build-001.log), and root received the source for review/preservation. The next conditional theorem HighNetworkCore is drafted: four globally line-bounded, band-correct OR outputs using two high functions and low partners from one prefix force that prefix to contain at least six gates. Its finite ownership selector and combined theorem are not compiled yet; builds are held while the checker occupies memory. formal_baseline plans an exact deleted-output formula interface to extract this representation from the reduced eleven-gate circuit.

### 2026-11-24T03:29:50.081539+00:00 — lease_timer: proposed final-file cleanup, not applied

Analysis snapshot is the 4,455-line target, SHA256 e5b0443b9f04e55ec2273e8c47d8904f8b8b0349d520ecfda291bf8cab4f3248. Tables (lines 1175–1498, 324 lines / 47,319 bytes) has no lexical reference outside its namespace. A proof of the lower bound can omit this standalone 8,192-bit validator and benchmark entirely; a refutation may need validate, in which case only benchmarkGates through benchmark_valid (1435–1496) should be removed. Separately, AndFirst26.witnessGates through condition_realized (1081–1170) is an unused 65-gate nonvacuity demonstration and can be archived outside the proof. Likely expensive kernel computations are Tables.periodicInputs_eq, Tables.band_value, Tables.benchmark_tables, and AndFirst26.witness_certificate; attribution is a static inference, not an isolated profile. No target changes made.

Lean 4.36 Replay.lean confirms replay is sequential and invokes addDeclCore with unlimited resource limits for each project declaration. It replays unused helpers too, before CheckLemma tests the named theorem. Reducing Lean worker count helps concurrent builds but does not cap this replay. Removing unused computational demonstrations is therefore preferable before the final checker run, while preserving their reviewed archival artifacts.

## 2026-11-24 03:30:30 UTC — formal_baseline

Compiler semantic draft ready: Dead.eval preserves every surviving wire, code_op_at preserves gate operation tags, and deleted_formula reconstructs deleted roots from the common surviving circuit while keeping original forward/self inputs false. CompilerExtra adds paidCode/paidIndex/paid_eval and no-read preservation. Dead.lean first run was intentionally interrupted with SIGINT (exit130, full log retained) when root serialized builds under the16GiB memory limit. Waiting for fresh_proof to release the single build slot; these new semantic lemmas are NOT yet checked. Deleting paid gates and all exceptional sink outputs in one pass yields the common internal circuit directly and avoids needing sink preservation under index remapping.

## 2026-11-24 03:30:44 UTC — special_status: search archive review

Approved scratch search/orch-package-0326 for copying to results/orch/search as branch metadata only. All 46 manifest entries match their recorded SHA256 and byte counts (1,056,393 bytes total); 45 copied artifacts also match their live scratch originals, and README is explicitly a generated archive description. manifest.json is the sole unlisted self-manifest. No unsafe paths, symlinks, Python syntax errors, or credential-pattern findings were found. All four small gzip traces decompress with intact CRCs; all five included CNFs have consistent headers, clause counts, and variable bounds. This does not certify LRAT derivations or the circuit-to-CNF translation.

The archive correctly distinguishes historical UNKNOWN runs, externally interrupted streams with no verdict, the currently running detached restarts, local restricted UNSAT results, diagnostic circuits that fail the required band, and the counterexample only to the auxiliary generic inequality. All imported exploratory helper sources are included, with nonportable scratch/solver paths disclosed. The normalization notes preserve chronology; README and restart sources consistently state the current >=4 nonordinary and >=8-support restrictions. No proof or refutation of L-meta-1024 is claimed. This archive must be excluded from an eventual single-file proof PR.

### 2026-11-24 03:31:14 UTC — root: general OR-output route

Mathematical proposal under independent review: choose a minimum-AND counterexample. If any first band-correct target occurrence is AND, its two distinct generated parents and itself can be clamped/deleted for other targets and replaced by three direct OR gates, reducing AND count without increasing size. Thus all first target occurrences can be OR; retarget and sink-normalize to obtain OR sink outputs. This is not yet fully formalized.

The shared-parent essential-triple argument can use band correctness alone: the separating positive row has seven true inputs; after flipping its sole line point, extend the remaining six outside-line points to an eight-true negative band row. Monotonicity then forces the opposite parent false at the flipped row, avoiding a global upper-bound hypothesis. Fresh is formalizing this weakening; lower_bound is exploring a global parent-incidence lower bound.

## 2026-11-24 03:32:00 UTC — fresh_proof

Ownership.lean compiled (ownership-build-003.log) and the combined HighNetwork.lean compiled (high-network-build-002.log). The conditional theorem FourOrSinks.high_network_lower proves six gates are needed in a common low-prefix circuit when four distinct line outputs are either the OR of two shared high functions or the OR of one high function and one low-prefix signal. It assumes band correctness and global line upper bounds; both-high uniqueness follows from correctness. Root received both successes immediately. The build slot is released to formal_baseline. A stronger band-only version is drafted: shared-parent essential variables follow by extending the flipped six-true witness to a negative eight-true band row, using low-partner monotonicity. This removes the global-upper assumptions, but that stronger version is not yet compiled.

## 2026-11-24 03:32:22 UTC — formal_baseline

Checked semantic compiler checkpoint: baseline/Dead.lean compiled exit0; complete log baseline/dead-build-002.log. Dead.eval preserves every surviving source wire under NoReads, and code_op_at preserves surviving gate operation tags. Root/reviewer notified and file frozen. Compiler.lean now builds sequentially in the granted single-build slot; its deleted-root formulas and paid-clamp wrappers remain unverified until that build succeeds.

## 2026-11-24 03:33:27 UTC — special_status: compiled components and OR-output normalization

Approved Ownership.lean and HighNetwork.lean for preservation. HighNetwork contains the unchanged ThreeTriples, SharedParent, and Ownership components, then proves only a conditional common-prefix length >=6 from four injective line IDs, explicit one/two-high OR decompositions, band correctness, and global line upper bounds. Successful logs contain only the finite ownership letI style warning. Forbidden syntax scans were empty; drop the standalone target import when integrating.

Approved Dead.lean and its complete dead-build-002.log. Its reviewed DeadCore prefix is byte unchanged and its sole added fragment is exactly DeadExtra.txt. NoReads excludes valid references to deleted coordinates while allowing invalid future references; Dead.eval preserves all surviving valid source values, and code_op_at preserves their gate tags. Invalid references map to the current compiled output index and remain false at evaluation. No operation/fan-in hypotheses are needed for the exact evaluator identity. Only permitted imports/limit options occur, no forbidden constructs or logged errors were found.

The general all-OR-output normalization is mathematically sound with a useful precision: choose lexicographically minimal (AND count, gate count) among all <=38 band-correct counterexamples. Full symbolic constant propagation never adds AND gates; do not count the intermediate Sink OR-to-nullary-AND rewrite as the final circuit. Any valid output use permits clamping later uses true and deleting its first consumer, contradicting gate minimality. An earlier target occurrence permits retargeting and deletion of the old sink. Thus outputs are already first occurrences and sinks. A first AND target has two distinct generated parents; deleting those parents and the AND root after clamping, then adding three direct OR gates, preserves all other band targets and strictly decreases AND count. Parents dominate the desired target only on the band, and dominate the actual AND-root function globally. OR padding and the reviewed point/ordering/fanout normalizations preserve OR output roots. This normalization is not yet a Lean theorem.

## 2026-11-24 03:34:09 UTC — lower_bound: parent-incidence extension

The apparent k=5 high-parent obstruction K4 minus one edge is ruled out by stronger essential-support counting. Label its five edges by distinct projective lines. For each high vertex v, force the support union E_v over incident edge (v,u) labeled L and every other edge at u labeled M of L minus M. This follows from the shared-parent essential lemma. All 154,440 assignments of five distinct lines were enumerated: the dependency-component rank of the four E_v is always at least ten (56,160 rank-ten, 84,240 rank-eleven, 14,040 rank-twelve). Hence these four high functions cannot be computed by nine internal gates. Source and complete log: /tmp/oec/pequalnp-pilot-21/lower-bound/high_graph_essential.py and high_graph_essential.log. This is exhaustive Python evidence for one structural case, not a Lean certificate or a complete k=5 proof.

The shared-parent essential witness needs band correctness and monotonicity only, not global line upper bounds: after flipping the unique true target point off, extend the resulting six outside true points to a negative eight-true band row. Root and fresh_proof independently identified this improvement.

## 2026-11-24 03:34:15 UTC — special_status: static replay-cost cleanup review

Approved performance/cleanup-candidate.lean for a serialized build, not yet as a compiled replacement. It is exactly the two proposed deletions from the 4,455-line snapshot: AndFirst26 witness demonstration at old lines1081–1170 and the entire unused Tables namespace at old lines1175–1498. The candidate has4,041 lines; every retained byte is unchanged, namespace boundaries are intact, and no Tables or removed witness-declaration references remain. Imports/options and forbidden-construct checks pass. The original snapshot is byte-identical to committed4f2bed9, preserving all removed components in branch history. Candidate SHA256: fedc8bbbadf14777289c73f9535adf516c8c467fdcd3ecb2c8b00acfcca704aa. Restore/retain the validator if the eventual result becomes a table-validated refutation.

## 2026-11-24 03:35:00 UTC — formal_baseline

Checked complete compiler checkpoint: baseline/Compiler.lean compiled exit0 (compiler-build-002.log). New helpers in CompilerExtra.txt include deleted_formula with original forward/self inputs explicitly false, paidCode/paidIndex/paid_eval matching paid-true Cut semantics, exact Cut.unpaid length, operation/fan-in preservation, OR-tag preservation under a false output assignment, and union/no-read preservation for simultaneous paid/output deletion. Root/reviewer notified; immutable source pending preservation. Single build slot released to fresh_proof. Generic append-three-OR constructor is drafted but uncompiled in AppendLine.lean.

## 2026-11-24 03:35:10 UTC — counterexample_search: archive and OR-sink normalization

The reviewed 46-file search archive and its manifest were copied byte-for-byte to `results/orch/search/0326`; all hashes were rechecked before and after copying. No child commit or push was performed. Root has the named-file manifest for staging.

General all-OR-output-sink normalization received independent mathematical approval. Choose a counterexample lexicographically minimizing (AND count, gate count) among size<=38 circuits. Full constant propagation is essential: symbolic true clamps can delete OR-to-true nodes and collapse AND-with-true copies without adding permanent AND gates. Sink or nonfirst output uses would lower gate count without increasing AND count. A first AND target has two distinct prior generated parents; clamping/deleting those parents and that target, then appending three direct OR gates, lowers AND count. Thus one may assume all output sinks are first OR occurrences. This is a reviewed existential normalization, not yet a Lean-checked general bridge. It is compatible with live OR padding and existing symmetry/fanout/order normalizations.

Prepared scratch `search/cegis-or-sinks.py` by adding only thirteen output-OR units to the reviewed full encoder plus distinct output paths/metadata. It is under final code-diff review. No new encoder or solver has launched; root plans to consider replacing the unrestricted full query at the 03:47 replan while retaining all other live queries.

## 2026-11-24 03:35:45 UTC — special_status: compiler wrappers and future OR-sink encoder

Approved Compiler.lean for preservation, SHA256761e1552e594643bcd4f4e3ace2b8e140b1b499fa25e3b2cb9538ed8c8ff99cb. It is the byte-unchanged reviewed Dead prefix plus exactly CompilerExtra.txt. deleted_formula explicitly preserves original forward/self-read falsity via i<n+j. paid_eval excludes paid outputs and raw paid coordinates and realizes the exact paid-true Cut semantics; paid_length, allowed operations, NoReads unions, and OR-tag preservation have explicit sufficient assumptions. Successful log contains only harmless prefix warnings; no forbidden constructs. These are compiler helpers, not the posted lower bound.

Approved the frozen future search/cegis-or-sinks.py, SHA25616c9f86037011b60d2251a65408c8f16e9d1d77a47ee5793daffaa02f8fc9dff. Its exact delta from the reviewed unrestricted resume encoder is a distinct output directory, updated scope metadata, and thirteen negative operation units on gates25–37. With op=false meaning OR, these are precisely the thirteen decoded output gates. No normal-dual assumption is added; full-band mode, >=4 nonordinary flags, guarded support>=8, and independent scalar candidate checking are unchanged. Mathematical normalization remains reviewed rather than Lean formalized. No active query was changed by this review.
