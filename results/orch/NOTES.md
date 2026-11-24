# L-meta-1024 orchestration notes

Status summary updated 2026-11-24 03:48:05 UTC. Owner: root. Branch: pnp/pilot-21.

## Read before starting

Read this file and `lemmas/README.md` before each new assignment. Append findings here with UTC timestamps and your agent name. Use an exclusive file lock for concurrent append operations; do not overwrite another agent's notes. Record only verified results as checked. Keep counterexamples to auxiliary conjectures distinct from counterexamples to the posted statement.

Only root controls the single L-meta-1024 lease and publication. Do not acquire, release, or submit any gap. The existing exclusive-lock renewal timer is root's automation; request a renewal from root before a long build or search. Never record authentication material.

## Goal and current status

Prove the exact posted theorem in `lean/PEqualNP/Outside/L_meta_1024.lean`: a fan-in-at-most-two monotone circuit producing the thirteen projective-line ORs on inputs with five or six false coordinates needs at least 39 gates. The line at w is `{0,1,3,9}+w` modulo 13. There are 3,003 required input rows.

The current 4,041-line target passes the named-module lake build; its source is pushed at `0fb15ea`. It contains partial results, not the exact named theorem. The local checker previously rejected it with `REJECTED (no-theorem)`; the fresh retry faulted without a verdict after an OOM kill (verifier exit137). No proof PR exists. No valid counterexample to the posted statement has been found.

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
6. **toolchain_setup — global total-gate proof.** Investigate collective selected-DAG avoidance and charge AND routing costs; the weaker individual-domination OR-packing inference is disproved. The passive resource watcher prepared by lease_timer continues; root owns renewals and build admission.

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

Next review at 04:39 UTC. The first 25-minute review completed at 2026-11-24 03:48:05 UTC. Continue 20–30 minute replanning thereafter. Overall job started at 01:28:21 UTC; the approximate six-hour budget ends at 07:28 UTC.

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

## 2026-11-24 03:37:59 UTC — fresh_proof

FourPairs.lean compiled exit0 (four-pairs-build-003.log; only inherited Ownership style warning). The stronger shared-parent dependence lemma and high-network theorem require band correctness and monotonicity, without global line upper bounds. The final FourOrSinks.four_pairs_impossible theorem rules out four injectively labeled, nonordinary, band-correct line outputs represented as OR pairs over a common monotone fan-in-two circuit of at most seven internal gates. It handles missing/repeated/invalid parents, extracts the five-gate prefix, and uses the small-support exactness theorem to force each root to use one of the last two internal indices. Root received the success immediately; source frozen for review and preservation. The full four-exotic reduction and arbitrary thirteen-output lower bound remain incomplete.

New assignment: draft first-AND normalization with exact AND-count accounting. Planned compiler method: close the three forced-true seeds under constant propagation (evaluate the seeded cut at all raw inputs false), delete every generated wire forced true, and use the surviving original operation tags. This must remove OR-to-nullary-AND intermediates before comparing AND counts. No new normalization result is yet checked. Build slot released to performance cleanup, then formal AppendLine.

### 2026-11-24T03:39:18.777078+00:00 — lease_timer: cleanup candidate compiled

special_status independently approved the exact static deletion-only diff. The 4,041-line scratch cleanup candidate then compiled with exit 0 in 27.635 seconds; process max RSS was 7553136 KiB. Candidate SHA256 is fedc8bbbadf14777289c73f9535adf516c8c467fdcd3ecb2c8b00acfcca704aa. Complete build log, exit file, timing JSON, candidate, original snapshot, and patch are in scratch performance/. Target remains unchanged, and the local checker was not run. Root was notified immediately for preservation; the serialized build slot was released to formal_baseline at 03:39:01 UTC.

## 2026-11-24 03:39:50 UTC — special_status: four-output obstruction, streaming, and cleanup

Approved compiled FourPairs.lean, SHA2565546b73f1e6366288e5602d1c5a78fb825fb881172d1b159d130bfb8231735c7. The band-only shared-parent lemma correctly extends the flipped input to a negative eight-true band row and uses low-parent monotonicity. high_network_lower_band removes the global upper premise. four_pairs_impossible explicitly assumes at most seven internal gates, four injective line labels, OR-pair band correctness, and global nonordinariness; it handles short lists, repeated parents, and invalid indices. This is the conditional four-output obstruction, not the full posted theorem. Only the inherited letI style warning; forbidden scans empty.

Approved streaming_cnf.py (SHA2565c93998e77af73b0bb9d3f457d086153ac4e281776eb247daba51314ac056aab) and cegis-or-sinks-stream.py (SHA256185cd4fc3e81e0e0e3e022555859a03635e7c4a2ff21b9ae02eb31650fd5a8fe). Exact base var/one inheritance and clause/header serialization preserve the encoder; all four complete fixture pairs independently byte-match, including48,300 clauses and the empty clause. Exclusive per-run body/part creation and flush/copy/size-check/close/atomic-rename sequencing are sound for the intended unique output paths. Failed writes retain artifacts and do not proceed to solving. No active query changed.

Cleanup compilation confirmed from complete performance/cleanup-build.log and cleanup-build-result.json: exit0,27.635s, peakRSS7,553,136KiB,17warnings and noerrors. Candidate hash remains fedc8bbbadf14777289c73f9535adf516c8c467fdcd3ecb2c8b00acfcca704aa. The previously reviewed exact two-block cleanup is now approved for compiled preservation/application on the proof route. This is not a checker pass.

### 2026-11-24T03:40:02.747705+00:00 — lease_timer: passive monitoring and reset recovery

The detached memory watcher records full process snapshots and cgroup counters every 5 seconds in scratch performance/. Seven observed serialized Lean compiles, including cleanup-candidate, stayed below 5.28 GiB total anonymous memory with five SAT workers active; OOM counters remain unchanged since the verifier incident. The watcher is read-only and can be stopped via memory-watch.stop.

For another execution-environment reset, inspect both lock mechanisms: check-lean.mjs uses a PID-less mkdir lock with a 60-minute timeout, while build.sh considers a slot alive whenever kill -0 succeeds. A zombie PID can therefore retain a build slot even though no build remains. Only remove an empty checker lock or queue slot after verifying its former holder is gone/zombie and no live owner exists. Current queue scan found no pid/config files; root is serializing builds by coordination. Root separately replaced the lease timer with a detached exclusive-lock process; only root controls desk operations.

2026-11-24 03:40:47 UTC — root: The reviewed cleanup candidate compiled independently and is now the4041-line target: removed only unused Tables validator/benchmark and AndFirst26 witness demonstration,414lines total. All retained bytes are unchanged. Prior4455-line checkpoint remains committed. A fresh named-module lake build is pending; no new checker pass is claimed.

## 2026-11-24 03:42:25 UTC — lower_bound: overlapping-pair surcharge assignment

Root reassigned this agent to formalize the following charge-family surcharge in an owned scratch Lean file importing the current target: if an ordinary line has two charged gates with distinct overlapping two-point singleton cores, then its charge family has at least four gates. Strategy: under a three-gate charge budget, the first bounded full-four-point-core wire has only the two pair-core gates available earlier. An AND cannot be first, because some false-at-line-complement parent already has the full core. An OR cannot cover four singleton points using two overlapping pairs, or one pair and one singleton.

Potential five-exception continuation: the missing-raw argument gives at most two raw essential cut sources and nine paid pair-core witnesses. Pigeonholing eight ordinary owners gives the overlapping pair, hence one extra paid gate and cut-source bound ten. Pick a raw-missing line point outside the repeated owner line (three candidates, at most two raw sources). The six-zero cross witness kills both repeated-owner paid gates, leaving at most eight positive essential sources, contradicting positive_frontier_impossible. This remains mathematical until the premises and compiler bridge are formalized.

The structured pair-AND/prepared-OR stress test of the surviving cumulative component potential completed 1,153,443 mutations in thirty seconds without a violation. It is evidence only. Complete source/log: lower-bound/stress_pair_guards.py and pair_guard_stress.log in scratch.

## 2026-11-24 03:43:02 UTC — special_status: selected-DAG branch-packing counterexample

The stronger inference to branch-vertex-disjoint selected trees, or to sum(|L|-1) OR gates, is false under the proposed abstract domination condition. An explicit graph for the four concurrent Singer lines0,4,10,12 has18AND gates and10OR gates, while four branch-disjoint four-terminal selected trees need12OR branching vertices. Each line-selected DAG contains exactly its four terminals, selects both OR children and one false-at-complement child at every selected AND, and passes all504 shared-gate/nonintersection-terminal nondomination checks. All8192 assignments confirm every actual output is globally bounded by its designated line. The outputs are not band-correct: each has867 errors on the required band. Thus this is only an auxiliary packing counterexample; its28total gates do not refute the proposed total-gate inequality or L-meta-1024.

Construction: write the lines as {0,a_i,b_i,c_i}. Make two independent AND4 routers for each private-position array (A1,A2,B1,B2,C1,C2). Set u=0 OR A1, v=A2 OR B1, w=B2 OR C1, z=C2 OR0, h=u OR w, k=v OR z, and use four distinct sink gates h OR k. For owner i, route each AND tree to its corresponding private point. Every private terminal has paths through both h and k, so every shared gate has a bypass. The6shared OR gates plus4sink OR gates cannot pack12distinct branching vertices. Explicit graph, selections, finite checks, and precise scope are in scratch packing-review/selected-packing-counterexample.json and selected-packing-check.log. Root, lower_bound, and toolchain_setup were notified. A valid total-gate argument must account for AND routing cost, as in lower_bound's Euler deficit formulation.

## 2026-11-24 03:44:15 UTC — toolchain_setup: collective selected-DAG avoidance

For distinct target lines L and M and p in L minus M, delete simultaneously every selected-L node globally bounded by the M line OR. A selected-L path from its output to p must remain: the six-zero row M union (L minus {p}) makes every deleted node false and every other selected raw leaf false, while band correctness requires the L output true. A false-evaluation induction on the selected DAG proves the contrapositive. In particular deletion of all selected-M nodes is allowed. lower_bound independently confirmed this mathematical premise. It is stronger than individual shared-node nondomination and excludes the duplicate-router example because both high routers are deleted together. It is not yet a formalized Lean lemma or a total-gate packing theorem.

## 2026-11-24 03:44:30 UTC — formal_baseline

Checked append-line constructor: baseline/AppendLine.lean compiled exit0, append-line-build-002.log. AppendLine.appendLine adds exactly3 OR gates, computes the target line OR globally at15+old length, and preserves every earlier valid wire; allowed/length/output_valid checked. Root/reviewer/fresh notified, source frozen. Reduction.lean now builds sequentially: Cut.cutVal_add_sinks/essential_add_sinks and PaidClamp.correct_and_bounded (≤12 support sources with all4 raw line coordinates ⇒ paid-true clamp preserves band correctness). These Reduction lemmas are not yet checked.

## 2026-11-24 03:44:43 UTC — counterexample_search: pre-replan snapshot

0: 23.0min, no verdict/model; 1: 23.0min, no verdict/model; 2: 23.0min, no verdict/model; full: 22.8min, no verdict/model; normal: 22.2min, no verdict/model. All five monitors and solvers are live (SNs/RN), with solver nice15. No SAT model or UNSAT verdict has appeared in these restarted queries.

Cgroup memory.current=13.83GiB of 16GiB, anonymous=5.04GiB; disk free=13.02GiB. No new encoder/build was launched.

The independently reviewed OR-sink replacement is ready in both frozen forms: list writer `cegis-or-sinks.py` SHA16c9f860..., streamed writer `cegis-or-sinks-stream.py` SHA185cd4fc... plus `streaming_cnf.py` SHA5c93998e.... Four small fixtures, including48,300clauses, are whole-file byte-identical. Planned root-authorized replacement interrupts only full solver20248, lets monitor20210 retain a clean UNKNOWN/log/gzip closure, then starts the streamed all-OR-sink full query in a unique directory. No interruption has occurred yet.

A separate k=5 K4-minus-edge-with-ordinary-helpers source is prepared at scratch `search/cegis-graph-five.py`; it is not launched or yet independently reviewed. It allows four arbitrary high signals selected from nine internal gates, all edge-to-target assignments, and all fifteen direct-tree shapes for each of eight other outputs. Unused high-network padding is allowed. Every candidate still receives the existing full3003-row scalar validation.

## 2026-11-24 03:45:33 UTC — fresh_proof

General first-AND normalization is now drafted end to end, but uncompiled: TrueClampExtra defines two-stage true-constant cleanup; AndCostExtra proves a generic retained-tag AND-count bound; SeedPreserveExtra preserves all other targets; SurgeryExtra adds the three direct OR gates; FirstAndParentsExtra extracts two distinct earlier generated parents from a first AND target; FirstAndImprovementExtra packages strict AND decrease without increasing total size. The cleanup uses T=Sink.transform(S,gs), P=generated wires true at T(all-false), then deletes S union P after clamping P. This removes every introduced nullary AND.

A mathematical simplification sent to root: minimum AND count alone suffices. Choose first band-correct occurrences, exclude AND by the surgery, retarget to the OR occurrences, and apply the checked Sink transform. The final normalized circuit need only retain its size bound and OR output tags, so any internal AND-count increase during final sink normalization is irrelevant. No minimum-gate tie-break or unary-copy deletion is needed for this existence statement. These new first-AND claims remain unchecked.

## 2026-11-24 03:46:23 UTC — formal_baseline

Checked reduction helpers: baseline/Reduction.lean compiled exit0, reduction-build-001.log. Cut.cutVal_add_sinks and essential_add_sinks show that adding unread sink outputs to a cut changes no other output or essential set. PaidClamp.correct_and_bounded proves paid-true clamping preserves band correctness (and gives a global line upper bound) when E has≤12 sources, contains all4 raw line inputs, and remaining paid sources have outside singleton witnesses. Its foreign-support count is≤8. Root/reviewer notified, immutable source pending preservation. Current build batch complete and single slot released.

## 2026-11-24 03:46:30 UTC — special_status: AppendLine and replan assessment

Approved AppendLine.lean (SHA25634e63e18eefade3a22274fdd6511b610c9efd063fbee95a8ffa5c9326cc09def). The Boolean grouping is exactly (x_w OR x_(w+1)) OR (x_(w+3) OR x_(w+9)); the new output is15+oldlength, length increases by3, and existing valid wires are unchanged. The new tail exactly matches AppendLineExtra.txt. Seven inherited prefix edits only narrow arithmetic simp calls to explicit list-length lemmas and change no statements/definitions; immutable Compiler.lean itself is unchanged. Integrating only the extra fragment avoids carrying those unrelated proof-local edits. Complete build log has warnings only.

Replan assessment: the four-exotic result now has a concrete formal path through FourPairs plus paid-clamp/rebuild and first-AND normalization, but still does not settle arbitrary exotic count. The unrestricted path needs a global count after OR-sink normalization; collective selected-DAG avoidance is mathematically sound, while individual nondomination does not imply disjoint branching trees or an OR-only bound. For k5, lower_bound's negative-row argument forces distinct exact singleton cores {intersection,q} before pigeonholing; this repairs the otherwise insufficient repeated-owner argument. The paid family P and essential set E must remain fixed when the surcharge tightens the budget. Formal raw-source bounds and the remaining parent-graph cases are still required; K4-minus-edge enumeration is only one case. Current archives accurately separate checked partials, auxiliary counterexamples, restricted/UNKNOWN search outcomes, and unformalized normalization. Minor inventory update needed: Tables is no longer a current main-file namespace.

## 2026-11-24 03:47:49 UTC — formal_baseline:03:47 assignment

Read the refreshed orchestration notes and lemma inventory. Finishing append-list and deleted-OR-root interfaces, then assembling the four-exotic reduction against FourPairs. Assembly.lean now contains uncompiled drafts: appendLines with exact3*length cost, allowed gates, old-wire preservation and generated global line outputs; deleted_or_pair converts each deleted OR root to two fixed internal read indices with20 as false padding. Build queue is root named module, lower surcharge, fresh normalization, then this assembly batch. Existing compiled Reduction/AppendLine remain immutable.

## Replan 1 — 2026-11-24 03:48:05 UTC

Read the accumulated notes and independent assessment. Decisions:

- Keep L-meta-1024 and its sole lease. No exact proof, counterexample, acceptance, or PR exists. Named-module build of the 4041-line source passed; do not repeat the costly checker while the named theorem is absent.
- Double down on the concrete four-exotic route. formal_baseline assembles the checked compiler, paid clamp, append-list construction, and FourPairs interface. fresh_proof formalizes first-AND surgery, preserving a specified ordinary-output family, then the minimum-AND OR-output normalization.
- Continue the five-exotic extension: lower_bound formalizes the overlapping-pair charge surcharge, then support-budget tightening; keep the same paid set P and essential set E throughout. Full parent-incidence case coverage is still required beyond the K4-minus-edge case.
- Retire individual-nondomination branch-disjoint-tree and OR-only counting. toolchain_setup investigates the stronger collective avoidance condition and total cost including AND routers. Auxiliary counterexamples must remain clearly scoped.
- Replace only the unrestricted full SAT run with the independently reviewed streamed OR-sink query after a fresh renewal. Preserve the old run as a strategy interruption with complete logs; keep the other four runs. Prepare, but do not yet launch, a focused five-output helper-sharing query for a distinct search direction.
- Keep one Lean build at a time. Root named-module build is complete; after the brief SAT transition, lower_bound has the next slot, then fresh_proof, then formal_baseline. Final checker requires its own memory window.
- Preserve every reviewed compiled component and complete log promptly. Continue shared notes with file locks. Next replan: 04:13 UTC.

## 2026-11-24 03:48:55 UTC — special_status: reduction and scoped search preparation

Approved Reduction.lean, SHA256907ad5e2a96f83aac768810176252f5e7d22720f42a11cfa5dd9e06770a1e68b: unchanged Compiler prefix plus exactly CutSinksExtra.txt and PaidClampExtra.txt. NoReads makes added sink cuts invisible outsideQ, including invalid indices. PaidClamp removes four distinct raw line sources from E of size<=12, leaving<=8 foreign sources; explicit outside singleton witnesses give one negative eight-true row making all foreign sources true. Support-restricted monotonicity yields both global line upper bound and band correctness after paid clamping. Assumptions and syntax are clean; complete successful log has19prefixwarnings/noerrors.

Approved frozen cegis-graph-five.py (SHA256703f062a279a52965bdf82e22958ae0b6d41b10ac1996f5dac6f8c1eaa2cbd8e) only as the stated restricted template. Four distinct high selectors among nine residual internal gates, a free five-edge/target bijection, sorted endpoint guards, and the two degree-class graph automorphisms are encoded correctly. Internal liveness is omitted solely to permit unused padding; output sinks, lex ordering, compatible direct trees, and scalar validation remain. This is not coverage of all five-output topologies. The generated-high restriction can also be justified within this graph: shared-parent dependence excludes raw high signals, and an ordinary pair/triple OR port cannot be bounded on the band by both distinct incident line targets.

Approved search/orch-package-0349 for metadata copying/preservation: all7manifest entries and20,474bytes match recorded hashes and source copies; only the self-manifest is unlisted. Test source, exact byte-equality evidence, dependency paths, and preparation-only scope are consistent; no unsafe paths, credential-pattern findings, or Python syntax errors were found. No new solver was launched by this reviewer.

## 2026-11-24 03:49:07 UTC — counterexample_search: authorized OR-sink replacement

Root authorized replacing only the old unrestricted full query. Solver20248 received SIGINT at03:48:35; monitor20210 finished cleanly after1601seconds with UNKNOWN, not UNSAT. Complete old logs and gzip trace remain unchanged; gzip integrity passed (43,927,006 compressed bytes;154,103,808 uncompressed; SHA256 cffda41575bc674a55d9dc807a35633578871f96ee78ef212d180747c676b13a). Full strategy-interruption metadata is scratch search/strategy-replacement-0351.json.

The reviewed streamed all-OR-sink full query launched detached at03:48:55, runner24940, budget5400seconds, nice15, all3003bandrows. Its unique artifact directory is scratch search/full-or-sinks-stream/case--1; exact sources were snapshotted with hashes. Other four queries continue unchanged. Encoder completion and solver PID are pending. Root renewal03:48:06 expires04:08:06.414Z.

The independently approved seven-file source/test supplement was copied verbatim to results/orch/search/0349; manifest.json is the staging inventory. No child commit or push was performed. Graph-five also passed independent review and remains unlaunched.

2026-11-24 03:49:49 UTC — counterexample_search: streamed encoder completed in about12seconds; new solver24948 is live under detached runner24940, nice15. CNF has361,079variables and12,667,419clauses. All3003 band rows are encoded. Encoder memory slot released to root; no verdict/model yet.

## 2026-11-24 03:51:13 UTC — lower_bound: PairSurcharge compiled

PairSurcharge.lean compiled successfully on its first attempt (exit 0). Source is frozen at scratch lower-bound/PairSurcharge.lean, SHA256 45ffd7615f2e15eaf7ca2bee0436e0b20596969a7c5c6ea12d613bd3aeb20ca9; complete log lower-bound/pair-surcharge-build-001.log. Generic overlapping_pair_charge and its ordinary-output wrapper prove at least four D charges from a four-point full singleton core and two distinct charged gates with overlapping two-point singleton cores. The proof handles original invalid/self/forward reads with an explicit masked gate formula. It does not assume well-formed input indices or distinct singleton points beyond what charged membership and distinct gate indices already imply. Root was notified immediately and independent review requested. The single build slot has been released. This is a checked surcharge lemma, not the exact posted theorem or a completed five-exception theorem.

## 2026-11-24 03:53:06 UTC — lower_bound: missing-raw witness formalization

Read the refreshed notes/index and began the next primary assignment. Planned standalone witness API keeps the original paid set P and essential set E fixed. First construct a positive band row with one designated line point true and any three other selected raw coordinates false; use positive_frontier_impossible to show a missing raw line input forces at most two raw coordinates in E when card E<=11. Then kill all raw coordinates in one positive row and compare against each of the nine negative rows containing eight outside points. Monotone separation forces a paid essential coordinate for each outside point, with an exact pair singleton core by owner-line intersection. Distinct outside points force distinct paid coordinates. The surcharge and fixed-set cardinal tightening will be connected afterward. This is not a completed five-output graph case split. No new Lean build started; fresh_proof currently owns the slot.

## 2026-11-24T03:55:35.903536+00:00 — formal_baseline: four-output assembly batch

Fresh FirstAnd normalization compiled and released the build slot. Complete uncompiled drafts are Assembly.lean (append-list/deleted OR pair), SmallFamily.lean (all four outputs nonordinary in a <=11-gate correct residual), FourBound.lean (at least39 gates under nine ordinary outputs plus four OR sinks), and NineOrdinaryExtra.txt (combine minimum-AND normalization, then derive at least5 exotic outputs in any <39 counterexample). Root renewal requested before serialized compilation. No exact posted theorem is claimed.

## 2026-11-24 03:55:38 UTC — fresh_proof

FirstAnd.lean compiled exit0 on first-and-build-002.log. Root, independent reviewer, and formal_baseline received immediate notification; source is frozen with SHA256172d015fd5441ce6fef737441521d0a73a939cb0e003ba95e932ddf7e9d71ffe. New checked namespace TrueClamp includes: two-stage constant cleanup; strict AND-count decrease when an AND seed is deleted; preservation of every other band target and every previously ordinary output; first-AND parent extraction; first_and_improvement; and normalize_or_sinks. The final existential theorem preserves an arbitrary specified ordinary set W, keeps total gate count no larger, makes every output a sink (NoReads), and makes each output outside W an actual OR gate. It uses minimum AND count among correct circuits preserving W, without a gate-count tie-break.

This is a general normalization theorem, not the posted39 lower bound. formal_baseline now has the build slot for FourBound and the finite wrapper: choose exactly9 ordinary outputs for W, then the complement has exactly4 OR roots after normalization. The successful log contains only deprecated-tactic/unused-simp warnings, including inherited prefix warnings. No forbidden syntax appeared in the new extra files.

## 2026-11-24 03:55:44 UTC — counterexample_search: derivative-only diagnostic correction

The previously archived29-gate157-row dual diagnostic, after swapping AND/OR, computes all13 target ORs on the65 rows consisting of every line complement Z_L and its four additions Z_L+{p}. Independent scalar validation checked those65 rows and all8192 inputs: every output is globally bounded above by its designated line OR. It still fails the actual band on nine outputs with213errors each. Thus these derivative rows plus global upper bounds cannot prove39gates. This corrects my earlier statement to toolchain_setup that no existing diagnostic settled those rows. The original29gate artifact is already archived in0326; scratch search/diagnostic157/derivative65-original29.json records the converted circuit and new complete checks. No new SAT solver or Lean build was run.

## 2026-11-24 03:56:29 UTC — toolchain_setup: cycle-space reduction and diagnostic exclusion

The exact remaining graph target is existential: choose selected paths for the line-point incidence edges so that the induced GF(2) cycle map is injective. For k four-point lines on N raw inputs, its required cycle rank is 3k-N+1; a connected binary circuit with g gates has rank at most g-N+1. An injection yields g>=3k. Equivalently, choose independent representatives from three fixed raw-boundary cosets (terminal-pair path plus selected-DAG cycle space) per line. Merely choosing independent triples from the full chain spaces is insufficient because they could be cycles. special_status identified this qualification and supplied an example showing arbitrary path choices can cancel incidence cycles even in a globally correct circuit. No existential injection theorem is proved yet. Precise reduction and missing step: scratch research2/cycle_space_route.md.

A short finite check enumerated every false-AND selection in counterexample_search's globally bounded 29-gate derivative diagnostic. None of its nine non-pencil outputs satisfies collective avoidance; all four ordinary pencil outputs do. Thus this diagnostic refutes derivative-only potentials but not the stronger selected-DAG route. Full source, JSON, and log: scratch research2/collective_diagnostic.py, collective_diagnostic.json, collective_diagnostic.log. No solver or Lean build was launched.

## 2026-11-24T03:58:02.790670+00:00 — formal_baseline: assembly checkpoints

Assembly.lean compiled exit0 (assembly-build-002.log), then SmallFamily.lean compiled exit0 first attempt (small-family-build-001.log). Both sources frozen and root/reviewer notified. Assembly adds arbitrary append-list of exact line ORs with three gates per line and preserves old valid wires; deleted_or_pair converts a deleted OR root to two fixed internal indices, with20 as false padding for a <=7-gate code. SmallFamily shows all four target outputs in any <=11-gate band-correct circuit are globally nonordinary, because appending9 direct outputs would otherwise contradict the ten-ordinary lower bound. FourBound.lean now compiles sequentially; it has not passed yet.

## 2026-11-24 03:58:27 UTC — special_status: normalization and residual-circuit reviews

Approved PairSurcharge.lean, SHA256 45ffd7615f2e15eaf7ca2bee0436e0b20596969a7c5c6ea12d613bd3aeb20ca9, with an empty successful log. Under a three-charge budget, the two supplied pair-core nodes and full-core output exhaust D. Earlier false-at-complement parents therefore have a supplied pair core or at most one singleton hit, and two such parents cannot cover four points. Invalid/self/forward inputs are explicitly masked. The ordinary wrapper assumes global correctness; distinct gate indices suffice, with no hidden distinct-point premise.

Approved FirstAnd.lean, SHA256 172d015fd5441ce6fef737441521d0a73a939cb0e003ba95e932ddf7e9d71ffe. Its reviewed AppendLine prefix and all eight new fragments match exactly. Two-stage constant cleanup deletes introduced nullary-AND constants, preserves original operation tags on surviving indices, and strictly reduces AND count when the original AND seed is deleted. Surgery preserves every other band output and every previously ordinary output, then rebuilds the selected line in three OR gates. normalize_or_sinks minimizes AND count among circuits preserving arbitrary W, retargets only outside W, and uses Sink to obtain NoReads and actual OR roots outside W. Final AND minimality and a gate-count tie-break are unnecessary for this Lean syntax. The successful log has30 harmless warnings; forbidden scans are empty. This is a normalization theorem, not the posted lower bound.

Approved Assembly.lean (SHA256 5d46fb234d8b16a684386fbd228cee2ff421815bb27ae70771df0ac3a4332141) and SmallFamily.lean (SHA256 a089d09a0187714c315e01a50bc485fe99f394ab992e6c28b149ea9773413054). Prefixes/extras match exactly; both successful logs have21 warnings and no errors. Appending a list costs exactly three gates per entry and preserves prior valid wires. deleted_or_pair masks original invalid reads and uses index20 as false only under the explicit seven-internal-gate bound. small_four_nonordinary proves that an ordinary output in a correct four-line residual of at most11 gates would yield at most38 gates and ten ordinary outputs after adding the other nine direct line outputs, contradicting the checked ten-ordinary theorem.

Mathematically approved the future guard: output true at its own line complement implies at least eight original AND gates. With line inputs fixed false, the output is exactly AND of the nine outside inputs, because every eight-point outside subset is a required negative band row. A true certificate selects all AND children and one true OR child; its distinct raw leaves number at most binary-AND count plus one, including DAG sharing, constants, unary/repeated inputs, and false invalid reads. All nine raw outside leaves are necessary. This certificate-count argument is not yet Lean formalized, and no active query changed.

## 2026-11-24 03:58:28 UTC — toolchain_setup: independent packing archive validation

Independently reconstructed all28 gates of special_status's four-line auxiliary packing example and reproduced18AND+10OR,48 selected false-AND checks,504 individual nondomination checks, all8192 globally bounded rows (32768 output checks), and867 band errors for each output. Also confirmed collective avoidance fails all12 ordered owner pairs. Archived six reviewed files under results/orch/research/packing with SHA256/byte manifest and explicit scope. The original author used inline Python; the archive supplies a new independent executable validator/reconstructor and its complete output. No commit, push, Lean build, or solver launched. This remains only an individual-nondomination/OR-packing counterexample, not a total-gate or posted-gap refutation.

## 2026-11-24 03:59:03 UTC — special_status: guarded AND-count encoder

Approved guarded_and_count.py for future integration, SHA256 20cb437f685fff9e3d9bb779f104d7c3ee9c420731b43eb14c9a9b6d0f8e8954. Its exact prefix-threshold recurrence handles signed literals, first-column cases, and diagonal cases correctly. With38 operation literals and13 own-complement guards it uses276 auxiliary variables and1,071 clauses. Each guard is not-own-complement OR threshold-eight. The complete4,098-case test source/log/JSON are consistent and check actual clauses, including exhaustive signed small inputs and randomized full38 guard cases. Future callers must supply original-AND and original-own-complement orientations. No active runner was changed; the mathematical certificate-count justification is reviewed but not yet Lean formalized.

## 2026-11-24 04:00:02 UTC — counterexample_search: future abnormal-value constraint

Independent mathematical review approves: if an output is true at its own line complement, fixing its four line inputs0 gives AND of all9 outside inputs, requiring at least8 original AND gates by true-certificate DAG branching count. This remains mathematical rather than a completed general Lean theorem. No running query changed.

The standalone future helper search/guarded_and_count.py was independently code-reviewed (SHA25620cb437f685fff9e3d9bb779f104d7c3ee9c420731b43eb14c9a9b6d0f8e8954). It builds exact signed prefix thresholds and guards each own-complement value by the global threshold8. For38 operation inputs it adds276 auxiliaryvariables and1071clauses including13guards. Independent unit propagation and complete small signed assignments, plus randomized38-input guard cases, passed4098cases. Full test source/log/JSON remain in scratch.

A future complementary search could require at least one own-complement positive and8ANDs, since normal-dual separately covers the all-own-complement-false class. This is a proposed partition only; no new solver was launched. Prepared preservation supplement search/orch-package-0400 is pending archive review.

## 2026-11-24 04:00:06 UTC — special_status: FourBound compiled review

Approved FourBound.lean, SHA256 482d21d9c9698b1ee938a60bcc9888498335c0567b692c06c0bae4110675884f. Assembly is exactly SmallFamily plus the unchanged target OneAnd geometry excerpt, reviewed FourPairs, and FourBoundExtra. The paid set P has at least27 generated gates and is disjoint from the four distinct exceptional output sinks Q. Adding the other three unread sinks to each cut changes neither its output nor essential set, so that set has size at most9. Clamp9 then supplies all four raw line coordinates; paid clamping preserves band correctness. Deleting P union Q leaves at most7 internal gates. Deleting P alone yields a correct four-output circuit of at most11 gates, so SmallFamily forces all four residual outputs globally nonordinary. The deleted-OR formulas hold on all assignments and transfer those functions to the checked FourPairs contradiction. All size, disjointness, validity, and ordinary-output premises are explicit; no hidden global upper bound is assumed. Complete successful log has22 warnings and no errors; syntax checks pass. This remains the conditional39 bound with nine ordinary outputs and four unread OR roots, pending the normalization/cardinality wrapper.

## 2026-11-24 04:00:32 UTC — fresh_proof

New distinct assignment: abnormal output (true at its own line complement) implies at least8 AND gates. Drafted AbnormalAnd.lean, not yet compiled. Its generic positive_components invariant tracks raw-variable component labels and true-wire certificates; an AND merges at most two labels and costs1, while a true OR selects one true parent and costs0. The cardinal inequality holds for every raw-variable subset, so the output component yields a true certificate contained in the supplied true input with size at most ANDcount+1, even with shared DAGs, repeated inputs, nullary gates, and invalid reads. At Z_line this certificate lies outside the line; if size<=8, Clamp.extend_eight gives a negative band row where monotonicity keeps the output true, a contradiction. Waiting for the serialized build slot after formal NineOrdinary.

## 2026-11-24T04:00:42.003880+00:00 — formal_baseline: four-exception bound compiled

FourBound.lean compiled exit0 (four-bound-build-002.log) and was independently approved. The full paid-clamp/deletion/FourPairs bridge gives39 gates for nine ordinary outputs plus four unread OR sinks. NineOrdinary.lean then compiled exit0 (nine-ordinary-build-002.log): it combines Fresh's checked minimum-AND normalization preserving exactly9 ordinary outputs, enumerates the four-line complement, and removes the OR/sink hypotheses. Thus nine_ordinary_bound proves39 whenever at least9 outputs are globally ordinary; five_exotic_outputs proves every <39 counterexample has at least5 nonordinary outputs. Both sources frozen, root/reviewer notified, and the single build slot released to lower_bound. NineOrdinary SHA256 7da93f71e9584f5a3f11b52b1943b0ecc70368ec8db2db466c5ac4cd8e52c20e. This remains a strengthened conditional lower bound, not the exact posted theorem.

## 2026-11-24 04:01:33 UTC — special_status: nine-ordinary bound and search supplement

Approved NineOrdinary.lean, SHA256 7da93f71e9584f5a3f11b52b1943b0ecc70368ec8db2db466c5ac4cd8e52c20e. It is exactly FourBound plus the reviewed FirstAnd suffix and the64-line wrapper. nine_ordinary_bound selects exactly nine ordinary outputs, preserves them through normalization, enumerates their four-line complement, and discharges FourBound's OR-root/sink assumptions. five_exotic_outputs correctly derives that any circuit with fewer than39 gates satisfying the posted band specification has at least five globally nonordinary outputs. Successful log has31 harmless warnings and no errors; format checks pass. The unrestricted posted statement remains unproved. Future five-literal flag constraints may use minimum5 via the previously checked extreme-value characterization; active queries were not changed.

Approved search/orch-package-0400 for metadata preservation: all11 files and16,104 bytes match manifest hashes and scratch copies; no unsafe paths, credential-pattern findings, or Python syntax errors. Independently re-evaluated its converted29-gate circuit on all8192 assignments:106,496 global-upper output checks and845 output checks on65 derivative rows pass; nine outputs each fail213 actual-band rows. Conversion and original0326 source hash match. The README correctly limits this to an auxiliary shortcut counterexample, and authorized strategy-interruption records correctly report UNKNOWN rather than UNSAT.

## 2026-11-24 04:02:16 UTC — lower_bound: MissingRawWitness compiled

MissingRawWitness.lean compiled exit0 on attempt2; success log lower-bound/missing-raw-build-002.log is complete. Source is frozen at scratch lower-bound/MissingRawWitness.lean, SHA256 0d0f456a691d97fd685cddcedccff30a49bbd1387099e08cd29a78707b64e1ae. The first attempt had only two Fin-index elaboration errors, now fixed. Main paid_pair_witnesses proves, for the SAME paid family P and support E of cardinality<=11 with a missing raw line coordinate, that rawSet has cardinality<=2 and that the nine outside points inject into paid essential coordinates. Each selected coordinate has an exact two-point singleton core consisting of its outside point and the owner/target line intersection. Hypotheses explicitly include monotonicity/support/correctness of F, raw-or-paid source classification, outside singleton witnesses for paid nodes, and owner D membership. Root was notified immediately, independent review requested, and the single build slot released to fresh_proof. This is a checked witness theorem, not yet the fixed-budget Clamp11 contradiction or a complete five-exception lower bound.

## 2026-11-24 04:02:26 UTC — counterexample_search: diagnostic preparation and preservation

The independently approved11-file search supplement was copied verbatim to results/orch/search/0400, including graph-five preparation, the future guarded threshold helper/tests, exact interruption/launch records, and the independently rechecked29gate derivative shortcut counterexample. Root has the manifest inventory; no child commit/push occurred.

At root's request, prepared but did not encode or launch search/cegis-collective-diagnostic.py, SHA256915e245b1e6be575c4449e4999494f61bfdd507a5be90eff89b12768fb193aad. It explicitly includes533dual rows:468six-point sets containing a line,13exact lines,52deleted-point triples. It omits all full-band-only guards and off-band additions. Independent review is pending. Any SAT model will be checked on533rows,65original derivative rows, all8192global-upper rows, and all3003actual-band rows; nonzero band errors are labeled auxiliary only. This is a proposed test of the collective-avoidance proof premises, not a full-gap query. All five current searches remain unchanged and unresolved.

## 2026-11-24T04:02:47.613184+00:00 — formal_baseline: five-output compiler draft

Read refreshed notes/index and followed root's next assignment. ResidualFamily.lean now drafts the generic append-complement induction step and small_five_nonordinary (<=14-gate five-output residual). FiveReduction.lean drafts general deleted-OR-pair extraction with dynamic false padding, the generic other-sink cut cardinal bound, and a conditional compiler reduction to five globally nonordinary OR pairs over<=9 internal gates. The crucial raw-line-in-essential-set premise remains explicit; lower_bound's fixed-P/E surcharge/Clamp11 proof will supply it. Both drafts are uncompiled and await the serialized slot after Fresh/toolchain. The full five-parent-incidence impossibility theorem remains separate and unproved.

## 2026-11-24 04:05:54 UTC — fresh_proof

AbnormalAnd.lean compiled exit0 with an empty abnormal-and-build-003.log. Source SHA256 8391004979ba1caf01a54eb04e9cdbde4b294a4dbf9fb8d1b128f4210ee6e53a. Root, reviewer, and the next build owner were notified immediately. PositiveCertificate.positive_components is a weighted component invariant charging only AND gates; small_positive_certificate gives a true support contained in any supplied true input, with cardinal at most the global AND count plus1. abnormal_and_lower proves that a band-correct output true at Global.Zof(Global.line w) requires at least8 AND gates. It handles shared DAGs, repeated/invalid reads, and nullary/unary gates. This is a checked structural restriction, not the39-gate theorem. The single build slot is released for ExcessSupport, then Clamp11.

## 2026-11-24 04:06:42 UTC — special_status: witness, certificate and diagnostic reviews

Approved MissingRawWitness.lean (SHA2560d0f456a691d97fd685cddcedccff30a49bbd1387099e08cd29a78707b64e1ae): under its explicit fixed P/E hypotheses, E cardinality at most11 and a missing raw line coordinate imply at most two raw coordinates and nine distinct paid pair-core witnesses. Positive seven-true and negative eight-outside rows, exact two-point core extraction, and injectivity are correct. Neither P nor E is changed. This remains the witness component of the five-exception argument, not the full bound.

Approved AbnormalAnd.lean (SHA2568391004979ba1caf01a54eb04e9cdbde4b294a4dbf9fb8d1b128f4210ee6e53a), empty successful log. Its generic positive-component invariant yields a certificate of cardinality at most ANDcount+1, and an output true at its own line complement therefore needs at least eight AND gates. Constants, unary gates, repeated operands and invalid reads are covered; format checks pass. The posted39-gate theorem remains absent.

Approved collective533 diagnostic preparation (SHA256915e245b1e6be575c4449e4999494f61bfdd507a5be90eff89b12768fb193aad). Actual diff removes all full-band-only guards and off-band additions. Dual first-AND roots, sink normalization, live padding, first-pair/order symmetry and four essential raw inputs hold on the explicit533-row domain. Scalar checks cover the diagnostic,65 derivative rows,8192 global-upper rows and3003 actual-band rows; only zero actual-band errors produce counterexample.json. Scope is a restricted auxiliary/global-upper problem, not an unrestricted gap encoding. No encoding or solver was launched for this review.

## 2026-11-24 04:06:48 UTC — toolchain_setup: ExcessSupport compiled

Scratch research2/ExcessSupport.lean compiled exit0 with an empty excess-support-build-002.log. Band correctness plus truth at the line-complement forces every support set to be all13 raw inputs; APIs expose support_univ, mem_support, support_card, and raw_essential for Cut.essential with13 independent raw sources. Binary circuits and valid prefixes computing such an output have at least12 gates. Conversely, support size at most12 forces falsity at the line-complement, and monotonicity then gives a global upper bound by the line OR. No finite enumeration was added. Source frozen and root/reviewer notified immediately; independent review is pending. Build slot released to lower_bound.

## 2026-11-24 04:07:09 UTC — counterexample_search: both replacement options reviewed and frozen

The533-row collective diagnostic passed independent review, including its restricted-domain AND-root/sink/live/order/first-pair normalizations. Source hash remains915e245b1e6be575c4449e4999494f61bfdd507a5be90eff89b12768fb193aad. It retains no full-band-only guards.

The strengthened graph-five source also passed independent review, SHA25671d9145fdc694745f1090acdec636a15efee5a27aed61edc103cbbe1c03ceb84. Checked NineOrdinary plus eight fixed direct ordinary outputs forces all five residual outputs nonordinary. Exact complement/singleton clauses enforce this, and exact syntactic support clauses require at least8points for each. Forty independent fixed-network CNF/scalar tests passed (20accepted,20rejected). Original graph-five remains frozen unchanged.

Both options now have immutable dependency snapshots/manifests under their unique scratch artifact directories, collective-diagnostic533/encoding-source and symbolic-graph-five-strong/encoding-source. Neither encoder nor solver has launched; root will decide at04:13. Current five long queries remain unchanged.

## 2026-11-24 04:07:21 UTC — special_status: strengthened template and excess support

Approved strengthened graph-five preparation, SHA25671d9145fdc694745f1090acdec636a15efee5a27aed61edc103cbbe1c03ceb84. Eight fixed ordinary outputs plus NineOrdinary force all five residual outputs nonordinary; the support theorem then gives at least eight raw support points. Added support clauses, exact own-complement/singleton evaluations (including prepared OR ports), and nonglobal disjunction signs are correct. Forty fixed-network propagation/scalar checks agree:20accepted and20rejected. Existing graph-template restrictions remain explicit; no encoding or solver launch occurred.

Approved ExcessSupport.lean, SHA2560db4fa811a95dc9866c8aedc5266638ce7d929a86a1ded46a7b990b587d7bc42, empty successful log. An abnormal own-complement value forces every outside raw point essential by comparison with the corresponding five-zero band row; the four line points are already necessary by band correctness. Thus every genuine support is all13 points, with no monotonicity assumption needed for this necessity. The cardinality and circuit/prefix lower bounds of12 correctly use the checked cut-component support bound. Monotonicity is added explicitly only to derive the global upper bound from a false own-complement value. Format checks pass; this remains a necessary-condition component, not the full39 theorem.

## 2026-11-24 04:07:45 UTC — special_status: upstream status refresh

Fully paginated read-only GitHub searches found zero PR titles matching exact L-meta-1024 or broader1024, zero corresponding commit-message matches, and zero default-branch commits touching lean/PEqualNP/Outside/L_meta_1024.lean. Structured JSON shapes, complete total counts and incomplete_results were checked; all five calls exited0 with empty stderr. Full stdout/stderr/status files are under scratch status-review-0408. These checks found no accepted proof/refutation; no lease or repository state was changed.

## 2026-11-24 04:08:08 UTC — special_status: replacement-query archive review

Approved search/orch-package-0410 for metadata preservation: all8 manifest entries and23,795bytes match hashes and scratch originals; both frozen dependency manifests match actual archived0326/0349 sources byte-for-byte. Safe paths, Python syntax and credential-pattern checks pass. README correctly distinguishes prepared/no-result state, the restricted K4-minus-edge template, and the auxiliary533-row/global-upper diagnostic. No complete-gap result is claimed.

2026-11-24 04:08:14 UTC — counterexample_search: the independently approved8-file preparation supplement was copied verbatim to results/orch/search/0410. Root can stage its manifest-listed paths plus manifest.json. No child commit/push. All five current queries remain unresolved; no replacement launched yet.

## 2026-11-24T04:08:24.873195+00:00 — formal_baseline: five-parent rank diagnostics

Short random diagnostics sampled connected five-edge parent graphs, using four ordered high vertices and up to five distinct low vertices, with repeated actual low wires represented by the same vertex. For vertex v, required T_v is the union of L\M over an incident output edge(v,u,L) and every other output edge at u carrying M. Making every T_v a raw-variable clique gives a necessary component rank. No survivor occurred in169,152 connected samples against the global bound9 (prefix bounds were unnecessary). This is empirical support only, not a finite theorem.

Disconnected2+3 shapes do survive all prefix bounds: edges[(2,4),(3,4),(0,8),(1,8),(3,5)], lineIds[8,4,2,12,11], required masks[2088,4353,2816,161,49,6146,0,0,0], ranks[4,6,7,8,9] at capacities[5,6,7,8,9]. Ten such survivors appeared among453 samples. No Boolean functions or band-correct circuit were constructed; this only shows the necessary rank constraints are insufficient. Sources and complete JSON/logs are baseline/five_rank*_diagnostic.py and five-rank-*-diagnostic.* in scratch. Fresh/root/lower were informed.

Tree saturation alone also cannot force ordinary behavior: OR of three line inputs, ORed with (fourth line input AND OR of four foreign inputs), is a7-gate read-once nonordinary output matching the band. The missed assignments have at least7false bits. Additional multi-output constraints are required.

## 2026-11-24 04:09:27 UTC — lower_bound: fixed-budget Clamp11 compiled

Clamp11.lean compiled exit0 on attempt2, with an empty complete success log lower-bound/clamp11-build-002.log. Frozen source SHA256 153c44a359d4d618daa2327c7d375404a1629c61cb04b6f2a5cb5e5f45322b0b; the added fragment is lower-bound/Clamp11Extra.txt, following unchanged reviewed PairSurcharge and MissingRawWitness prefixes. Main missing_raw_impossible and raw_line_members assume eight globally ordinary owner lines, target outside that family, P equal to their full charge-family union, the SAME E/P satisfying card E + card P <=35, and explicit cut-function monotonicity/support/band-correctness/source-classification hypotheses. The proof obtains P>=24/E<=11, nine injective paid pair-core witnesses, a repeated owner, surcharge P>=25/E<=10, and a second missing raw point whose six-zero separating row kills both owner witnesses. The eight-positive-frontier contradiction proves every raw target-line coordinate lies in E. Root and reviewer were notified immediately; the single build slot is released to formal_baseline. This completes the paid-source tightening, not the remaining five-output parent-incidence obstruction or the posted theorem.

## 2026-11-24 04:10:22 UTC — counterexample_search: next replan snapshot

- fanout0: solver20167 stateR; RUNNING elapsed 2884 freeGiB 12.46 proofMiB 156.5; events=[].
- fanout1: solver20169 stateR; RUNNING elapsed 2884 freeGiB 12.46 proofMiB 152.8; events=[].
- fanout2: solver20171 stateR; RUNNING elapsed 2884 freeGiB 12.46 proofMiB 154.5; events=[].
- normal: solver20458 stateR; RUNNING elapsed 2829 freeGiB 12.46 proofMiB 65.8; events=[].
- ORfull: solver24948 stateR; RUNNING elapsed 1272 freeGiB 12.46 proofMiB 22.8; events=[].

Cgroup current=13.37GiB/16GiB, anonymous=4.35GiB; diskfree=12.45GiB. OOM counters unchanged. Both reviewed, snapshotted replacement options are ready (strong graph-five and diagnostic533); neither has launched. Root owns authorization, fresh renewal, and memory-slot sequencing.

## 2026-11-24 04:13:12 UTC — special_status: Clamp11 approval and replan assessment

Approved Clamp11.lean (SHA256153c44a359d4d618daa2327c7d375404a1629c61cb04b6f2a5cb5e5f45322b0b),710lines, empty successful log. Prior reviewed PairSurcharge and MissingRawWitness bodies are exact unchanged substrings; new suffix exactly matches Clamp11Extra. The SAME P/E are retained through P>=24/E<=11, nine paid witnesses, owner collision, shared-core surcharge P>=25/E<=10, and the second missing raw point. Its seven-true separating row kills the two distinct owner coordinates, yielding the checked eight-positive-frontier contradiction. Assumptions are explicit; only the permitted heartbeat limit is added.

Replan assessment: the k5 paid-source bridge is now checked. The remaining k5 obstruction is complete parent-incidence coverage and impossibility for five nonordinary, globally bounded, band-correct OR pairs over at most nine internal gates. The K4-minus-edge template is not all cases. Completing this step would force at least six nonordinary outputs in any circuit below39 gates, still short of the unrestricted theorem. The separate collective-avoidance/cycle-space route still lacks its rank/uncrossing bridge; individual shared-gate bypass alone is known insufficient. Reviewed archives preserve these scopes accurately.

## 2026-11-24 04:13:40 UTC — special_status: residual and five-output compiler review

Approved ResidualFamily.lean (SHA256d39073702c89824659f8ca5f5f1b6000bd3cb7e7281c45818aa344a562c50d47) and FiveReduction.lean (SHA2565e2aa822520458324ae9387089af094cbf951157294335eb2454616f6e19bb6d). Each is exactly its reviewed prefix plus the named new suffix; successful logs contain31 harmless warnings and no errors. ResidualFamily correctly appends the complement family, preserves valid old outputs, and applies its explicit previous-bound premise; the five-output specialization uses NineOrdinary. FiveReduction correctly handles invalid/self/forward reads through dynamic false padding, bounds essential support after cutting other sinks, clamps paid sources, preserves OR roots, and deletes at least29 gates to leave at most9 internal gates. Its five residual OR-pair functions remain band-correct, globally bounded and globally nonordinary. Paid-family count/outside witnesses/disjointness and raw-line membership are still explicit hypotheses, pending the owner-family wrapper. Allowed heartbeat option only; no exact theorem claim.

## Replan 2 — 2026-11-24 04:14:35 UTC

Reviewed the shared notes and independent assessment.

- Completed since the previous review: unrestricted nine-ordinary bound (at least five nonordinary outputs in any smaller counterexample), general OR-sink normalization, fixed-set Clamp11, generic positive-certificate bound, abnormal-output eight-AND bound, and abnormal-output thirteen-input support. These are compiled partial results; exact statement remains open.
- formal_baseline will finish the unconditional eight-ordinary reduction to five nonordinary, globally bounded OR pairs over at most nine internal gates. fresh_proof handles all remaining five-parent incidence shapes, including disconnected cases and forest-saturation guards. lower_bound supports the connected-shape and fixed-budget lemmas. The five-output impossibility theorem is still missing.
- Keep the global normal-output route separate. Individual nondomination/OR packing and abstract pairwise rank conditions are insufficient. toolchain_setup is checking primary literature and actual gate/graph realization constraints; no global-to-band normalization may be assumed.
- Retire fanout case1 in favor of the reviewed 533-row diagnostic after the current Lean build batch; preserve the interrupted run completely. Keep fanout0, fanout2, normal-dual, and full OR-sink queries for now. Prepare a new disconnected2+3 parent-template search matching the proof obstruction, then independently review it before replacing fanout2. The already reviewed K4-minus-edge query remains unlaunched because that connected template is mathematically excluded by the new reduction plus rank counting.
- Keep one Lean build or large encoder admitted at a time. Root owns renewals and submission. Continue immediate reviewed preservation of successful sources and complete logs.
- Next review: 04:39 UTC. Approximate overall deadline remains07:28UTC.

## 2026-11-24 04:15:39 UTC — toolchain_setup: bounded primary-source research

Completed the requested bounded built-in-web literature check; no shell fetches or writes to external sites. Exact source URLs, read date2026-11-24, short quotes, verified claims, and proposed applications are in scratch research2/literature_2026-11-24.md. Read primary papers by Sokolov, Jukna, Wegener, and Grigor'ev. No ready theorem closes the normal-output selected-DAG inequality. Proposed next restricted case is global minimum-formal-degree pruning under squarefree four-leaf certificates; arbitrary repeated certificates remain unresolved. Normal-output scope is explicit.
