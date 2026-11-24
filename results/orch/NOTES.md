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
