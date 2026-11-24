# S08 integration and delivery review

Initial review: 2026-11-24T03:25:47.137400+00:00. Verdict: **PASS_FOR_RESEARCH_CHECKPOINT_ONLY** for the four exact snapshots below. This is an independent local artifact review, not proof acceptance or permission to submit the posted gap.

| Reviewed path | SHA-256 |
|---|---|
| `results/orch/agents.json` | `be54fe73cd29e456407d9a941a369c74d7f6bff6ae95b870c364f6f11f3d1f4a` |
| `results/orch/NOTES.md` | `1c7a3ecc19b64cee046d7fb120d8a2964d0cb298ec8aa33082c7f903d6dccacd` |
| `results/orch/TIMELINE.md` | `f4a4bcc183fecde040634805ab7e998c80f5110ad28ad0478b2589d58b419d52` |
| `results/orch/lemmas/INDEX.md` | `1c192867b54f3f14e818d59c26a0e4383759f8b72e16a24593028fc707b143d7` |

Snapshot captured at 2026-11-24T03:24:56.803325+00:00; complete snapshot files, manifest and evidence log are in `/tmp/oec/pequalnp-pilot-18/orch/S08/`. A later NOTES append is outside these reviewed hashes. Re-review every added byte before claiming the new tip was reviewed. This report does not cover unrelated untracked reports or research files.

## Evidence and outcome

- Local HEAD is `8e0afb4ffd85b79f12c20cdabd4b16cc2ba26274` and the named file is 1,859 lines / 89,387 bytes, SHA-256 `f4bd1991b5602c241151fac9e8a2279df1a4ae9b6f4b6aa44782a27c0f4d6ea5`. Both agree with NOTES. No tracked diff was present at initial capture. Remote pushed state and absence of a remote PR are reported by the orchestrator, not independently queried.
- `ancestor-support-checkpoint-review.json` binds the current source hash to the existing complete named-module build log, which ends `Build completed successfully (5109 jobs).` Its stderr is empty. Existing baseline, concrete-bound, matching-lift and ancestry audits name only `propext`, `Classical.choice`, `Quot.sound` (or subsets). No build or axiom audit was rerun by S08.
- The source proves a size-22 baseline with exact target behavior, a size-at-least-22 bound under the explicit clean binary AND/OR hypotheses, and the listed helper results. It has no theorem named exactly `PEqualNP.Outside.L_meta_1342`. The reports correctly distinguish these partial results from the posted at-most-21 existential and correctly record the posted checker as NOT RUN.
- `agents.json` lists exactly six active strategies S01/S02/S03/S04/S06/S08 and two backlog strategies S05/S07. This agrees with the user's platform-limit correction and the appended allocation note/timeline. No agent-manager tool is exposed here for a separate runtime census. The initial eight-route roster remains a plan; the later allocation entry resolves its status.
- No credential indicators were found in the four complete setup snapshots. Scan categories and zero findings are recorded in the manifest. Lease identifiers, credential files and environment variables were not read. Public worker IDs are not authentication credentials.
- The initial setup is suitable to preserve on the authorized research branch, with the limitations and minor corrections below. It is not a single-file proof PR.

## Findings for the orchestrator

1. `INDEX.md` says “Current checked source” without immediately saying “partial”. Its later caveat and NOTES correctly resolve this, but “Current compiled partial source; posted checker NOT RUN” would remove ambiguity for readers of the index alone.
2. The named source currently has two helper namespace blocks. CONTRIBUTING requires one permitted module/auxiliary helper block and the full-name final theorem last. This is a known final-integration blocker, not a blocker for retaining partial research history.
3. Path prefixes such as `scratch/lean-4.36.0-linux/bin` mean the scratch-root alias `/tmp/oec/pequalnp-pilot-18/lean-4.36.0-linux/bin`, not a literal extra `scratch` directory. Shared lock paths must be the absolute `/tmp/oec/pequalnp-pilot-18/orch-notes.lock` and `/tmp/oec/pequalnp-pilot-18/orch-lean.lock`. S08 uses the former for append-only notes.
4. Runtime status, lease events and remote push/PR status are attributed to the orchestrator's records; this review makes no fresh network verification. Reviews of future checkpoints must refresh time-sensitive statuses and bind their new hashes.
5. Newly created strategy reports and later note appends require the next checkpoint review; this initial verdict cannot cover bytes that did not exist at its capture time.

## Repeatable integration review

A repeatable JSON manifest and static capture script are available in `/tmp/oec/pequalnp-pilot-18/orch/S08/`: `review-manifest-template.json`, `capture_review.py`, and `static_guard.mjs`. The script writes only a new S08 review directory and makes read-only git calls with explicit cwd. It runs the existing repository static guard; it never builds Lean or runs the posted checker. A completed capture is not a passing review by itself.

Example capture, run with cwd `/workspace/pequalnp-proofs`:

```sh
python3 /tmp/oec/pequalnp-pilot-18/orch/S08/capture_review.py \
  --label checkpoint_unique_label \
  --base 8e0afb4ffd85b79f12c20cdabd4b16cc2ba26274 \
  --artifact results/orch/agents.json \
  --artifact results/orch/NOTES.md \
  --artifact results/orch/TIMELINE.md \
  --artifact results/orch/lemmas/INDEX.md
```

Add each proposed report and each full build/audit/checker log explicitly with another `--artifact`. Add `--pr-base` with the full authoritative base commit for a committed delivery-tip review. The script excludes credential/lease/store paths and never prints matching secret values. Credential scanning uses signatures and cannot prove that arbitrary unknown secrets are absent. Review all explicit files in full, including untracked files, which git diffs omit. Results artifacts and prose are not subject to the Lean-only forbidden-text rules.

| Gate | Required evidence and interpretation |
|---|---|
| Scope | State `partial_checkpoint` or `final_submission`. A research checkpoint may contain result files. The final proof PR must add exactly the named Lean file relative to its authoritative base. |
| Exact statement | Save the original statement bytes and SHA-256 without rewriting. Require the declaration `PEqualNP.Outside.L_meta_1342` with exactly the posted type for `check`, or exactly its negation for a declared `refute` run. No added clean/binary normalization assumption, weakened target, changed edge list, or 22-gate substitute. Textual agreement is preliminary; the checker elaborates independently and checks the proof type. |
| One Lean file | Confirm the integration changes no other Lean file, pins, definitions, checker, workflow or configuration. Full tracked/untracked inventory and source hash must be recorded. A final PR must show precisely `A lean/PEqualNP/Outside/L_meta_1342.lean`, no modifications/deletions/renames/second file. |
| Bytes and mode | UTF-8 regular text, no NUL/control/invisible characters, at most 524288 bytes, not a symlink or executable; committed Git mode `100644`. Record byte count and hash. |
| Imports | Plain top import lines only; Mathlib/modules and the allowed project root `PEqualNP.Defs`; no later occurrence of the word `import`, even in comments. Scratch Outside-module imports must be removed during integration. Never satisfy module-system build warnings by adding a prohibited leading `module` command. |
| Forbidden text | Use the pinned `.github/scripts/outside-guard.mjs` raw scan, including comments, rather than an incomplete ad hoc word list. It checks `_root_`, quoted strings, `sorry`/`admit`, new axioms, native mechanisms, executable/metaprogramming commands and namespaces, quotation escapes, and other prohibited markers. Record the guard hash and complete diagnostics. |
| Attributes and options | Only the four numeric scoped limits: `maxRecDepth`, `maxHeartbeats`, `synthInstance.maxSize`, `synthInstance.maxHeartbeats`, on separate `set_option ... in` lines directly above the declaration served. Only `@[simp]` / `@[local simp]` pass the attribute filter; prefer no exported simp helpers or instances. Check these constraints manually as well as with the guard. |
| Namespace and layout | Helpers stay in the permitted module/auxiliary namespace; scope delimiters at column zero, named `end`, fully qualified final theorem last. Follow CONTRIBUTING's single-block wording. The implementation actually permits repeated own-prefixed blocks, so do not misreport this documentation issue as an observed automated rejection. Avoid custom datatypes and instances, which trigger human review even when the current guard permits them. |
| Integration | Compare full source to the reviewed base and the compiled fragment; explain every changed byte and every removed scratch harness line. Record source hash before/after, exact named-file diff hash, fragment hash, exact new statements and scope/hypothesis review. Any later source edit invalidates the old hash binding. |
| Builds | Keep standalone-fragment compilation, integrated named-module build, and posted checker as three separate statuses. Record argv, explicit cwd, source hash before/after, exit code, timestamps and complete stdout/stderr hashes. Empty logs alone do not establish exit zero. Do not rerun a successful named build unchanged merely for this review. |
| Axioms | Audit every new externally useful helper and the final theorem transitively, not just direct textual axiom declarations. Preserve an external audit harness and full `#print axioms` logs; never place that command in the final proof file. Every dependency must be within `propext`, `Classical.choice`, `Quot.sound`. Bind audit source and compiled module to the reviewed source hash. |
| Posted checker | Keep NOT RUN until the exact final theorem exists. Then preserve the complete `node tools/check-lean.mjs <named-file> <original-statement-file> check` (or `refute`) output, exit status and complete MANIFEST. A source build, static PASS, axiom list, SAT verdict or advisory PR result is not authoritative acceptance. A checker fault/timeout is not rejection, acceptance or mathematical exhaustion. |
| Lean coordination | Every memory-heavy compile/audit/checker run must hold `fcntl.flock` on `/tmp/oec/pequalnp-pilot-18/orch-lean.lock` for its full subprocess lifetime. Use the pinned toolchain and explicit `lean/` cwd; no `lake update`, no Mathlib source rebuild. Review does not launch redundant builds. |
| Delivery and preservation | Orchestrator alone commits/pushes/submits. Retain the research branch tip and all results in its history. Build a submission tip whose PR comparison to the authoritative base contains only the added named file; a clean delivery branch can preserve the research branch unchanged. If using a cleanup tip on the same branch, ensure all research artifacts disappear from the PR diff while prior commits remain reachable. Do not erase research history. Verify the final committed blob equals the checked SHA-256, mode and size; review any changed base and record the exact local/remote tip. |
| Evidence freshness | Hash all delivered logs and reports, including untracked additions. Never silently upgrade a snapshot verdict to cover later note appends or report edits. Review the final PR comparison, not merely the last commit, staged diff, or working tree. Only the orchestrator refreshes gap/lease and remote status. |

The capture script has been exercised on the 2,000-line integration with all four setup files and current build records. Its `boundary-static-capture/manifest.json` SHA-256 is `b81a30992488c1ba6550ed88eda4bd72956f6c5212480524bc9cdd3ec14b2fa5`; no captured file changed during the run and no credential indicators were found. This capture records the expected missing-final-theorem guard result rather than treating it as full format acceptance.

## Post-snapshot integration review

At 03:27 UTC, independently reviewed the requested 2,000-line source SHA-256 `f872b394be5f8fdcfd20fe735e26856aebdcc88b17a305f35a49a85d8a8fcfdb` against `8e0afb4ffd85b79f12c20cdabd4b16cc2ba26274`. Named-file diff SHA-256 is `cb1c8c4e974dfbc722e46b3ab478b57c1aab9d69ad9b59c736d44c3c99f82839`. Verdict: **PASS_FORMAT_AND_EXACT_INTEGRATION_FOR_PARTIAL_CHECKPOINT**. Full manifest `orch/S08/boundary-integration-review.json` has SHA-256 `31396590b44a78eb9fbb2afa3782ff3d36b109419904ccc54b6cc3249d87ac63`.

Every prior source byte is preserved except moving the final auxiliary `end` after the new declarations. The insertion is byte-identical to fragment SHA-256 `cfc466912c36549c3d1538d646ae9f1a5748e4e2f95dd8a70487d997cf957021` after removing its scratch import, outer namespace wrapper and redundant `open` harness line. Imports are unchanged. The actual repository plain/import guard passes; there are no new global instances, datatypes or attributes. The own-namespace/final-theorem guard rejects the missing module-named final theorem as expected. The source still contains two permitted helper blocks; consolidation is the stricter documented final-file requirement, not a failure raised by this guard.

`boundary-lean/seventh-result.json` binds the standalone exit zero to the fragment hash. The two complete seventh logs are empty, each SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. `boundary-lean/named-result.json` reports exit zero; complete named stdout SHA-256 `fe21362cf92b26e91364449fe9fb99f18dd2fe89214aa5d1b9b5377f1fa07aa2` ends with successful build, and stderr is empty. The named result JSON omits a source hash; its binding is supplied by the orchestrator's explicit hash confirmation, integration record and this exact-body review. S03's independent proof review subsequently passed at 03:28. Main's new transitive axiom audit was still pending when this review was issued.

The precise new result is `target_boundary_spec`: for a `Monotone2` circuit, acceptance of the 16 target edge pairs and rejection of the 24 listed maximal independent inputs implies exact target behavior on every input. It adds no circuit witness or gate-count result. The exact statement is preserved in `orch/S08/boundary-exact-statement.txt` and S03's report. The initial INDEX's unsuccessful-fragment sentence became stale when the PASS record appeared at 03:25:15, after the initial snapshot. Refresh it before the next checkpoint. The initial 1,859-line source claim is likewise historical, not a description of the later integration.

Independent bounded Python enumeration also confirms every graph fact listed in INDEX: 16 edges, 125 independent/1923 positive inputs, the exact 24 masks (22 of size four and two of size three), minimum cover seven, no C4 and only the identity automorphism. Complete results are in `orch/S08/independent-graph-check.json`. These finite script checks are supplementary evidence, not new Lean results.

Next direction after reading the new S02/S03/S06 reports: preserve the compiled boundary partial after the main audit, update validation and INDEX truthfully, and use S03's concrete 40-row evaluation/canonical posted-predicate bridge for any candidate. Continue treating S02 candidate searches and S06 redundant-clause preprocessing as separate research evidence; none establishes the posted theorem. Their later report revisions need their own hash-bound checkpoint review.

No named proof edits, git writes, network writes, desk calls, solver runs or Lean builds were made by S08.

## Audit follow-up at 2026-11-24T03:30:26.377473+00:00

The main audit harness and all five expected outputs are now present. `boundary_cover_bool` has no axioms; `target_negative_cover`, `target_negative_independent`, `circuit_eval_mono`, and `target_boundary_spec` depend only on the three allowed axioms. Complete stdout SHA-256 `31003a47b97be1bb36067b33d2c0f6464d13bc4d3405c922bc15d02ad0938db7`, empty stderr SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`, audit-harness SHA-256 `cbfd379f5b8cd2bb860293e13773c8654566dc288d79ad3781cca261a8f95963`. Copies and metadata are retained under `orch/S08/`. The named source still matches `f872b394be5f8fdcfd20fe735e26856aebdcc88b17a305f35a49a85d8a8fcfdb`. No audit exit-status record was present at this observation, so S08 records the observed complete output rather than inventing process completion; main should preserve its actual exit status/source binding. No axiom content blocker was found.

At this observation INDEX still contains the obsolete “no successful fragment build yet” paragraph and NOTES still opens with the 1,859-line source hash. These were accurate in the initial snapshot but must be updated for the upcoming 2,000-line checkpoint. Later findings alone should not leave the opening current-status paragraph contradictory. TIMELINE should record the new compiled partial. Only the orchestrator edits those shared summaries.

## Checkpoint metadata clearance at 2026-11-24T03:31:16.960608+00:00

**PASS_FOR_COMPILED_PARTIAL_CHECKPOINT_PUSH.** Reviewed validation.txt, boundary-checkpoint.json and all eight listed copied logs/reviews/build/integration records. All sizes and hashes match, all copies equal their scratch sources, and the named source remains the reviewed 2,000-line hash. Main explicitly confirms the audit exited zero; the checkpoint now preserves that status and the harness hash. Partial-only/current-source/checker-NOT-RUN claims are accurate. No credential indicators or concurrent byte changes were found in the eleven scoped files. Full metadata review: `orch/S08/boundary-checkpoint-metadata/review.json`, SHA-256 `b936012bff7499fb7efe1d486b6a39bbb73af342c21771c584c33c27f08b2392`. Evolving orchestration files and unrelated research artifacts remain outside this clearance. No build was run.

## Independent S06 RUP review at 2026-11-24T03:34:59.966672+00:00

**PASS_FOR_EXACT_RUP_PACKAGES_AND_16_SCOPED_SUBCASES.** Full review `orch/S08/s06-rup-review/review.json`, SHA-256 `b437637e0b2a155e66b4d4f4261a8407bdb04e2a4327180592d9cef1f84a6937`. Replay driver `orch/S08/review_s06_rup.py`, SHA-256 `8b4760faf8891084d85be9f78976cbd673b796b6988d8b73cadc6234ca872cdc`. All input snapshots and full checker diagnostics are retained below `orch/S08/s06-rup-review/`; driver stdout/stderr are retained beside it. This work does not delay the already-cleared boundary checkpoint.

| Object | Exact SHA-256 | Independently verified scope |
|---|---|---|
| Parent CNF | `38d93ec59a86378a8434b232d19b2b53e8cbc3c715e81432ee94db59ca6ace08` | 11,968 variables / 114,566 clauses |
| First RUP proof | `dad278648ab57d19bc4af884261eba40c0931c6f234ceb6485f998c50cf3991b` | 569 redundant additions; checker exit 0 / `s VALID` |
| First augmented CNF | `459714296e1b81ca589d3ad1f020606812e4cb29a1ad0cdf3273a94c0b702f0c` | Exact parent plus those additions; 115,135 clauses |
| Strong RUP proof | `b26cafe87463ab3b6a806275f67bbf146e2945fbf5e637aa3775a2c2f6fca992` | 994 redundant additions; checker exit 0 / `s VALID` |
| Strong augmented CNF | `7eed87fcaa73613b91fecd7a56ede475679860012323ca5a3a37b2868cd5c1a4` | Exact parent plus those additions; 115,560 clauses |
| Scoped subcase proof | `5965d6717c76455b052dc1e6309d52c6c8253dc53e9d47a43f4270c07c8b39e4` | Strong proof followed by an empty clause, valid only with each recorded assumption |

Reviewed `probe.cpp`, the initial package builder, second-level builder and subcase builder. Reconstructed every first-level and second-level input from the original parent bytes, the preceding proof, and only the declared assumptions. Verified every lifted clause negates exactly those assumptions, every source/manifest/log hash, and the unchanged variable numbering. The first package comprises 195 root units and 374 lifted clauses; the stronger package adds 425 more clauses. No global empty clause occurs in either consequence proof. The correctness of these conditional clauses does not require trusting that the four operation cubes are exhaustive.

Ran 19 sequential bounded checker replays on S08-owned snapshots: two consequence packages returned `s VALID`, all sixteen original-parent-plus-one-unit subcases returned `s VERIFIED UNSAT`, and the same empty-clause proof on the original parent without an assumption was rejected with exit 1. Aggregate checker wall time was 1.78 seconds. Each subprocess had a 1 GiB address-space limit, five CPU seconds and a six-second supervisor timeout. No solver, Lean compiler, posted checker or active worker was launched or altered.

The sixteen exact assumptions are `rights[g][1] = true` for zero-based gates `g = 1..16`, mapped by the original metadata to literals `151, 289, 431, 577, 727, 881, 1039, 1201, 1367, 1537, 1711, 1889, 2071, 2257, 2447, 2641`. Every subcase CNF equals the original parent plus exactly its one literal. They form overlapping restricted subcases, not an exhaustive partition. The negative control proves that this submitted proof does not establish a contradiction without those assumptions; it does not prove that the parent is satisfiable. No assigned-shard/global UNSAT, Lean proof, or runtime speedup is claimed.

The checker binary SHA-256 `e6894b5b74ac2c09b494344f397ec5111547aaa782cdb399f1a8b6835ecef84b` equals the previously reviewed binary, and all 34 recorded checker source hashes still match. No generator rebuild was necessary: the generated consequences were checked directly against the exact original CNF. All 166 captured inputs stayed unchanged during review, and the complete snapshot credential-indicator scan found zero hits.

Packaging note: the original `package.json` records generation outputs but does not itself preserve checker completion status/command/log hashes. Archive the full independent review and replay logs with the package so that `s VALID` has an explicit exit-zero/argv/source binding. Future UNSAT checks on the augmented CNFs must retain this preprocessing proof chain; checking an augmented formula alone does not document its relation to the original parent. SAT candidates must still pass the original-CNF and all-input validation and receive a Lean proof.

Later `suffix-fanin` proofs, the new short CDCL control and any files outside the recorded hashes are not included in this verdict. After reading the latest shared findings, the next useful handoff is to preserve these stable proof packages and their exact replay evidence. Review S01's existence normalization separately from implied RUP clauses; no unreviewed J18 unit was included in these checked packages.

## Final S06 package and proposed sweep review at 2026-11-24T03:37:52.850640+00:00

**PASS_FINAL_RUP_EXACT_AAAA_PARTITION_DIRECT_PROOF_AND_PROPOSED_COMMANDS.** Full record: `orch/S08/s06-final-review/review.json`, SHA-256 `6a5daee23ed457fecf8c280e23dea6a42bfbd4eb98eb3f0fb9ff012ac748efad`. Replay source: `orch/S08/review_s06_final.py`, SHA-256 `870f91031007af071f4a04689ea52d25bcd14d26c61dd76b9cb442a4cabd5b11`. Full snapshots, before/after input hashes, command arrays, exits and complete stdout/stderr are retained in that review directory. All 399 entries of S06's final artifact manifest matched; no reviewed input changed during the run.

The final proof has 3,692 additions / 119,955 bytes, SHA-256 `f319ae4b04ce7c6910389dc7f60ed61c353417192c47a44def9b35cc784683c8`; augmented CNF SHA-256 `2d20f5647012ed07af999643828cd3ac7916d4f61417d966579a49862b05e879` has 118,258 clauses. Every suffix-fanin local CNF, incremental proof prefix and negated-assumption lift was independently reconstructed byte for byte. A fresh RUP-only replay against the original parent returns `s VALID`, preserving satisfiability without asserting UNSAT.

The exact AAAA partition manifest SHA-256 is `571bbb81339f2538aaeb9c013a0117db7d526ac485ed44af0f5cd335356d5213`. All 18 case CNFs equal original clauses plus the checked consequences plus exactly the four positive operation literals and one right17 selector. Their full metadata objects preserve all original decoding arrays and add only the declared hash/count/cube fields. Twelve excluded sources 0..11 and the coverage statement were independently replayed by composing the entire preprocessing proof and empty-clause proof against the original CNF plus each exact assumption set. Thus the review checks original-parent provenance, not just a contradiction in an unexplained augmented input.

Disjointness was checked from the actual CNF: its 30-selector positive clause is present, and traversing binary implications from each selector reaches the negation of every other selector. The implementation uses a sequential at-most-one encoding, so the pairwise exclusions are not literal binary pair clauses; this review checks the implication paths rather than assuming such clauses exist. Sources 12..29 therefore cover the AAAA case and are mutually exclusive.

The retained direct source-13 proof is 1,243,473 bytes, SHA-256 `3e15055185b8fa99377cbda2b77ca7a5631cb22886665f7c23e461d2ed1920fe`. Its input is precisely original CNF plus `[2807,3072,3341,3614,2851]`; it includes no preprocessing or S01 normalization premise. Independently replayed it using DSR `--forward` and obtained exit zero / `s VERIFIED UNSAT`. This direct DRAT proof is separate from the RUP-only consequence proof. The same final empty-clause claim without a cube still rejects. Sixteen bounded checker replays took 3.92 seconds total; S08 ran no solver or Lean process.

Every proposed runner command was checked against the exact case hash, unchanged reviewed runner `535ff6e32a68a31eefa1545f031483d0e9b73acd79066d1bbb2a2f42c86685bb`, solver `2a0137451efde370d67b88aec26f1e902870f095b1204b07049a103bc6bbd647`, and checker `e6894b5b74ac2c09b494344f397ec5111547aaa782cdb399f1a8b6835ecef84b`. The command uses CaDiCaL `--unsat`, a 20-second online-runner cap, 1024/2048 MiB solver/checker address-space caps, and only the existing abort-sentinel path (its contents were not read). The 17-case proposed order is `14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,12`, excluding already-certified source13. At concurrency one this requests at most 340 solver-search wall seconds plus startup/checking overhead. This is a reviewed launch recipe, not a launch by S08 or a predicted runtime. Only the orchestrator schedules it after the current annealers end.

One minor metadata defect: `bounded_control.py` writes `started_utc` after the solver returns, so that field is an end observation mislabeled as a start. The monotonic measured 0.2206-second duration and certificate hashes/verdicts remain usable. Correct or annotate the timestamp label when archiving; it does not block the proof package or exact sweep.

Even complete success on the seventeen remaining cubes would establish only AAAA exhaustion under the reviewed original-CNF interpretation. AOAA, AAOA, AAAO, other shapes and the global posted Lean theorem remain separate. Retain the final preprocessing proof and exact original-parent mapping with every subsequent online result. A timeout remains inconclusive.
