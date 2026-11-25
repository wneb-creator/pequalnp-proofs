# Research artifact review

Reviewed 2026-11-25T06:28:55.827565+00:00 by repo_review, read-only except this note. Coordinated stable-file lists with circuit_search, lower_bound and constructive. No desk calls, builds, solver runs, git mutations, installs or credential reads.

## Verdict and claims

PASS for preservation of the identified research artifacts, provided the final snapshot records capture times and hashes. No credential-shaped values, environment dumps or credential-reading commands were found in the inspected sources/configuration files. Current tracked modifications are restricted to results/orch research notes; no unexpected core source/config edits were present.

The factor result is a checked-by-enumeration36-gate candidate with14 degree-two shadow edges, not a26-gate solution. The factor-pair enumeration is exhaustive only over maximal compatible pairs, not all circuits or minimum circuit costs. Scoring and MILP objective are heuristics. UNKNOWN solver results and fixed-candidate UNSAT smoke outcomes must not be reported as a general lower bound. The strategy notes currently preserve these distinctions correctly.

## Factor snapshot

Stable programs in job scratch constructive/: factor_partition.py, factor_compatibility.py, factor_orbits.py, factor_score.py, factor_milp.py. These use same-directory imports and must remain together.

Preserve complete JSON/log pairs: compatible-pairs; factor-orbits; factor-score-smoke; factor-milp-run1. The initial factor-smoke pair is historical: its log used an earlier scorer revision and is not claimed byte-reproducible from the final source.

Reproduction sequence, with <dir> replaced by the saved directory:

- python3 <dir>/factor_compatibility.py --seconds 10 --output <dir>/compatible-pairs.json
- python3 <dir>/factor_orbits.py --input <dir>/compatible-pairs.json --output <dir>/factor-orbits.json
- python3 <dir>/factor_score.py --input <dir>/factor-orbits.json --output <dir>/factor-score-smoke.json --seconds 5 --passes 1
- python3 <dir>/factor_milp.py --input <dir>/factor-orbits.json --output <dir>/factor-milp-run1.json --seconds 90 --per-case 1

Capture complete stdout/stderr separately for each command. Owner reports Python3.12.14, NumPy2.3.5 and SciPy1.17.0 were preinstalled; no installation or network fetch occurred. Only factor_milp needs NumPy/SciPy. Enumeration counts should reproduce; timing, set iteration and MILP heuristics can alter retained scoring candidates.

Confirmed summary consistency:5033 maximal unordered pairs,168 side-preserving automorphisms,45orbits; first scoring pass45representatives; MILP109cases in90.169seconds, best36gates/14shadow edges. These agree between notes, JSON and logs.

## Shadow-three snapshot

Stable source/configuration dependencies: circuit-search/synthesize.py, phased.cpp, phases.py, shadow_smoke.py, near26.json, near26-shadow3.phases, solver-metadata.json; sat-review/verified_symmetry.json and verify_rows_symmetry.py are required by phase generation and must also be preserved.

shadow3-26.cnf and its mapping are regenerated with synthesize.py --gates 26 --dirty-and --shadow-missing 3. Saved encoding log reports11073variables,306744clauses,58rows. Preserve the exact generated files or their hashes plus exact generation command/source hash. Use the shadow-specific phase file; the earlier near26.phases belongs to a different encoding.

The separate active guided run uses live-dirty26.cnf, near26.phases and guided26-run.json. It adds liveness and dirty-AND restrictions. Do not conflate it with either the shadow-three run or unrestricted-output CEGIS. Completed shadow smoke logs show a fixed27gate star excluded and a fixed28gate absorbed circuit accepted and truth-table checked; neither is a general SAT/UNSAT claim.

## Hot-hint CEGIS snapshot

Stable sources: lower-bound/cegis-hints.cpp, cegis-hints.hpp, cegis-warm.hpp, prepare_cegis.py, biclique_warm.py. Preserve both included headers. Preserve cegis26.meta and the exact base CNF or source/hashes/commands required to regenerate it. Base preparation removes only the validated58output-unit clauses from heawood26.cnf and its mapping. The general encoder reproduction command is synthesize.py --gates 26 --no-liveness, matching the recorded original hash.

Preserve biclique30.json and biclique30.hint as stable hint inputs. Current cegis26-hints.hint, status, run log and iteration/warm models are LIVE: copy them with an explicit snapshot timestamp, and distinguish incomplete log prefixes from completed logs. Source files are frozen according to lower_bound. Smoke logs hint-accept, hint-fallback, hint-invalid, biclique30-fixed, final-accept and final-fallback are complete.

The driver validates hint format, gate count, backward references and active rows. Hint or warm UNSAT probes explicitly fall back to unconstrained solving; they do not become a false general UNSAT result. It uses bounded solving slices and reports UNKNOWN on exhaustion. Current owner report is31active rows and UNKNOWN; last SAT candidate satisfied30rows and retained false positives. General research encoding includes canonical65prefixes, adjacent independent order and boundary nontriviality, with tail copies allowed; it has no liveness/domination/dirty-AND/shadow restriction.

## Official checker capacity

Current filesystem:7.9GiB total,1.2GiB free. Toolchain3.1GiB, project .lake2.6GiB, Mathlib package2.2GiB. Compressed local Mathlib cache is already only136KiB, so removing archives cannot materially help.

The unchanged official local checker loads all Mathlib, including private/server module data and IR; focused dependencies are insufficient. No supported cache artifact-filter option exists. I found no realistic route to full checker readiness within this volume while preserving required artifacts. More local storage, a larger environment, or the unchanged official checker on a sufficiently provisioned runner is the credible route once a complete candidate exists. Do not fabricate a root Mathlib.olean, remove required runtime files, alter checker imports, or report focused compilation as official-checker acceptance.

## Update: legitimate RAM-backed artifact storage

Read-only capability inspection found existing /dev/shm tmpfs4.9GiB free, but no direct scratch mount is established. Current uid1000 has zero effective/permitted capabilities, and seccomp is active; no mount or namespace probe was attempted.

Root proposed a legitimate alternative: persistent keeper process owns anonymous memfd files containing byte-for-byte genuine downloaded artifacts, while normal cache paths remain symlinks to /proc/PID/fd/FD. This does not modify checker code or manufacture compiled artifacts. Python os.memfd_create is available. No memfd or symlink was created during this review.

Resource limits: cgroup memory.max8GiB, no physical swap; RLIMIT_NOFILE soft/hard16384, system file limit about1million. The current memory charge around4.1GiB was mostly3.9GiB filecache, with about245MiB anonymous memory and246MiB kernel memory. Reclaimable disk pagecache means more real headroom than raw memory.current suggests. Lean CompactedRegion documents mmap-backed olean regions, so genuine artifact bytes in memfd may overlap the checker mapping charge, though pointer fixup/private mappings and checker heap can add memory.

Assessment: this is a plausible controlled storage route, unlike deleting required files or changing checker imports. It is not yet proven sufficient for a full checker run. Select the largest genuine artifacts to obtain the needed GiB while staying comfortably below16384keeper FDs, rather than moving every tiny file. Preserve file bytes/hash and relevant metadata; run unchanged Lake freshness checks after relocation. Keep the keeper process alive through builds/checking and monitor memory.current. Avoid concurrently running other memory-heavy processes. Do not assume a full4.9GiB RAM allocation leaves enough checker memory under the8GiB cap.

This updates the earlier disk-only conclusion: the ordinary overlay volume remains insufficient, but a memfd-backed cache could legitimately extend storage if peak memory measurements permit.


RAM keeper implementation review (2026-11-25 06:43 UTC): Scratch keeper.py now implements genuine sealed memfd relocation, original allowed-cache path symlinks, repeated SHA256, preserved mode/mtime, 5 GiB/11900 descriptor hard ceilings, atomic rollback, recoverable restore and explicit status/stop. Unit failure injection and separate-process 2 MiB mmap smoke passed; logs under /tmp/oec/pequalnp-pilot-70/ram-keeper. No real cache artifacts moved, smoke daemon stopped. Must coordinate only quiescent artifact files and retain keeper lifetime until restoration. Full checker memory viability remains unmeasured.


Checkpoint review (2026-11-25 07:02 UTC): PASS for 54 stable search artifacts (422360 bytes), inventoried with SHA256 in /tmp/oec/pequalnp-pilot-70/research-audit-0700.json. Sources cover the optional first-20-gate non-domination constraints, third-gate stabilizer restrictions, independently checked certificates, recording wrapper and regression tests. Completed general/guided/CEGIS/pairdirty searches are UNKNOWN, with no exhaustive negative conclusion. Fixed-network smoke SAT/UNSAT results are regressions only. The pairdirty status field configuration=unsat names a solver preset; the actual timeout verdict is UNKNOWN. Its 483164081-byte DRAT artifact is explicitly incomplete and excluded from preservation; metadata records its hash. The CEGIS run found no 31-row model, which is not a nonexistence claim. Two live circuit-search logs were excluded; immutable run metadata and phase inputs were reviewed. Credential-pattern scan found no flags; tracked changes remained research notes only.

Official cache staging review: PASS for CachePlan.lean and decompress-batched.py. getHashMemo starts from full Mathlib; official prepareDecompConfig selected 6636 unique archives and correctly skipped 2481 matching traces, totaling all 9117 successfully downloaded modules. The batch script retains official archive/base JSON data and leantar options, waits for extraction completion before relocating closed immutable artifacts, preserves full logs and stops on errors. No checker or Lean runtime module changes. RAM and disk limits still require external monitoring; the script checks a 500 MiB disk floor and its own descriptor/budget caps, not cgroup free memory. Full checker success remains a separate required check.

Resume review: PASS for decompress-resume.py. Batch35 had completed extraction before the post-extraction space check stopped, so START5400 resumes at the next module. Remaining archives alone are validated. Every keeper operation targets the auxiliary socket and obeys its returned 820677200-byte ceiling; the primary remains fixed at 4548031920 bytes. Combined RAM ceiling is exactly 5 GiB. Descriptor ceilings apply separately to each keeper process, with aggregate counts reported. Official decompression arguments and the 500 MiB floor are unchanged. New extraction/status logs use resume prefixes. The research audit inventory was refreshed after verified gzip compression of the incomplete DRAT: 54 files, 422799 bytes.

Kissat split/runner review: PASS. Independently compared the prepared final-AND 26-gate CNF against its reviewed base: all existing lines except the header are unchanged; the clause count increases from 365449 to 365450 and the sole appended unit is -36888, matching the encoding where a positive operation variable means OR. Mapping fields are unchanged except count and explicit branch/hash metadata. Solver binary SHA256 matches the pinned official Kissat4.0.4 provenance. The runner preserves complete output, hashes inputs/binary, records wall/CPU measurements, and checks SAT models on all 16384 inputs before recording a witness. Fixed-AND28 smoke is SAT and fully verified; opposite-operation28 smoke is UNSAT for that fixed regression only. A future UNSAT verdict applies only to this restricted final-AND instance. A raw SAT status is insufficient without full_truth_table_verified=true.

Cofactor artifact consistency review: stable cofactor_dag.py and two JSON/log pairs add a bounded heuristic search, with factor_partition.py as the local dependency. Main log and result metadata agree on 1942 trials, 24.143072169 seconds, best27 gates and zero full-table errors. Notes explicitly state that neither the full problem nor this heuristic family has been proved optimal. Credential-pattern scan had no flags.

F0-plus-available-A audit: PASS. Reproduced the 23-gate base byte-for-byte with the documented no-canon/no-liveness/no-lex-order flags (SHA256395f8900a3e638cc6fb45cf0eea6e35011be3d8194bc5a3c3fe792f6c47bfb00). The prepared instance changes only its clause count and appends exactly six correct positive units for OR(1,2), OR(4,13), giving A=x1 OR x2 OR x4 at 13-input wire14. Moving to14 inputs shifts that wire to15. The removed vertex13 has precisely neighbors1,2,4, so (A OR F0) AND (x13 OR F0) equals the full target. The three appended gates have valid backward indices and turn23 gates into26. Independently evaluated the retained25-to28 smoke extension on all16384 inputs successfully. This remains a restricted sufficient strategy; no completeness or negative claim follows. Scratch review.json and full log are under f0-audit/.

Frontier checkpoint packaging review after the07:28 workspace restart: PASS. All20 manifest entries (10 Lean sources and10 empty compilation logs;72939 bytes) match both original scratch files and preserved copies byte-for-byte and match recorded SHA256/size. Imports are only PEqualNP.Defs or Mathlib.Init. No forbidden root escape, strings, unsafe proof commands, axioms or attributes were detected. Per-lemma independent mathematical reviews remain the relevant source reviews; this pass verified preservation and packaging. Main Lean/core files were unchanged. Validation correctly states that the26-gate theorem is unresolved and the full-cache checker ended exit137 without a verdict. It does not claim acceptance.

Fresh post-restart research inventory reviewed at2026-11-25T07:32:51Z:124 stable files,1110271 bytes, with SHA256 in /tmp/oec/pequalnp-pilot-70/research-audit-fresh.json. This includes cofactor/F0/Kissat sources and dependencies, solver provenance, completed shadow3 output, and interrupted third-prefix/Kissat output. Both interruption metadata files match their full log hashes and explicitly leave solver verdict, exit code and finish time null. No runtime or negative result is inferred from the restart. New live F0+A23 solve/wrapper logs are excluded, while immutable run metadata is retained. All generated CNFs, incomplete proof blobs and upstream binaries/checkouts are excluded. Credential-pattern scan found no flags; no unexpected core changes were present.

Focused-cache restoration selection review: PASS before deletion. The original manifest lists101919 unique paths:87928 regenerable regular Mathlib build artifacts outside the2566-module focused closure (998917844 bytes), and13991 symlinks matching the two original dead keeper manifests exactly;4059 lost links belong to the focused closure. Both allowed roots resolve to their literal paths. Input setup hashes match;68 requested roots belong to the preserved closure. Source/toolchain/project/Cache/other dependency files are not eligible. Apply validates all entries before mutation and rechecks each stat before unlink. Existing focused regular bytes remain preserved. Focused traces remain, so subsequent selected-root restoration requires official forced unpack; this review does not assert that recovery or a new build has completed. Disk margin after restoration remains a separate concern.

Recovery manifest compression follow-up: PASS. Independently decompressed the2221149-byte gzip and verified original51035639-byte SHA256349b6ee10f158fe55dd6d9fb1b7d9c5e0dc64596c52ad736f9731d30f1c020b4 and101919 unique entries. The loader checks this checksum before JSON parsing; selection and deletion guards are unchanged. Root authorized applying the reviewed manifest.

Corrected F0+A24 route: PASS. The earlier three-gate Shannon extension was sufficient but unnecessarily restrictive. The helper now defaults to the direct identity F=F0 OR (x13 AND A), which adds exactly two gates and lets a24-gate F0 witness meet the26-gate target. Reproduced the24-gate base byte-for-byte with intended flags (SHAc3ae35e9f9c2371b8eb9a4eca54acd5e454d12a83fe6e1d8c5c759f0427340ad); only the six correct prefix units are appended, yielding130758 clauses. Independently rechecked the25-to27 direct smoke on all16384 assignments. The new helper source SHA isecc2ba6736568545e3fc3940e9898af55e8fe788e87a610c5850cbeac7b16574. Old three-gate smoke remains reproducible using the explicit shannon method.

Authorized obsolete-CNF removal audit: PASS as a retained-record cross-check. The exact29 authorized top-level CNF paths and sizes match obsolete-cnf-removal.json, totaling108354392 bytes; all have recorded SHA256, and five hashes match earlier independent records. New24-gate inputs are preserved. Root had already removed the bytes before this final pass, so this is not a new hash computation over all29 files. No regeneration or deletion was performed by this reviewer.

## Completed-search and optional-runner checkpoint, 2026-11-25T08:44:29Z

Matching-cut14 completed UNKNOWN after 2700.022 wall seconds and 2534.165 CPU seconds. Its complete log, source hashes, and recorded verdict agree. The fixed-family timeout supplies no unrestricted nonexistence conclusion. General-OR26 and joint TEN have static reviewed launch metadata only in this checkpoint; their live solver logs are excluded.

The optional joint phase generator and phased runner have separate independent PASS reviews. All reviewed source, input, binary, and phase hashes match. The phased smoke is the known 27-gate baseline. The 991-literal near-seed preferences have 47 full-target errors and remain soft preferences, not a satisfying model or added constraints. The final first-pair postprocessor hash matches its independent review; it accepts only the supported fixed correlated families and preserves the reviewed normal-form scope. Unreviewed liveness and tail-lex artifacts are excluded.

Commit034fdef whitespace audit: all442 diagnostics are trailing whitespace in34 preserved raw solver logs. Every committed log matches its original scratch bytes. There are no source or Lean whitespace diagnostics. Complete diagnostics and the per-file hash report are retained under the job scratch directory as review-034fdef-diff-check.log and .json. Raw logs are preserved exactly.
