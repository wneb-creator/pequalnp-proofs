The official checker run on the preserved partial file for L-meta-4970 ended in a confirmed kernel out-of-memory kill, not a mathematical rejection or a timeout. The target theorem was absent, so this run could not have accepted the posted statement. The exact recorded result is:

```text
CHECKER FAULT: the verifier ended without a verdict (exit 137).
```

The complete branch log is `results/orch/checker-partial-final-4970.txt`. It reached `verifier reading the built file` at t=5s. The parent observed termination around 2026-11-25 16:42:20 UTC. No checker or trusted cache changes were made during this diagnosis. No FD handoff, artifact removal, or rerun was implemented after the diagnosis.

The environment uses Lean v4.36.0 and Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Before the run, the complete pinned cache was validated by `lake --no-build build PEqualNP.Defs Mathlib`, which reported `All targets up-to-date (18422 jobs)`. The repository's existing native verifier built successfully in 5 jobs. No Mathlib source build or `lake update` was used.

Observed resource evidence:

- Cgroup memory limit: 8,589,934,592 bytes (8 GiB).
- At the first sample: memory.current 8,589,844,480 bytes; memory.events reported max=243779, oom=0, oom_kill=0.
- After termination: memory.events reported max=376435, oom=1, oom_kill=1. The recorded memory peak was 8,590,057,472 bytes.
- PID 40459 initially had RSS 4,360,316 KiB: 3,432,492 KiB shared-memory mappings, 707,532 KiB ordinary file mappings, and 220,292 KiB anonymous memory. Its recorded high-water RSS was 5,061,048 KiB.
- A 10.003-second sample showed worker 40461 making progress: 3.71 CPU seconds, 16,105 major faults, and 1,545,457,664 disk-read bytes. Its state was runnable; the main and I/O threads were waiting normally. Earlier cumulative disk reads already exceeded 36 GB.
- After the kill, cgroup shmem remained 4,861,149,184 bytes. Disk space available at the final read-only inventory was 372,604,928 bytes.

This shows severe file-page reclaim and repeated disk reads under the fixed memory limit. The cache holders retain approximately 4.5 GiB of unconditionally resident anonymous-file data; that capacity is unavailable to the verifier even when a particular held artifact is not in its current working set. The final OOM counter increment confirms the exit-137 cause. The exact verifier substage at the kill was not instrumented, so it should not be described more narrowly than the verifier phase.

The missing-theorem test is late in the unchanged checker. `lean/CheckLemma.lean` first imports all of Mathlib and the definitions root with extension initialization at lines 355–356, imports the target at line 380, replays definitions and project constants at lines 413–419, and only then tests theorem existence at lines 432–433. An absent target theorem therefore does not avoid the full environment cost.

The checker source and pinned configuration matched committed HEAD during diagnosis (`714ebaf1046616e29db38dde7bdc4ed60c89af33`). The parent had fetched newer upstream proofs into FETCH_HEAD but had not checked them out. The working checker and configuration were not those newer fetched files. Observed SHA-256 hashes were:

```text
lean/CheckLemma.lean 86997b026ef2b80d738df77f4c214166cf5b0b2ea8cc98d4bd3c8b5e420dbdd5
tools/check-lean.mjs d3f8ca82be7a4aabcf5aba7727b715140c82fa575340c6a8f5d7b134bf4d23ad
lean/lakefile.toml ee756ab61cf24d2fd5f561d89080cf162e34f35b06d9b6101bc680ef1619a7bf
lean/lake-manifest.json d0af863cde532caaef1b1bee0d63ec47100208e33e488309cb80abc88b8f1509
lean/lean-toolchain 582a63f8f9c5128067b688778c1051cf1464c3ca9d57b9325025c051c29b774a
```

The three cache holders must remain alive until their artifacts have been safely transferred or restored. Their state files are under `/tmp/oec/pequalnp-pilot-154/`:

| Holder | PID | Files | Exact held bytes | State file |
| --- | ---: | ---: | ---: | --- |
| Initial | 5982 | 9241 | 2147483645 | `memfd-artifacts-state.json` |
| Stage 2 | 8784 | 3906 | 1610612442 | `memfd-artifacts-stage2-state.json` |
| Stage 3 | 31621 | 1140 | 1073741376 | `memfd-artifacts-stage3-state.json` |

All held artifacts were copied with SHA-256 validation, original size/mtime preservation, atomic path replacement, and kernel seals preventing writes, growth, shrinkage, or further seal changes. The complete Lake no-build validation passed using those paths. Independent later hash, mmap, seal, and mtime samples also passed. There are no exact duplicate contents among the 14,287 recorded artifacts, so simple whole-file deduplication offers no recovery.

Potential optimization for a future full-proof run, **not implemented**:

1. Hand off ownership to a successor holder that supports restoring individual artifacts. It can open the existing holders' recorded `/proc/PID/fd/FD` paths, preserving the same sealed inode without duplicating RAM. A read-only probe confirmed identical device/inode, size, and seals. There are 14,287 artifact descriptors and a soft/hard limit of 16,384, leaving room for a successor's control descriptors. Every cache link would need an atomic replacement, validation, and durable state record before any old holder could be stopped. Until that entire handoff is validated, retain all original holders.
2. Reclaim ordinary disk space by making verified compressed backups of optional toolchain/build components. The measured candidate inventory is 15 core static archives (408,819,420 bytes), nine unused auxiliary executables (84,605,280 bytes), and the already-built Mathlib cache utility executable (124,968,488 bytes): 618,393,188 bytes total. A read-only `zstd -q -c` measurement produced 119,228,930 compressed bytes, a potential net recovery of 499,164,258 bytes. The measurement streamed compressed output to a counter and discarded it; no backup was created and no original was removed. The exact candidate paths are recorded in `optional-storage-inventory.json` in task scratch.
3. If this optimization is attempted, verify each compressed backup by decompression and hashing before removing its original. Process smaller candidates first and the largest static archive last to maintain free-space reserves. The currently built `checklemma` must remain intact. Native static libraries are needed for relinking; after any such move, verify that the unchanged verifier is still up to date before running the official checker, and restore archives if any relink is required. This continuation behavior is supported by Lake source inspection but has **not** been tested with archives absent.
4. Restore selected held artifacts to ordinary disk files with identical bytes, mode, and mtime; validate their hashes; atomically replace the cache paths; then close only the successor's corresponding FDs. Keep every required cache path continuously valid. Using the measured inventory and a 350 MiB disk reserve would make about 505 MB available for such restoration at the sampled free-space level. Ordinary disk-backed pages can then be reclaimed under pressure, unlike the current pinned memfd contents.
5. Revalidate `lake --no-build build PEqualNP.Defs Mathlib checklemma` and the named proof build, then run the unchanged official checker. Reduced memory pressure is plausible, but neither success nor the amount needed can be guaranteed before an actual rerun. The current failure alone does not establish that an approximately 500 MB reduction would suffice.

Do not remove IR on the assumption that the checker only reads declarations: Lean's import machinery can read `.ir` and `.ir.sig` while loading extensions. Likewise, missing dependency `.c` or `.ilean` files can trigger Lake rebuilding, even though they are not ordinary verifier module data. Do not leave broken cache links, disable checks, change trusted source, modify pinned configuration, or substitute a different verifier. The proposed restoration route preserves complete artifact contents and paths throughout.

Evicting clean pages with `posix_fadvise(DONTNEED)` helped setup, but it cannot release held memfd data. During this run the kernel was already reclaiming millions of ordinary pages. Evicting small source/log files would not resolve the observed working-set shortage. Pausing the parent's expendable solvers could recover their approximately 214 MiB (UNVERIFIED independently: this amount was supplied by the parent and was not measured here).

Current invocation requirements remain:

```sh
PATH="/tmp/oec/pequalnp-pilot-154/lean-4.36.0-linux/bin:$PATH"
PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-154/lean-4.36.0-linux/bin/lake
PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-154/pnp-state
```

Detailed setup records remain in `lean-setup-complete.txt`, `capacity-notes.txt`, and the three holder state files under task scratch. The 10-second resource sample is `checker-resource-sample.json`; the compression measurement is `optional-compression-estimate.json`. Preserve the exact original FAULT log as the result of this official checker run.
