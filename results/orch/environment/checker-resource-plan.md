# Pilot 76 checker resource plan

Read-only investigation, 2026-11-25. No deletion, sparse-checkout change, checker
execution, replacement keeper, or cache restoration was performed for this plan.
Compression measurements streamed data and retained the original files.

## Actual state

* Cgroup limit: 8,589,934,592 bytes. Two recorded OOM kills.
* At 10:50 UTC, current cgroup use was 2,312,806,400 bytes, with only 90,112
  bytes of shmem. Host MemAvailable is not the job's usable memory budget.
* The old keeper PID 14381 is a zombie, FDSize 0. Its last state update was
  09:45:24 UTC. The earlier assertion that it still pins 3.16 GB is stale.
* Disk free was 36,630,528 bytes at the first measurement; it subsequently
  fluctuated to approximately 47 MB as other jobs finished generated files.
* The 516 migrated ordinary artifacts remain on disk. The 12,754 other memfd
  artifacts are unavailable: 3,158,568,624 bytes, across 6,580 unique official
  cache archives. Zero `.ltar` archives remain locally.
* Archive hashes and per-artifact SHA-256 values remain in
  `ram-cache/manifest.jsonl`; disk-migrated paths are recorded separately.
  The missing compressed download total is UNVERIFIED: it was not recorded,
  and the old progress log contains transfer rates rather than archive sizes.
* The largest known extracted bundle among needed archives is 10,518,295
  bytes. Sequential download/extraction therefore avoids retaining thousands
  of compressed archives at once; preserve at least 100 MB of working reserve.

## Concrete disk savings for root review

| Candidate | Recoverable bytes | Preservation/constraint |
| --- | ---: | --- |
| Sparse checkout of 3,998 other Outside sources | 303,661,056 allocated | All retained in Git; keep named target and all other directories. No current Outside source modifications. |
| Compress unused Mathlib cache executable | 93,735,959 raw net | Original 124,968,488; measured zstd level 3 output 31,232,529. Verify round-trip SHA before removing executable; restore before invoking `lake exe cache`. |
| Compress official toolchain source directory | about 29,528,046 allocated net | Allocated 35,803,136; measured tar+zstd output 6,275,090. Runtime artifacts remain unchanged; source is recoverable locally. |
| Failed FUSE experiment build/source trees | about 22 MB | `fuse-2.9.9`, `fuse-install`, `squashfuse-0.6.5`; public source tarballs and all diagnostic logs remain. Keep squashfs-tools because it reads the static-library recovery image. |
| Discard local optional toolchain recovery images | 142,561,280 allocated | Higher operational risk: would require downloading the exact public Lean 4.36.0 release again for native relinking. Preserve manifests. Prefer keeping these images. |

Do not remove research results, active solver files, named proof artifacts,
Mathlib C/editor files, `.ir`, `.ir.sig`, or any `.olean` companion. The prior
reversible Mathlib C-file test failed the no-build closure. Lean's loader reads
the private/server triplet and IR companions, so omitting those is unsafe.

Git recompression is not worthwhile: 28,145 objects already occupy three
packs totaling 73,866 KiB, with zero loose or garbage objects. Repacking needs
temporary disk and has no demonstrated meaningful saving; do not prune history.

Proposed sparse checkout command, after checking no new Outside changes:

```bash
git --no-pager status --short
git sparse-checkout set --no-cone --stdin <<'EOF'
/*
!/lean/PEqualNP/Outside/*
/lean/PEqualNP/Outside/L_meta_2583.lean
EOF
git --no-pager status --short
```

This changes only local checkout configuration, not the tracked diff. Agents
must thereafter read other accepted proofs with `git show HEAD:<path>`.

Proposed compression commands, with full diagnostics redirected by the caller:

```bash
zstd -T1 -3 /workspace/pequalnp-proofs/lean/.lake/packages/mathlib/.lake/build/bin/cache -o /tmp/oec/pequalnp-pilot-76/cache-executable.zst
tar -C /tmp/oec/pequalnp-pilot-76/toolchain -cf - src | zstd -T1 -3 -o /tmp/oec/pequalnp-pilot-76/toolchain-sources.tar.zst
```

Record and compare complete SHA-256 values after decompression before removing
any original. No removal commands are included because root requested review
before deletion. With the conservative first four choices, approximately
0.45 GB additional disk becomes available. After maintaining the working
reserve, roughly 0.38 GB of the missing artifacts could be restored to disk,
leaving approximately 2.8 GB in a replacement keeper. Giving up both local
recovery images lowers that to approximately 2.65 GB. These are estimates from
the measured byte counts; concurrent scratch growth changes the final budget.

## Genuine cache restoration

Root must own the replacement exec session. Do not launch another keeper
owned by a subagent that may finish its turn. Liveness must check `/proc/PID/status`
for a non-zombie state and actual descriptors, not just PID-path existence.

The original keeper/migration scripts must not be reused unchanged: they have
old PID assumptions and treat dangling symlinks as errors. A reviewed recovery
variant should:

1. Read the original manifest and migrated-path list. Select only the 6,580
   needed official archive hashes; preserve every current ordinary artifact.
2. Download one archive at a time using curl from the original official URL:
   `https://cache.mathlib.org/mathlib4-master/f/<recorded-archive-name>`.
   Save complete diagnostics. Do not download all 6,580 files to the small disk.
3. Extract with the existing official `leantar -x -C <owned-stage> <archive>`.
   For each required artifact, compare its recorded SHA-256 before installation.
4. Replace only old `/proc/14381/fd/...` symlinks named by the manifest. Use
   ordinary disk while preserving the reserve, then root-owned memfds. Retain
   all other existing files and the previously verified named build closure.
5. Record actual current disk/RAM storage per path in a new manifest; do not
   carry forward stale original counters. Delete each downloaded archive only
   after all its required members are installed and verified.
6. Verify the no-build closure before any real build:

```bash
. /tmp/oec/pequalnp-pilot-76/lean-env.sh
lake build --no-build checklemma +PEqualNP.Defs +PEqualNP.Outside.L_meta_2583
```

Run that command from `/workspace/pequalnp-proofs/lean`. Never permit a missing
artifact to trigger Mathlib source compilation, and never run `lake update`.

## Runtime options accepted by the unchanged checker

`tools/check-lean.mjs:143` removes all `LEAN_*` and `LAKE_*` variables from the
child environment. Thus `LEAN_NUM_THREADS` and `LEAN_IMPORT_WORKERS` cannot
reduce this official checker's memory use. The host exposes only three CPUs
anyway. `LEAN_IMPORT_WORKERS` specifically controls frontend snapshot loading,
not the direct `importModules` calls in CheckLemma.

Both installed Lean and the verifier contain mimalloc. A light `lean --version`
capability probe confirmed the allocator's `purge_delay` default is 1000 ms,
and that `MIMALLOC_PURGE_DELAY=0` is recognized as zero. This option is not
removed by the checker environment filter and affects allocator page release,
not theorem checking or imports. A future unchanged checker run may therefore
use a command-scoped prefix:

```bash
MIMALLOC_PURGE_DELAY=0 node tools/check-lean.mjs <the existing checker arguments>
```

Keep the existing exact checker arguments. Do not add LD_PRELOAD, wrappers,
source edits, alternate kernels, or altered memory/trust checks. The saving
from immediate purging is UNVERIFIED until a future measured run; it cannot
reduce live objects or memfd backing. `MIMALLOC_ARENA_EAGER_COMMIT=0` is not a
credible RSS saving according to the allocator's own documentation.

Primary documentation read on 2026-11-25:

* https://github.com/microsoft/mimalloc#environment-options
  explains immediate page purging and its performance tradeoff.
* Exact local Lean 4.36.0 source: `Lean/Environment.lean` (module companions)
  and `Lean/Elab/Frontend.lean:210` (snapshot import worker option).
* Unchanged local `tools/check-lean.mjs:143` establishes environment filtering.

## Expected outcome and limit

This is a credible incremental improvement, not a demonstrated fit. The last
verifier reached at least 5.58 GB RSS before OOM with 3.16 GB pinned backing;
RSS and backing partially overlap and cannot simply be added. Conservative
disk recovery can remove another roughly 0.38 GB of pinned backing, and
allocator purging may lower transient retention. No calculation proves that
the full kernel replay will fit 8 GiB. Defer the expensive restoration and next
official verifier run until root judges it warranted, ideally with a complete
theorem. Current official checker status remains unavailable, not accepted:
two earlier OOM faults, followed by loss of the anonymous verifier-only cache.
