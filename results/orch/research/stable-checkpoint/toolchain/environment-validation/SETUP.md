# Pilot 78 Lean setup

From `/workspace/pequalnp-proofs/lean`, run:

```sh
source /tmp/oec/pequalnp-pilot-78/toolchain/env.sh
lake build <named-module>
```

Lean 4.36.0 was installed from the official release; Mathlib remains pinned at
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. No lake update was run.
The initial environment had neither Lean nor the promised cache.

`lake exe cache get Mathlib.Init` passed, and all 9,117 authentic Mathlib cache
archives were downloaded and extracted. `lake build +PEqualNP.Defs checklemma`
passed both before and after final storage changes: 5,151 jobs, no Mathlib source
compilation. Full logs: `build-baseline.stdout`, `build-baseline.stderr`,
`build-final.stdout`, `build-final.stderr`.

## Storage arrangement

The container has a 7.9 GiB overlay and an 8 GiB cgroup memory limit. All runtime
artifacts remain authentic and byte-identical. Some `.olean.private` artifacts
are sealed memfd files, with symlinks in ignored `.lake` directories. Keep holder
PID 4303 alive for subsequent builds. Current state is 8,912 retained files,
3,312,690,600 bytes. An additional 223 files (616,857,552 bytes) were hash-verified
and restored to ordinary disk. Independent review checked all symlink targets
and sampled SHA-256, seals, modes, and mmap reads.

The current disk reserve is about 230 MiB. Only optional Mathlib generated `.c`
and `.ilean` files outside the original 2,480-module Defs dependency closure were
pruned; the complete removal list is `optional-pruned.jsonl`. Thus use selective
proof imports and restore any additional build dependency artifacts before
building. Required runtime files were never pruned.

The already extracted official download archives were removed to recover disk;
they can be downloaded again. The cache-fetch executable is backed up as
`cache-executable.zst`. Restore it, with SHA-256 verification, before another
cache command:

```sh
python3 /tmp/oec/pequalnp-pilot-78/toolchain/restore-cache-executable.py
```

This needs about 125 MB of free disk. Toolchain static libraries, IDE metadata,
and public toolchain sources are preserved in `lean-optionals.tar.zst`, whose
5,200 entries were all hash-verified before removal. They are unnecessary for
the already linked checker and normal proof elaboration. If a future native
link needs them, `restore-lean-optionals.py static` restores exact static libs;
`ide` and `source` restore the other categories. Ensure disk capacity first.

`memfd-control.py status` reports live storage; `store <absolute paths...>`
relocates regular private artifacts to sealed RAM, while `release <paths...>`
restores retained private artifacts to real disk with SHA-256 verification.
These are storage operations only; they never change Lean artifact bytes.

## Checker limitation

The unchanged checker executable must load all Mathlib at runtime. A smoke test
using existing module `PEqualNP.Defs` and statement `True` should reach a missing
declaration rejection after imports; neither attempt reached that stage.
The first was stopped during sustained memory pressure. After lowering memfd
storage by 617 MB, the measured retry again saturated the 8 GiB limit for 60
continuous seconds and was terminated at 68.4 seconds (exit -15). It emitted no
verdict. Logs and memory samples are `checker-smoke-retry.*`. No OOM kill occurred.
This is a resource limitation, not a proof rejection.

A read-only compressed FUSE filesystem was investigated to avoid nonreclaimable
RAM backing, but the mount was refused with `fusermount3: mount failed: Operation
not permitted`. No workaround or retry bypass was attempted. Its unused source
and build logs remain in this scratch directory. The checker and repository
sources were not edited; git status remained clean.


2026-11-25 11:12 UTC source archival update:
- Root authorized archiving Mathlib `.lean` sources outside the static build closure of `PEqualNP.Defs`, `PEqualNP.Outside.L_gct_231`, and `CheckLemma`. Header imports, including `public meta import` and `import all`, were traced. CheckLemma statically imports only Lean; its Mathlib use is dynamic compiled import.
- 6,518 source files /71,939,474 bytes archived to `mathlib-source-backup/chunk-*.tar.zst` (17,155,552 compressed bytes), in 935 small chunks. Every archive was completely decompressed and SHA256 checked before deleting its source files. All runtime `.olean`, `.olean.server`, `.olean.private`, `.ir` remain untouched. Current required-source closure and provenance recorded in `source-archive-plan.json` and `source-closure-edges.json`; `all` in the raw missing-token list is Lean's import modifier, not a module.
- Each chunk's JSON manifest stores original SHA256, file size, mode, atime_ns, mtime_ns. `python3 /tmp/oec/pequalnp-pilot-78/toolchain/restore-mathlib-sources.py Mathlib.Module.Name` restores named modules; argument `all` restores all and needs about72MB free. Exact hash and nanosecond mtime restore smoke test passed. Future new imports may require restoring their source closure as well as previously archived `.c`/`.ilean` optional artifacts before Lake builds.
- Disposable duplicate slice2 inputs in numeric/ were removed only after comparison against geometry_search/slice2 originals. Regenerable rg filename censuses were removed during a zero-disk emergency; the complete source archive manifest remains.

2026-11-25 11:38 UTC auxiliary executable archival:
Unused bundled alternate checkers/IDE helpers (lean4lean, con-leche, leanchecker-paranoid, lean-beam-mcp, beam-daemon, con-ron, lean-beam, nanoda_bin, leanexport) were archived individually under `auxiliary-program-backup/` with full SHA256 round-trip verification before source removal, preserving mode and nanosecond mtime in manifest.json. No repository checker/build script or CheckLemma references these programs. Normal lean, lake, clang, linker, cadical, leantar, and all runtime import artifacts remain intact. Restore via `python3 /tmp/oec/pequalnp-pilot-78/toolchain/restore-auxiliary-program.py PROGRAM` or `all`. leanexport was restored as an exact hash/mtime smoke test and remains available.

2026-11-25 12:06 UTC metadata archival:
- Archived53,262 ignored Lake `.hash`/`.trace` files outside the original selective closure:218,161,152 allocated bytes→4,927,488 backup bytes. Every file was fully hash-verified in its tar.zst before removal; compressed JSON manifests preserve SHA256, mode, nanosecond mtime and atime. All runtime import files were untouched. A real restored sample passed exact hash/mode/mtime checks.
- The no-build smoke caught LeanSearchClient child modules omitted by the static closure plan. Restored all metadata for Basic, Syntax and LoogleSyntax; the second `lake build --no-build checklemma +PEqualNP.Defs +PEqualNP.Outside.L_gct_231` passed. No Mathlib source compilation was attempted. Full validation:optional-metadata-validation.json.
- Restore a future module with `python3 /tmp/oec/pequalnp-pilot-78/toolchain/restore-optional-metadata.py Mathlib.Module.Name`; `all` restores all original metadata and needs~208MiB disk. Its source and optional c/ilean may also require the older restore procedures.
- Root separately enabled sparse checkout omitting only unrelated historical Outside proof sources, preserving the named proof and all required imports. See root-sparse-checkout-validation.json. Disabling sparse checkout needs~304MiB free disk.

2026-11-25 12:10 UTC additional private-artifact migration:
-272 authentic sealed memfd private artifacts (432,790,536bytes) were individually SHA-verified, copied and verified by the unchanged holder protocol, atomically restored to disk, then checked for exact bytes/mode/nanosecond mtime. Holder4303 now retains8,640files/2,879,900,064bytes (~2.68GiB). Disk reserve after migration~109MiB. The complete plan and event log preserve provenance and rollback paths.
-Postmigration `lake build --no-build checklemma +PEqualNP.Defs +PEqualNP.Outside.L_gct_231` passed. This does not claim full checker runtime readiness; another measured smoke must wait until competing CAS/Lean jobs are paused. See private-migration-validation.json.
