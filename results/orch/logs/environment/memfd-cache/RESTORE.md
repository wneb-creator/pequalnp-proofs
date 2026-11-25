Only immutable downloaded toolchain or cache artifacts are candidates. Proof source files are never replaced.

Each stage has a JSON manifest with original paths, hashes, modes and nanosecond timestamps, and a state file naming its live manager PID. Verified compressed tar archives were created before migration; closeout may delete these disposable backups after testing live restoration, to recover enough disk space. Do not terminate a manager while any corresponding path remains a link into that process.

Stage 1 original size: 2,147,489,644 bytes across 2,854 files. Backup archive: stage1.tar.zst, approximately 501 MiB. Source root is the downloaded pinned toolchain under this job's scratch directory.

To restore after freeing enough disk space, run from the repository:

    python3 /tmp/oec/pequalnp-pilot-144/memfd-cache/restore_stage.py /tmp/oec/pequalnp-pilot-144/memfd-cache/stage1.json /tmp/oec/pequalnp-pilot-144/memfd-cache/stage1.tar.zst

The restoration script streams verified bytes to temporary regular files, restores metadata, replaces each link atomically, verifies all restored hashes, and only then terminates the manager. An interrupted or capacity-limited restoration leaves the manager alive; retain the archive and state file and finish restoration later.

If the manager dies unexpectedly, retain the archive and manifest. Restore its links from the archive after obtaining space; the proof source and Git branch are unaffected. If full cache downloads consume the space needed for restoration, remove only newly downloaded reproducible cache artifacts identified against the recorded baseline before restoring.

Stage 2 uses stage2.json and stage2.tar.zst with the same restoration script. Its source root is Mathlib's downloaded build artifacts. mathlib-cache-baseline.json records the existing build-artifact paths immediately before stage 2 and further full-cache batches; new artifacts beyond that baseline are reproducible cache additions, never proof sources. Restore stage 2 before stage 1 when returning to disk-backed operation. Each manager stays alive until its own links have been restored and verified.

Live restoration without a compressed archive:

    python3 /tmp/oec/pequalnp-pilot-144/memfd-cache/restore_live.py /tmp/oec/pequalnp-pilot-144/memfd-cache/stage2.json
    python3 /tmp/oec/pequalnp-pilot-144/memfd-cache/restore_live.py /tmp/oec/pequalnp-pilot-144/memfd-cache/stage1.json

The live script reads the existing immutable memfd through its manager's recorded descriptor, verifies SHA256 and size, restores original mode and nanosecond timestamps, and atomically replaces the symlink with the verified regular file. It verifies every restored artifact before terminating that stage's manager. An interrupted restoration leaves the manager alive. The one-artifact test and subsequent no-build preflight passed; see restore-live-test.log and preflight-after-live-restore.log.

Pinned redownload fallback if both a live manager and its archive become unavailable: the downloaded Lean release is exactly Lean 4.36.0 for Linux x86_64, https://github.com/leanprover/lean4/releases/download/v4.36.0/lean-4.36.0-linux.tar.zst, archive SHA256 2b7ab1ed8b92d2e6abfaf41344823b510064dbc9c0260cac73eb496ab2dea6eb. Verify this complete archive checksum before extracting migrated stage1 paths; verify each restored file against stage1.json. Preserve required public, private, and server oleans and IR. Mathlib is pinned to fc4f59e577feb1a4956671bc04ac18aaaf8cd842; after Lean is functional, use that checkout's official cache tool to restore affected modules, and verify original stage2 artifact hashes. Module names come from the stage2 manifest's lib/lean/Mathlib paths after removing artifact suffixes. Remove only dangling downloaded cache links before forced unpack if required. Never rebuild Mathlib from source or change revisions.

For closeout, closeout-new-cache-inventory.json identifies only reproducible generated files added after mathlib-cache-baseline.json. Removing those additions frees room to return the known proof dependency closure and the toolchain to ordinary disk files. No proof source, Git object, or user data is a candidate. Complete restore and capacity logs are retained in this directory.
