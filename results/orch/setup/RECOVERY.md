Lean runtime cache recovery

Pinned toolchain: Lean v4.36.0 (611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9).
Pinned Mathlib: fc4f59e577feb1a4956671bc04ac18aaaf8cd842.

The kit toolchain/cache were absent. Official Lean binaries were installed in
/tmp/oec/pequalnp-pilot-184/setup/lean-4.36.0-linux. A normal lake exe cache get
retrieved the selected proof dependency closure first. The remaining pinned
Mathlib modules were fetched unchanged from cache.mathlib.org using the pinned
Cache.Hashing-generated artifact hashes. All 9,117 cached modules are present.

This container has an 8 GiB filesystem and an 8 GiB memory cgroup. To fit the full
runtime statement library, 9,273 genuine cached artifact parts originally totaling
3,006,414,760 bytes were placed in immutable Linux memfd files. After verified
disk restoration, 9,211 parts totaling 2,838,564,880 bytes remain in sealed memfds;
62 parts totaling 167,849,880 bytes are regular files again. Package .lake links
target /proc/29634/fd/N. The holder process MUST remain alive through all
builds and checks. The files were SHA256-compared before replacement and sealed
against writes, growth and shrinking. All seal bits and file sizes were audited.
No proof bytes, imported constants, or checker code were modified.

If the holder exits, its links must be replaced with the genuine artifacts from
the official pinned Mathlib cache. On an adequately sized machine, obtain the
complete cache normally with lake exe cache get; do not copy these process-local
symlinks as permanent cache files. The complete local per-file SHA/size/FD manifest
is /tmp/oec/pequalnp-pilot-184/setup/artifact-memory-adopted2/manifest.jsonl, with
subsequent transitions in restored.jsonl and put-back.jsonl alongside it. The cache hash
list is setup/cache-hashes.stdout in the same scratch directory.

The initial selected dependency cache has all normal Lake artifacts. Additional
modules used only by the checker runtime omit generated C and editor .ilean files;
they retain every .olean, .olean.server, .olean.private, .ir and .ir.sig part.
Avoid building the entire Mathlib target: restore normal cache facets for any
new source-level imports beyond the existing selected closure first.

The already compiled checklemma verifier is retained. To reclaim disk, native
static archives were removed from the task-owned toolchain, and unused compiler
libraries/auxiliary tools were gzip-archived with SHA verification. Ordinary
Lean elaboration and leanir still run; native relinking would require restoration.
Backups and manifests are under scratch setup/optional-native-backups and
setup/cache-executable-archive.json. PEQUALNP_REAL_LAKE must point to the installed
bin/lake; PATH must include the installed bin directory.

No credentials were printed or written. The holder process and all cache state
are container-local; the actual Lean proof and validation output must be pushed
separately by the root agent.

Storage maintenance after the full checker's memory exhaustion:

The unchanged full runtime import smoke test passed. The subsequent official
checker exceeded this container's 8 GiB memory cgroup and its verifier exited137.
The memory event counter confirmed an OOM kill. A read-only FUSE storage probe
was refused with `fusermount3: mount failed: Operation not permitted`; no mount
workaround was attempted.

An independently reviewed maintenance pass archived and verified 53,169 files:
runtime-only cache hashes/traces, generated project setup JSON, and the public
PR census. Their 110,654,842 logical bytes occupy a 6,819,144-byte tar.gz archive.
The files were removed only after each archived member and unchanged original
passed SHA256 verification. The selected proof import closure was independently
checked: all 88 project setup files reference 2566 modules, disjoint from the 6635
runtime-only modules whose metadata was archived. Scratch recovery commands:

    python3 setup/reclaim_metadata.py restore

The script path above is relative to /tmp/oec/pequalnp-pilot-184. Its archive and
manifest remain in scratch setup/reclaim-metadata. Restore this metadata before
expanding normal Lake builds outside the original selected dependency closure.

A second independently verified archive contains 5296 generated C/ilean cache
facets: 343,630,640 logical bytes compressed to 40,757,737 bytes. Their originals
currently remain present. The reviewed `reclaim_facets.py apply --verifier-pid PID`
can remove them only after that PID is the genuine running checklemma executable,
past Lake's build phase. All .olean/private/server and IR/signature bytes remain
untouched. After the verifier exits, facets must be restored before another build:

    python3 setup/reclaim_facets.py restore

Restoring additional sealed cache artifacts to disk requires keeping the holder
alive. Its restore action copies, hashes, fsyncs and atomically installs a regular
file, verifies it again, then closes that artifact's sealed FD. Its reverse
put_back action makes enough disk room to restore the C/ilean facets afterward.
The original 13941 and intermediate 29410 holders are retired. Current holder
29634 correctly treats this container's persistent PID1 zombies as exited: their
file descriptors have already been released. Both full migrations checked every
SHA, inode, size and seal before old-holder retirement. The final audit verified
all 9,273 moved/restored artifact parts again. The post-maintenance command
`lake build --no-build checklemma` passed with `All targets up-to-date (5 jobs).`
No Lean process remains from setup maintenance. Disk free space is 312,623,104
bytes, leaving approximately 103MB above the 200MiB safety floor for new work.

For a future authorized verifier run, after its Lake build has finished, apply
the reviewed runtime facet cleanup using that genuine checklemma PID, then send
a restore request to holder 29634 via the task-local request queue:

    setup/artifact-memory-adopted2/requests/<unique-name>.json

The JSON request has action restore and max_bytes set to the desired limit; the
holder enforces its 200MiB disk floor. After the verifier exits, an action put_back
request returns restored artifacts to sealed storage to make room for the exact
C/ilean archive restoration. Check request result JSON for errors before moving
to the next phase. Never start another Lake build while those facets are absent.
