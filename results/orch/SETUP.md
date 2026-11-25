Lean infrastructure setup

Pinned Lean 4.36.0 verified; executable reports commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9.
Toolchain installed at /tmp/oec/pequalnp-pilot-74/toolchain.
All nine dependencies checked out at the exact committed manifest revisions.
No tracked configuration changed. An interrupted rebuild of Mathlib dependencies occurred after generated C cleanup; this was stopped and every targeted module was then restored from the official prebuilt cache with cache get! before the successful infrastructure build.

Use these environment variables for commands:

    PATH=/tmp/oec/pequalnp-pilot-74/toolchain/bin:$PATH
    PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-74/toolchain/bin/lake
    PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-74/build-queue
    MATHLIB_CACHE_DIR=/tmp/oec/pequalnp-pilot-74/mathlib-cache
    LAKE_ARTIFACT_CACHE=false

Targeted lake exe cache get completed successfully for all 67 Mathlib roots directly required by PEqualNP.Defs: 2,480 cache modules decompressed. Full logs are cache-get-defs.stdout and cache-get-defs.stderr in task scratch.

An infrastructure-only build of +PEqualNP.Defs and checklemma is running; full logs are infrastructure-build.stdout/stderr in task scratch.

The local checker additionally imports the full Mathlib module and requires Mathlib.olean, which the targeted cache does not yet provide. Disk total is 7.9 GiB; toolchain is 3.1 GiB and targeted packages about 2.5 GiB. Full cache may exceed available disk. No checker or manifest patching is proposed.

The downloaded 607,649,028-byte official Lean archive was removed after successful extraction and version verification to reclaim space.

Disk investigation: cache artifacts are approximately 1.073 GB .olean.private, 560 MB .olean, 152 MB .ir, 82 MB .ilean, 39 MB .olean.server, plus generated C. Full Mathlib has 8,712 source modules. Generated C (241 MB) and downloaded .ltar cache archives were removed safely; compiled proof data were left unchanged.

A normal user FUSE test was attempted using official squashfuse 0.6.5, libfuse 2.9.9, and squashfs-tools 4.7.5 built in task scratch. The mount was refused: fusermount: mount failed: Operation not permitted. No bypass was attempted; toolchain files were never moved or changed. Refusal preserved in fuse-test-mount.stderr.

Selective omission of private data is not viable for the unmodified checker: Lean.Environment.importModules defaults to OLeanLevel.private, and readModuleDataPartsOfMod loads all three .olean/.olean.server/.olean.private parts. See pinned toolchain src/lean/Lean/Environment.lean lines 2443–2456 and 2808–2811.

The initial infrastructure build was stopped on root instruction (exit 130). Root subsequently authorized generic infrastructure builds while unleased; infrastructure-build2.stdout/stderr now records the resumed build.

Successful infrastructure validation: lake build +PEqualNP.Defs checklemma exited 0 using the restored targeted prebuilt cache. Logs infrastructure-build3.stdout and infrastructure-build3.stderr. Defs.olean and native checklemma executable are ready.

Full compressed cache download completed (9,117 artifacts including existing targeted cache; 458 MiB compressed). Exact expanded inventory is running one archive at a time; progress and final reports are cache-inventory-progress.json and cache-inventory-final.json.

Memory cgroup limit is 8 GiB. A standard os.memfd_create probe and own-process /proc file read succeeded; no lasting memory-backed storage has been allocated yet. At least 6.5 GiB checker budget was initially requested, so a large allocation needs root assessment against exact footprint and expected overlap.

Final infrastructure status: Defs and checklemma build passed. Root instructed infrastructure work to conclude and preserve the functioning targeted environment. No toolchain file or required targeted cache artifact was removed after restoration. No persistent memfd storage was allocated.

Full cache exact inventory: 9,117 archives; total allocated expansion 6.9609565735 GiB, loader-essential expansion 5.8902053833 GiB. Additional loader-essential artifacts beyond targeted cache need 4.3834724426 GiB. With free disk and reclaimable downloaded archives, deficit is about 3.47 GiB before safety margin.

All downloaded .ltar archives were removed after inventory to leave room for proof work. Regular targeted prebuilt artifacts remain intact. A verified compressed backup of native/editor toolchain files was also discarded without deleting or altering any original toolchain file. Exact per-file inventory and all diagnostics remain in scratch.

Completed bounded full-cache experiment and baseline restoration; see infrastructure/README.md and attached complete artifacts. Unmodified checker returned CHECKER FAULT missing Batteries.olean, before full Mathlib import or theorem judgment. Peak 5.68 GiB does not establish complete checker fit. Original targeted artifacts and toolchain restored, all cache hardlink relationships restored, both memfd daemons stopped; final Defs/checklemma --no-build freshness validation passed.
