Lean infrastructure setup

Pinned Lean 4.36.0 verified; executable reports commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9.
Toolchain installed at /tmp/oec/pequalnp-pilot-74/toolchain.
All nine dependencies checked out at the exact committed manifest revisions.
No tracked configuration changed. No Mathlib source build performed.

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
