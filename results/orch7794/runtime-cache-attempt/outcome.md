# Bounded official-runtime-cache attempt

One bounded attempt provisioned the full official runtime closure, then ran the unchanged official checker under the requested 7.5 GiB memory guard. Preparation completed before its 16:50 UTC deadline. The exact inventory verified all 9,117 cached module entries and required runtime facets, including Batteries.

Official archives were fetched using hashes from the pinned Cache.Hashing implementation. New artifacts were SHA256-verified after placement; RAM-backed artifacts were genuine regular memfd files, sealed against writes/growth/shrinkage, with cache-path symlinks. Four holder processes respected the 16,384-descriptor per-process limit. Independent cross-process opening, hashing, and private writable mmap succeeded. No checker, proof, definitions, or cached-artifact contents were substituted.

Preparation first found that Python omitted symbolic fcntl seal constants. It stopped before creating RAM symlinks; constants were then read from installed Linux headers and directly capability-tested. The same bounded preparation continued with explicit digest exceptions and complete runtime-facet inventory. Both versions and all transport/manifest logs are preserved.

The final preparation placed 1,205,796,448 bytes on disk and 3,182,912,016 bytes in sealed memfds. Memory before the checker was about 3.6 GiB. Root renewed its lease at 16:38:43 UTC, then authorized the checker trigger.

The official checker passed its verifier-build and proof/Defs-build stages. During the verifier stage after both build stages passed, the monitor sampled 8,127,700,992 bytes (about 7.57 GiB), crossing its 7.5 GiB trigger. It sent SIGTERM to the checker process group and closed the artifact holders. No OOM kill occurred: cgroup memory.events recorded oom=0 and oom_kill=0.

The final official diagnostic was:

    CHECKER FAULT: the verifier ended without a verdict (exit null).

There was no ACCEPTED or REJECTED proof verdict. Complete stdout/stderr are preserved. The orchestration helper exited 0 after cleanup; it did not separately record the Node child return code on the memory-abort path. The checker source's printed fault path exits 3, but that child exit status was not independently logged.

After stopping this route, all attempt-owned RAM symlinks were removed. Only newly created optional runtime files were deleted, after checksum verification, and all fifteen link-time static archives were restored byte-for-byte from verified gzip backups. About 1.1 GiB disk space was available afterward. Final documented read-only verification:

    lake --no-build build checklemma PEqualNP.Outside.L_meta_7794 PEqualNP.Defs

returned exit 0: all 5,153 targets up-to-date. No Mathlib source build ran. No further RAM or mount attempt was made.
