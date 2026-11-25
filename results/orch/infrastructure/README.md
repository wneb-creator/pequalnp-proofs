Infrastructure experiment for pilot 74

Final state: ordinary pinned Lean 4.36.0 toolchain and targeted prebuilt cache restored. lake --no-build build +PEqualNP.Defs checklemma passed after restoration. Both memory-backed cache daemons were stopped only after every preexisting path and original artifact-cache hardlink was restored and byte-verified.

The unmodified checker was run against lean/PEqualNP/Outside/L_meta_2448.lean and the posted statement. It returned CHECKER FAULT because Batteries.olean was absent. It never completed the full Mathlib import and did not judge the main theorem. The observed peak was 6,100,291,584 bytes (5.68 GiB), below the 7.2 GiB watchdog limit; this does not demonstrate that the complete checker fits the 8 GiB memory limit.

The official whole-Mathlib cache inventory contains 9,117 archives: 6.961 GiB expanded allocation, of which 5.890 GiB is loader data. Sealed, byte-verified anonymous memory files allowed the loader cache to be installed while respecting disk limits. Ordinary FUSE mounting had been refused earlier; no mount bypass was attempted.

Original targeted artifacts had duplicate hardlinks in the task-owned build queue cache. That retained disk blocks after the first memory migration. These exact duplicate links were identified by cache hashes, stable inode checks and SHA-256 comparison, removed during the experiment, and restored afterward.

Dependency-root cache fetch returned 415 archives with 9 reported misses. Their private-import closure required further uncached Batteries wrappers. Fifty-five pinned non-Mathlib dependency wrappers compiled during the bounded attempt; it stopped at its retry bound. Last missing-module diagnostic was Batteries.Data.MLList.Heartbeats, which subsequently compiled; the unresolved checker-level aggregate remained Batteries.olean. No project proof source or checker source was modified for this experiment.

Restoration removed 35,025 experiment-added paths, restored 1,167 original private artifacts and corresponding hardlinks, restored and compared the compressed native/editor toolchain components, and stopped the daemons. Complete logs, scripts, exact inventory, hashes and restoration metadata are attached here.

Runtime commands still use PATH=/tmp/oec/pequalnp-pilot-74/toolchain/bin:$PATH and PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-74/toolchain/bin/lake.
