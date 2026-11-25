# Genuine cache migration checkpoint

The parent approved removal of exactly four reproducible link-time archives: libLean.a, libStd.a, libInit.a, and libLake.a, totaling 401,426,002 bytes. Their original SHA256 hashes were verified before removal. All other static support archives, executable binaries, shared libraries, public/private/server oleans, runtime IR, and original disk cache artifacts were preserved. The full inventory also lists the untouched archives.

The transfer preserved all 88,125 newly fetched official-cache artifacts. It copied 105 files totaling 327,634,943 bytes to ordinary disk, checking each copy against its original SHA256 before atomic replacement. New holders opened the remaining 88,020 original sealed inodes read-only; a complete reconciliation checked every size, hash record, old/new inode identity, and seal bit mask. Only after that check passed was the old loader stopped normally. Every artifact type remains available. The compressed JSONL manifest preserves complete per-artifact metadata; it is not a compiled binary.

The new cache remains live through the memory-cache-transferred holder service. Do not stop it while Lean uses its symlinks. Ten storage-holder processes are implementation processes, not additional AI subagents. The post-transfer disk reserve was 120,377,344 bytes and memory-backed storage was 4,044,984,320 bytes including page overhead.

The unchanged cached native-checker build passed in 5.04 seconds. CheckLemma.lean, tools/check-lean.mjs, and the checklemma executable retained their original hashes. No native relink was needed; any future relink would first require restoration of the four official toolchain archives. No Mathlib source was built and no checker source, configuration, or preload behavior was modified.

This checkpoint makes no new official-checker verdict or mathematical claim. The first checker run documented in the parent directory still ended without a verdict when the external memory guard stopped it. No further full checker run had started when this migration checkpoint was written.
