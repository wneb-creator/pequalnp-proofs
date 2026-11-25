# Anonymous cache feasibility

A small proof of concept used fifteen genuine official Batteries root artifacts (92487 bytes). Cache key: `6433765366249283`; downloaded archive SHA256: `e30931782c611152119118b127ac22c0350334f15961edf6dabecbb9fa9121d7`. Their exact bytes were placed in Linux memfd files, sealed against modification, and exposed only through symlinks under the allowed scratch directory. A separate process mmap-read and hash-verified every artifact. Pinned Lean read the root and reported the next genuinely missing dependency, `Batteries.Classes.Cast.olean`. This is not a complete library import or a checker verdict.

No named files outside repo/scratch were written, no existing cache/source files were removed or replaced, no checker/library code changed, and no Mathlib source was compiled. All scripts, official bytes, per-artifact hashes, full logs, and detailed analysis remain in `/tmp/oec/pequalnp-pilot-96/memfd-poc/`.

A mixed layout is plausible only after heavy workloads finish: keep small/public artifacts on disk and place selected large missing private/IR artifacts in sealed memfd, with strict disk, memory, and descriptor budgets. Current memory usage was 7.9–8.15 GB against an 8.59 GB limit, including 3.79 GB anonymous memory; adding several GB now would be unsafe. The descriptor limit is 16384. Default private imports require all exported/server/private olean parts, so `.olean.server` must remain. All sizing estimates are provisional.

Root requested that scaling stop while the full posted theorem is missing and proof elaborations use most RAM. No large download or allocation was attempted. The unmodified full-gap checker has no verdict.
