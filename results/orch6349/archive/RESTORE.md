Lossless archive of the canonical L-meta-6349 SAT run.

The solver returned UNSATISFIABLE with exit code 20. This archive is not a kernel verification of the lower bound.

Preserve the seven canonical6349.lrat.zst.part-NNN files in manifest order, raw-lrat-archive-manifest.json, inputs-manifest.json, and all six files in inputs/. The unsplit canonical6349.lrat.zst is redundant once all seven chunks are retained.

Concatenate the seven chunks in numeric order and zstd-decompress the resulting stream. The recovered canonical6349.lrat must have 1,179,072,387 bytes and SHA-256 e465869c21d7e38b4a37db6a6b15f227ed5242a754f3832054c0c79060859b81.

The compression script uses 1 MiB Python I/O buffers and a single-thread zstd process at level 10. The measured codec peak RSS was 27,648 KiB. It verifies the full decompressed digest and separately verifies that the concatenated chunk digest equals the complete compressed stream digest.
