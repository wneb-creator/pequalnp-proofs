# Fresh mono19 first-OR-edge computational exclusion

This is the complete fresh run of the independently reviewed proof-trace exporter, with no imported memo states. It excludes a positive 18-gate continuation from the ten Petersen inputs plus their first adjacent OR, in the exact copied-root search model. The root finished with `found 0` and exit 0 after 2,065,513 visits, 727.391 search seconds and 730.874465 wall seconds. Every one of its eleven initial copy branches completed.

This is a completed computation and a replayable proof-data export, not a full Lean certificate or the original posted theorem. The count-vector recurrence, finite checker and several concrete leaves are checked separately; the complete exported dependency graph has not been instantiated in Lean. The stronger monotone nine-variable lower bound 16 is used by the ten single-zero cofactor profiles.

The exact source SHA256 is b66739a56db722c470d02767c15b3e812f727546268d706df4a14c4442e8c021. Source, full log, supervisor status, all bank diagnostics, full rectangle trace, completed memo and immutable 26-record V3 rectangle matrix file are preserved. The command and exact timestamps are in the status file. No later V4 matrices are used.

The full proof trace is 2,462,656,845 bytes. To reconstruct it, decompress the nineteen files in the order listed in proof-chunks.json and concatenate their bytes. Chunk boundaries may split JSON lines. That file binds each compressed chunk, each decompressed chunk and the complete concatenated stream by size and SHA256. Each compressed part is below 11 MB. The complete proof stream contains every node, closure entry/provenance, omitted candidate witness, copy child, canonical action, completed memo reference and final signal dictionary. The rectangle trace and completed memo are separately gzip compressed with their original and compressed hashes in manifest.json.

The manifest uses direct file entries for source/logs/chunks and logical original-file entries with original_* and gzip_* fields for the two whole compressed streams. This research archive is not part of a proposed single-file proof PR.
