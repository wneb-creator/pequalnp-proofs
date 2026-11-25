# Completed bounded full-star checkpoint runs

Both finite-field runs ended at their wall limits with UNKNOWN and no final basis. Neither result proves the presence or absence of a complex solution. The reviewed exporter preserves all original generators and a bounded subset of active polynomial consequences; these are partial restart generating sets.

| Run | Wall seconds | Peak RSS KiB | Completed rounds | Latest snapshot round | Derived rows / terms |
| --- | --- | --- | --- | --- | --- |
| grouped-subset-r2-final | 1800.101571 | 2074172 | 267 | 261 | 425 / 998869 |
| star-center-r1-final | 900.056260 | 1317984 | 201 | 198 | 418 / 999920 |

Each seven-file archive contains complete stdout/stderr and wrapper logs, launch and result metadata, and the compressed latest snapshot with verified decompression hash. No solver was restarted after either cap.

- `grouped-subset-r2-final/sha256.json`: `3a5b7a268865520ef6754466e8a3e076887c39d77ab7258e227eac63013e2ac5`.
- `star-center-r1-final/sha256.json`: `0fc8f15c836ef0784ff61cec6a3eb1509df3126e90e801d6fe63ce655f58a3f6`.

The preservation helper is `preserve_completed_checkpoint.py`. Its metadata explicitly distinguishes the completed bounded run from the partial algebraic checkpoint. Source/input/provenance and independent reviews are in the earlier checkpoint and center-input archives.
