# Completed first-OR-edge rectangle-data census

This archive covers all five linked rectangle traces supplied by library_route. Trace paths and SHA256 values are pinned in traces.json. The final resumed search reported no circuit; this archive is only a data consistency audit and a size estimate, not a kernel proof of the search or the original gap.

All recorded rectangle cuts preserve duplicate root occurrences. The census validates sample-matrix load records against published loaderV3, equal lengths, exact integer cost sums, strict margins and stable repeated costs. It then deduplicates transformed sample matrices by coefficient array. All62,349 cost profiles were recomputed exactly with integer subset enumeration. Same-cap containment gives30,974 maximal profiles; no floating-point arithmetic enters that audit.

The three .json.gz files contain complete original JSON data, compressed only for archival storage. profile-literals.txt gives the uncompiled grouped packed-mask data. encoding-estimate.json measures sorted-delta Rice encodings with and without shared mask dictionaries; these are size estimates only, not implemented Lean decoders.

occurrence-summary.json adds exact repeated-work counts from a second pass:21,837,973 root-cost occurrences and305,558,342 subset leaves without sharing. A proof that reconstructs masks from already-present signal data can omit explicit profile masks, but kernel replay cost and memory sharing remain untested.

Dependencies are ONLY original13 matrices and loaderV1–V3 (IDs1001–1026). Later matrices are not used by these traces.

## Replaying from preserved files

All matrix dependencies and the exact integer oracle used by compression are now included in this directory. Python3 with NumPy and SciPy is required (the prepared job environment has both). `trace-map.json` maps the five original scratch names to compressed traces in sibling `../search/` archives, pinning both compressed and uncompressed SHA256 values. `traces.json` retains original provenance paths, but those paths are not needed for replay.

From this directory, run the following with a fresh output directory:

```sh
python census_rectangle_traces.py /tmp/oec/pequalnp-pilot-87/census-replay
```

The default trace list uses the archive-relative map, reads gzip directly, and verifies each uncompressed trace hash. Explicit trace arguments remain supported. The original62,349-profile dataset can also be audited without scanning traces: copy weights.json into a fresh scratch directory, decompress profiles.json.gz there as profiles.json, then run `python compress_rectangle_profiles.py <that-directory>`. Its integer oracle is the bundled tailor_bank_rectangles.py; its LP entry point is not invoked during auditing.
