# Bounded-subset checkpoint revision

This isolated export-only revision addresses the full-star snapshot size failure. It retains every original generator and selects active derived rows using a one-million-term budget. Candidates are ordered by increasing leading-monomial degree, then nonzero term count, then original active-basis index. The exporter takes each row that fits the remaining budget. The live basis is never changed.

Each atomic snapshot records available, retained, and omitted row and term counts. It is explicitly a partial restart generating set, not a Gröbner-basis verdict. Retaining the original generators and appending ideal consequences preserves the original ideal even when rows are omitted. The original ten-million-term import bound remains unchanged.

All nine interruption/resume controls passed with the production budget, and the same nine passed with a separate compile-time budget of two terms that forces omissions. Independent review checked all 21 provenance hashes, unchanged arithmetic core and wrapper, 108 snapshots, 186 appended ideal consequences, 42 completed or resumed bases, and the exact nine forced-budget selections and omission counts against the full counterparts.

The frozen `checkpoint-subset-engine/` archive contains 465 source, control, and metadata files; manifest SHA256 `bc8410875f1cbfdc4f430eb937a8f46c2045ce14cb6354dcce18ef66e7f91ca7`. It includes the two failed source-generation attempts and successful correction; neither failed attempt produced a solver run. Vendor engine files and native binaries are identified by provenance hashes rather than copied. The independent six-file `checkpoint-subset-review/` archive has manifest SHA256 `3fff4b1467b917a5088780000851dea810c719b677e67bd1eeeb3031b52e20fa`.

The subsequent full-star run is recorded separately. This archive reports tooling validation only.
