# Frozen structural research checks

These files preserve finite computational checks and mathematical research notes for L-meta-2602. They are not Lean certificates, a proof of the posted statement, or a refutation of the plane statement.

The JSON records are byte-for-byte snapshots of the files listed in `frozen-records.json`. The independent record was produced separately by the counterexample agent. `verify_structural_records.py` preserves a runnable reconstruction of the original tool-inline computations; there was no earlier on-disk script to copy. It uses only Python's standard library and performs no network access.

Run from the repository root:

    python3 results/orch/final-research/structural/verify_structural_records.py

The preservation run exited 0. Its complete output is in `validation.stdout` and `validation.stderr`; stderr is empty. It verifies all 64 rows of the two-star counterexample, all gate and OR-branch essentiality tests, both derivatives at all four target edges, and the exact clean-cover drop with and without constants. It also reproduces the matching-five OR-copy normalization on all 1024 rows and its complete prefix cover-count history.

The finite examples disprove proposed local counting invariants. They do not violate the conjectured global OR bound. The general family discussed in `structural-counting.md` is an informal mathematical argument; only its two-private-pair instance was exhaustively checked here.
