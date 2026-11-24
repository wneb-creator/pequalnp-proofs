# Auxiliary selected-DAG packing counterexample

This artifact disproves only the proposed inference from **individual shared-gate nondomination** to branch-vertex-disjoint four-terminal selected trees, or to three OR gates per output. It is not band-correct, does not refute the total-gate inequality, and is not a refutation of L-meta-1024. No Lean certification is claimed.

The graph uses the four concurrent Singer lines with IDs 0, 4, 10, and 12. Six independent AND4 routers feed six shared OR gates and four distinct OR sink gates. It has 18 AND gates and 10 OR gates, for 28 gates total. Four selected four-terminal trees would need 12 distinct OR branch vertices, but only 10 exist. Every one of the 504 individual shared-gate/private-terminal nondomination checks passes. All 8,192 assignments satisfy each output's global upper bound by its line OR. Each output nevertheless makes 867 errors on the 3,003 required band rows.

The stronger collective-avoidance premise fails for all 12 ordered pairs of distinct owners: deleting the other owner's entire selected DAG cuts private terminals. Therefore the example does not disprove the strengthened collective-avoidance or existential cycle-space strategies.

`selected-packing-counterexample.json` is the complete witness, including all gates and selected AND choices. `selected-packing-check.log` is the original author's complete summary. The original construction ran in an inline Python cell; `independent_validate.py` independently reconstructs every gate from the six-router description, validates the JSON and all finite checks, and also checks collective-avoidance failure. Its complete output is `independent-validation.log`.

To reproduce from this directory:

```sh
python independent_validate.py selected-packing-counterexample.json
```

Author: special_status. Independent validator and archival review: toolchain_setup. Copies were checked byte-for-byte against the reviewed scratch originals. `manifest.json` records SHA256 and byte counts for every other file; it omits itself.
