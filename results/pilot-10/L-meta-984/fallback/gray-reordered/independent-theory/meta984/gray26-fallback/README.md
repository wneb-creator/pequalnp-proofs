# Graph 26 Gray-route fallback

Status: finite Python audit passed. All Lean fragments here are **uncompiled**. No named proof file was edited, and no lower-bound result is claimed by this audit.

`C26GrayData984.fragment.lean` defines five short route networks and a 47-step walk. Starting with identity, the cumulative actions visit all 48 current graph automorphisms exactly once. Each network preserves the target. The simple walk applies 70 routing stages per wire across the full orbit, compared with 382 stages in the current literal-route enumeration. This count is not a measured Lean runtime speedup.

The data requires the generic `GrayWalkSuffix984.lean` from the sibling `single-not-reduction/meta984/gray-walk/` scratch directory. Its optional normalized wrapper also requires `GrayNormWalkSuffix984.lean`. For a simple-only integration, omit the final four declarations/lines defining `C26_grayNormOri` and its theorem. The named replacement fragments show the two alternatives for replacing existing `C26_ori` and `C26_ori_run`; do not append duplicate declarations. All state tables, parent data, scoring functions, and finite barrier checks remain unchanged. A complete Lean build and checker run are still required after any future integration.

The walk always advances its raw current list, even when the candidate does not improve the retained best list. This is complete Gray traversal, not greedy descent. The normalized variant retains the sorted best list and sorts each new candidate once. Both preserve `MonRun` from route validity and target fixing alone; visiting every group element is needed only to reuse the existing canonical frontier efficiently.

`validation.json` records the exact named-file hash audited, route counts, and fragment hashes. The generator checks all 32 basis positions against both current routes and compact metadata, verifies cumulative action order, and compares the old orbit, raw Gray walk, and normalized Gray walk on all 1067 stored states after deterministic varied orbit starts. Every canonical multiset agrees. Raw chosen list order agrees in 462 cases and differs in 605; ties and traversal order explain this, and no exact raw-list equality is claimed.

Reproduction uses `../gray26_fallback_generator.py`; complete stdout and stderr are saved as `../gray26-fallback-generator.stdout` and `../gray26-fallback-generator.stderr`. The generator only reads the named proof and writes this scratch folder. Root owns all integration and publication decisions.
