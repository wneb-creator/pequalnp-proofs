# Literal-route fallback

Status: UNCOMPILED scratch-only fallback. No named proof file was edited, and no Lean command was run for these artifacts.

`LiteralRoutes984.fragment.lean` supplies a generic orientation over an explicit list of route-stage lists. Its Boolean check requires each route to satisfy `validStages` and fix the exact target. The preservation proof uses only the existing `orbitActions_run` and `routeStages_run` lemmas.

`C0.fragment.lean` through `C30.fragment.lean` contain the data and proposed correctness declarations for each graph; `all31.fragment.lean` concatenates them. Each action list retains precisely the original automorphism indices 1 through group-1 in the original order. Identity index0 is excluded as in the existing implementation. Zero-mask stages are removed because the existing `step 0 d w` definition returns w. Thus every action map remains unchanged, including on words outside the compact bit width.

The fallback should replace the orientation implementation, not the certificate state data or its ordering. Per-graph definitions use new names (`C26_literalRoutes`, `C26_literalOri`, and so on) so the fragments can be tested beside the existing implementation in a separate scratch candidate. Existing packed route declarations can remain until integration determines whether anything else references them.

The generator `../literal_routes_generator.py` compares every stage against the packed route codes in the current named source. It then verifies all32 basis bits for each of196 original automorphisms, agrees with the independent permutation metadata, preserves the target and padding, and emits165 nonidentity actions. `validation.json` records the exact named-source hash and counts; each graph JSON records metadata hashes and original action indices.

Literal stage-pair payload is11990bytes, compared with13896bytes for the packed32bit hexadecimal payload. Full generated fragments, including proposed proof declarations, total24938bytes. There are1097 remaining nonzero stages. These are source-size and operation-count facts, not runtime measurements.

An independent agent reviewed the generic preservation argument and parsed all31 actual generated Lean literal lists, confirming that all165 routes and their order exactly equal the current packed routes with zero stages removed. No Lean acceptance is claimed until a future compile succeeds.
