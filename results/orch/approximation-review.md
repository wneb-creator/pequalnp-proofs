# Independent 18-gate approximation review

Reviewed at: 2026-11-25T14:14:50.032365+00:00
File: results/orch/lemmas/approximation.lean
SHA256: d3517b2d0b095ba1af784d5fb74abe72e218eda4d110696ff521167524e34f36

Verdict: PASS for an early partial checkpoint. No target-file modifications or additional Lean builds were made in this review.

Independent Python validation parsed the circuit and Boolean identity directly from the Lean source, and parsed the exact Petersen edge list from the original desk response. All 1024 inputs were evaluated.

- Exactly 18 AND/OR gates, each fan-in at most two, all references to earlier wires, output 27.
- The source function has exactly the posted 15 edges.
- Both sides of approximateBooleanIdentity agree on every assignment. Its left side equals the circuit and its right side equals the Petersen function OR the four displayed triple terms.
- The circuit differs from Petersen on exactly masks 138, 385, 521, and 770: the sets {1,3,7}, {0,7,8}, {0,3,9}, and {1,8,9} respectively. All differences are false positives.
- Each triple is independent and inclusion-maximal: adding any absent vertex creates an edge. This is why its upward-closed triple term adds only one erroneous assignment.
- approximatePetersen_misses correctly chooses the first bad triple. It is a counterexample to the candidate circuit, not to the posted gap.
- Only allowed PEqualNP.Defs import, own auxiliary namespace, no forbidden words/strings/attributes/options, normal UTF-8 source below the size limit.

The supplied complete build-05 log contains profiling output with no errors. Root reports exit 0. The proof uses kernel-backed decide and ordinary simplification, not a bypass.

Scope: a checked 18-gate approximation, not a circuit computing the exact target and not a proof or refutation of L-meta-2592. Suitable for preserving on the work branch; not a proof PR by itself.

Review program and full output: /tmp/oec/pequalnp-pilot-98/structure/review_approximation.py and review_approximation.log.
