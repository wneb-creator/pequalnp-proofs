# Independent review: edge robustness, conditional count wrapper, search artifacts

Reviewed UTC: 2026-11-25T14:25:53.518000+00:00
Reviewer: lean_setup
Verdict: PASS for preservation as partial proof/search evidence, not a full posted proof.

- Source: results/orch/lemmas/Partial.lean
  SHA256: 6a2d633512feadbbcf0ed09f923c2e2fe8ddd66b5cf79fb5f093d6b421a3653e
  Lines: 160
- Source: /tmp/oec/pequalnp-pilot-103/CountCheck.lean
  SHA256: 98bae5a7d19ccadb3196158f8b73015f01729f4ee6d2354634892da9315956d2
  Lines: 39

Lean review:

- Independently enumerated all vertex subsets: every subset of at least five vertices spans at least two Petersen edges, and deleting any one edge leaves independence number at most four. The edge-AND implication follows directly from membership in the disjunction's fifteen edges.
- CountCheck partitions all gates into NOT and non-NOT operations. Its conclusions are explicitly conditional on the assumed non-NOT floor of seventeen. It does not establish that floor. The at-most-two-NOT conclusion correctly also assumes total size at most nineteen.
- The sources use permitted imports/namespaces and ordinary proofs with scoped limit options. No placeholders, added axioms, unsafe/native evaluation, forbidden commands, root qualifier, strings, attributes, custom data types, or instances were found.
- Partial's two supplied final logs are empty; author reports exit zero. CountCheck was reported compiled by root. No heavy Lean test was rerun.

Search artifact review:

- All fifteen archived files are UTF-8 source/data/log/documentation; no executable binary is present. No credential/private-key patterns were detected. Source inspection finds no network access or credential use.
- All eight entries in SHA256SUMS match their archived files.
- Independently evaluated both 21-gate ten-input reference circuits and the 17-gate nine-input cofactor reference over every input. They compute their stated targets and each contains exactly one unused NOT; these are encoder validation examples, not counterexamples to the target bounds.
- near19 remains an incorrect candidate. The 969 neighborhood result records and log report only searches allowing one chosen triple of gates to change. README correctly limits their UNSAT claims and explicitly says broader searches timed out or were interrupted.
- Search programs evaluate any reported witness over the full truth table before printing WITNESS. The optional distinct-function restriction, all-gates-used restriction, fixed-first-operation cases, local neighborhoods, and ordered mode are search restrictions; no general impossibility follows from them without a separate completeness argument. README does not claim such a general result.
- Reuse caveat: source-index bit vectors have fixed width five. The archived jobs stay within that range; arbitrary larger --gates values require increasing that width and revalidating the encoder.

These artifacts can be preserved on the work branch. A final proof PR still requires exactly one added Lean file, the exact posted theorem, and successful checker acceptance.
