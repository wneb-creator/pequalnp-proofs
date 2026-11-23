# Independent review of fp3_strategy preserved results

Reviewer: prior_routes. Scope: 16 standalone Lean sources in fp3_strategy directories for L-lib-123 (8), L-meta-952 (3), L-meta-921 (1), L-meta-971 (1), and L-meta-997 (3). The separately pushed fresh/SmallWindow subtree is excluded from this review.

Verdict: PASS. No blocking source, validation, dependency, or theorem-scope issue found. Requested documentation corrections are resolved; no Lean source changed.

## Integrity and compilation evidence

Every archived source matches its manifest SHA-256 and line count and is byte-identical to the corresponding original scratch source. Every recorded relocated compilation has exit code 0, the expected source command and workdir, and a complete stdout/stderr log whose size and SHA-256 match the manifest. All 16 logs are empty. I verified the existing compilation records rather than rerunning unchanged sources. Reviewed source hashes are recorded separately in fp3_archive_review_sources.json.

All imports are Mathlib or PEqualNP.Defs. Supporting proof dependencies are inlined in the standalone combined files. No unlisted Lean source appears at the top level of the five reviewed directories. No admissions, new axiom declarations, native_decide, unsafe declarations, external implementations, kernel-bypass options, or credential-shaped content were found. Standard Classical choice use and decide +kernel are ordinary checked proof mechanisms, not new axioms or native_decide.

## Mathematical scope

- L-lib-123 establishes semantic stack/alternation/replay characterizations and explicitly conditional resource arithmetic. GrammarBound applies to binary concatenation grammars only. No generic trace compression or FP3 exponent saving is claimed.
- L-meta-952 proves conditional monotone cofactors and incidence restrictions. It does not claim general size-preserving one-NOT elimination.
- L-meta-921 gives singleton-cut/cofactor and finite-set context restrictions; it does not claim the missing global 39-gate count or a complete circuit deletion transformation.
- L-meta-971's five-vertex path example refutes a proposed cumulative safe-meet potential, not the Heawood 27-gate statement.
- L-meta-997's refund injection is exact; BoundedCase retains both extra assumptions (positive |y| and disjoint piece sizes at most |y|+1). WeightedFrontier counts each shared paid wire once. The general compensation step is still explicitly unproved.

I inspected the theorem definitions/statements and their central arguments against these claims, including the mate-free stack challenge, typed three-block parsing, cofactor replacements, refund injection, and bounded-case assembly. Duplicated evaluation/counting dependencies are already checked in the source files they inline. The reports clearly distinguish mathematical plans and restricted finite searches from checked Lean results. This review does not certify omitted SAT searches or establish a posted-statement checker verdict.

## Documentation correction resolved

The renamed report references now point to the preserved files. All eleven research reports include a historical archive note explaining pre-publication no-repository-mutation statements and scratch-path provenance. I verified the corrected destinations and confirmed no stale renamed-report references remain. All sixteen Lean source hashes and compiler-log hashes remain unchanged.

## Final staged snapshot

Exactly 58 staged files in the five reviewed top-level fp3_strategy folders match the reviewed worktree bytes. The separately published fresh subtree is excluded. The staged whitespace check passed. Complete per-file hashes and digest construction are recorded in fp3_archive_review_bundle.json.

Pathset SHA-256: 0e2ced07e9898dde0a29522471d0f8612ab1b05d6d54eb7b6c98e739f5d04301

Content-list SHA-256: 0a835ea841275d875592268da653acbd667936f4c6607fd58380b4bda152279f
