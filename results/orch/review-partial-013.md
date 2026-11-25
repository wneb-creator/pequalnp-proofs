# Independent checkpoint 013 review

Verdict: PASS for preservation of checked partial results on the job branch, conditional on the parent's named build completing successfully. This is not an accepted proof of L-meta-3451; the required full theorem is absent.

Exact main: lean/PEqualNP/Outside/L_meta_3451.lean, 3662 lines, 168031 bytes, SHA-256 4a0687272d92a47f45a32d19edf41cf9ecee5a89eb59af23dfc54e0b471f7a2f. Independently verified that the bytes equal the previous committed main plus the reviewed sensitivity/minimality fragment, with only its namespace shortened inside the existing auxiliary namespace, and the explicit partial-results comment. The mathematical source review is in review-global-sensitive-min.md.

The exact merged file contains no forbidden root namespace spelling, string literals, nonsimp attributes, sorry, native_decide, unsafe implementation, or new axiom. Imports and scoped resource options are unchanged. No declaration claims the full posted theorem. The namespace integration is exact. Authored-file git diff --check passes. Raw external stdout/stderr bytes are retained separately without whitespace editing.

The new certificate preservation set is outside the prior 89-file computational manifest:

| File | Bytes | SHA-256 |
|---|---:|---|
| results/orch/certificates/c6-seven-metadata.json | 1841 | 26143bca5a8eb0e2113b4ff442eab66a67d981b99581f6113a0de6adc3072a1b |
| results/orch/certificates/c6-seven.cnf.xz | 116344 | cd6200448307093977ee2825e0cfd3f46eae4a30a0077af2b7729c9dd40c5ec9 |
| results/orch/certificates/c6-seven.lrat.xz | 1983428 | aff3e92cda056b0be4ca6619eb504233e1412d896dd9449ee5079e3c1c4619ec |

Both xz streams independently decompress and all compressed/uncompressed hashes and lengths match metadata. The CNF has 4732 variables and 43446 clauses, with all literal indices and terminators matching the header. Its raw length is 935887 bytes and SHA-256 56c41b184795411d49abb37c69011a9c3fa77570e5c619f171ee6fa3b562dfcf. The binary LRAT begins with an addition record; raw length 4840472 bytes and SHA-256 a06ed2d393d473c7189f3c55d0e96bf2bf0610dda2f11ee524cbb0e3f94613bf. This is an integrity/header review, not LRAT proof verification or Lean certification. Metadata correctly states external UNSAT evidence and contains no credentials or live lease identifiers.

Reviewer: status_review. Proof and solver sources were not edited.
