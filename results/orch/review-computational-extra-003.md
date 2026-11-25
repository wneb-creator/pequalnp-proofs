# Independent extended nine-edge search review

Verdict: PASS for preserving these six files. N4 mask51863 at gate budget11 remains unresolved; the retained clean12-gate construction supplies only an upper bound.

The complete CaDiCaL log records 1200 seconds and exit0, with no SAT or UNSAT verdict. The trial record reports UNKNOWN after1200.02095 seconds, matching metadata. This is a completed limited search with no lower-bound conclusion, distinct from earlier interrupted runs. Both stderr files are empty.

The retained xz CNF independently decompresses to3492507bytes, SHA-2563312ecc1ccdd7baf2b4d169f3a2a7ba40a21eec7d505778ca97f5f8fa877a919. Its DIMACS header11397variables/138763clauses matches all clause terminators and literal indices. Compressed and raw hashes/sizes agree with metadata and the generation record. The recorded encoder source hash is the previously reviewed unchanged source. Metadata accurately preserves UNKNOWN and does not claim a new minimum or Lean result.

Selected public files contain no credentials or live lease identifiers. Mutable colored-lift and C8 dirty-optimum runs are outside this review.

| File | Bytes | SHA-256 |
|---|---:|---|
| results/orch/lemmas/n4-nine-eleven-1200-trial.stdout | 850 | f3af72d262d1a46ad41637208e213277ec7e30c7cd795dd4dc2190a4ce0b0a06 |
| results/orch/lemmas/n4-nine-eleven-1200-trial.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/n4-nine-eleven-1200-cadical.stdout | 59907 | 734972eb61b5cb7bf6105744573fa1055cb07a90605f89ac1be4be80baf76b1f |
| results/orch/lemmas/n4-nine-eleven-1200-cadical.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_n4_nine_extended.json | 1378 | d41e048f0761479cb8881f1859dad926895820e777c41900480cb18c0cf46204 |
| results/orch/certificates/n4-nine-eleven.cnf.xz | 336672 | 2092424b78e1f86abd5ed33bd24734650a4aa624dbdf3d1d1cc75b4b59b90d4a |

Reviewer: status_review. No proof or solver source was modified.
