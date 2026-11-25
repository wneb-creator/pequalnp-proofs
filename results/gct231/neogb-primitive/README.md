# Primitive logical-row exact-QQ adapter

This isolated adapter periodically divides an entire logical row by its positive integer content. After every eight pivot eliminations, the gcd includes all already-retained sparse coefficients and all unconsumed dense coefficients. Consumed dense entries are excluded because those columns have been eliminated. Every nontrivial division is recorded as an exact rational scale `1/gcd`, so the unchanged compact replay checks the resulting output identities.

Independent review **PASS**, preserved in `review/`: direct polynomial-state replay of all controls, a separate check of all 51 row-zero certificate steps, equality of all established output polynomials with the previous compact adapter, and 7,488 signed/zero/boundary cases of the extracted C helper under ASan and UBSan. The row-zero trace contains 29 additional scale records and the same 43 output records. All three toy controls and the row-zero unit control passed.

This snapshot contains the source delta, complete build/control logs, inputs/outputs/traces/certificates, and independent review. It contains no engine binaries or vendor tree. The prior exact engine provenance and license are in `../neogb-trace/`; the compact reference format is in `../neogb-compact/`.

A separately authorized fixed-C4 quadratic+cubic chart run is active outside this frozen snapshot. No chart verdict or new Lean theorem is asserted here.
