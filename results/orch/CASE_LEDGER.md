# Canonical equality-case ledger

Updated 2026-11-25 11:27 UTC. All sets use the accepted edgeList labeling; point labels agree with the posted cyclic labeling and line labels are negated modulo seven. The full target remains open. The listed zero-surplus bounds alone do not rule out a quiet edge with two eligible endpoints.

| Eligible inputs | Canonical ineligible set | Complete no-double-quiet result | Current component |
|---|---|---|---|
| 7 | {0,1,2,3,4,5,6} | Standalone compiled | Unique-reader chains |
| 8 | {0,1,2,3,4,5} | Standalone compiled | Saturated carrier count and linearity |
| 9 | {0,1,2,3,4} | Open | Missing-mask saturation and protected inputs; algebraic route owns case |
| 9 | {0,1,2,5,11} | Open | Mixed-cap missing-mask saturation |
| 10 | {0,1,2,3} | Open | Noncollinear-triple and missing-mask counts |
| 10 | {0,1,2,5} | Open | Cap missing-mask saturation and protected inputs |
| 10 | {0,1,2,11} | Open | Triangle-consumption structure |
| 10 | {0,1,11,12} | Open | Bplus at least13; Bzero at most1 |
| 11 | {0,1,2} | Open | Bzero=0 |
| 11 | {0,1,3} | Open | Bzero=0 from strengthened cofactor loss |
| 11 | {0,1,11} | Open | Bplus at least13; Bzero at most1 |
| 12 | {0,1} | Open | Bzero=0 |
| 12 | {0,9} | Open | Bzero=0 |
| 13 | {0} | Open | Bzero=0 |
| 14 | empty | Open | Bzero=0; exactly two consuming positions per label; every AND output has empty singleton support |

Additional cross-case result: if all seven line-neighborhood masks occur, the new false-wire surplus argument forces every point to be ineligible at27 gates and hence rules out double quiet. The standalone build and independent composition review passed.

Integration: the preferred conditional exact-statement bridge passes standalone compilation and independent review. It trims after the actual output and deletes only zero-fanout internal gates, transporting both traces through an injective wire renaming; no ordinary lower-bound/minimality premise is needed. Cyclic relabeling and canonicalization are explicit. The universal/canonical no-double-quiet theorem remains an explicit hypothesis.
