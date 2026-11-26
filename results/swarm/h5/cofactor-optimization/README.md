This packet preserves two checked replacements for cofactor-pool construction and their historical validation. `FastCofactorPools.lean` replaces the coordinate-mask construction with the already certified `Automorphism.fastSwapWords`; `FastDirectCofactorPools.lean` applies that pool construction to the earlier DirectMode checker.

The formal results are exact equalities to their respective checker families:

- `FastCofactorPools.check_eq`: `check i = Replay.checkNodePrefix i` for every compressed-prefix node.
- `FastDirectCofactorPools.oracle_eq` and `check_eq`: equality to `Replay.DirectMode.oracle i` and `Replay.DirectMode.checkNode i` for every DirectMode node.
- Each `closed` theorem still requires every corresponding node check to equal `true`. The packet does not supply that universal premise or a complete circuit lower bound.

All constants above are under `PEqualNP.Outside.L_meta_2373_aux.Cert18`. Both audits report only `propext`, `Classical.choice`, and `Quot.sound` recursively. The audit files and their complete stdout/stderr are included, as are successful source-hash-bound build receipts.

The compressed-prefix sources are pinned to checker revision `f59430f57ef1bacea1760fc2928a78526ac58ce7`. The DirectMode sources are pinned to `6577b13f206a0b4041e887813fb2f47584df3dd9`. Their source directory is `results/swarm/h8/certificate18/` in the fork repository. `dependency-provenance.json` lists all required local checker-module hashes: nine core modules for the first family, and those nine plus `BlockReplay`, `DirectDecode`, and `DirectReplay` for DirectMode. Each archived source and current built source was checked byte-for-byte against its git revision. The shared `lean/PEqualNP/Outside/L_meta_6581.lean` is identical at both revisions and main `cc06910dad6d57c83b639802d4c71034de91063f`. These wrappers require those dependencies on Lean's module path; this packet does not duplicate the larger checker source tree.

The final FastCofactorPools source SHA256 is `50c7fd1c1c0ae1e4b6b03a3d333b38fbd0b48cb3910f89dd978039b12ef10c3c`. Its only change from the earlier source review was a scoped `maxRecDepth 8192` before `poolList_eq`. The DirectMode wrapper SHA256 is `e063a96c12e29004c48bc6321ec59d4815a5b58913166b63a4761b3d2b872aeb`. Current successful receipts supersede the earlier source-only status notes.

The following are historical single-run observations, with an 8,000 MB Lean memory cap and one worker in every receipt. The two node292 comparisons are separate checker families. No baseline for DirectMode node5229 is included or inferred.

| Historical run | Checker revision | Elapsed seconds | Peak RSS (KiB) |
| --- | --- | ---: | ---: |
| Compressed prefix292, baseline | `f59430` | 49.199734264 | 7,916,436 |
| Compressed prefix292, cofactor wrapper | `f59430` | 36.193218873 | 7,788,624 |
| DirectMode292, baseline | `6577b13f` | 35.150999766 | 7,161,888 |
| DirectMode292, cofactor wrapper | `6577b13f` | 24.587074079 | 5,919,500 |
| DirectMode5229, cofactor wrapper | `6577b13f` | 4.142690630 | 3,241,080 |

All five benchmark modules contain `decide +kernel` examples for exactly the stated checker and node. Their source hashes match the original receipts and runner logs; all completed with exit0, no timeout, and empty stderr. The timing observations do not guarantee a repeated speedup or predict full-family replay time. Peak RSS and elapsed time are retained exactly in `receipts/`; the table rounds only elapsed time to nine decimal places. Complete stdout/stderr and runner logs are in `logs/`, including empty files.

Later frozen Packed revision `36375ce3bb56c227c81ecae98f6641800006b8c2` incorporates this cofactor-pool optimization. Its `PackedDirect.oracle` also changes the collision path. The equalities and sample checks in this packet target the earlier compressed-prefix and DirectMode predicates; they are not proofs of Packed node checks and must not be counted toward Packed range coverage. The three later Packed source hashes in the provenance file document this relationship only.

`manifest.json` pins every distributed file, checker revision, audit result, and benchmark receipt. `review.json` records the independent publication review. `validation.txt` summarizes the checks. This packet was prepared without fresh Lean or SAT runs and without modifying tracked files.
