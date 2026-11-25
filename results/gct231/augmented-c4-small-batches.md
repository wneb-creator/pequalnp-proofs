# Smaller pair batches on the augmented C4 finite-field systems

The already reviewed augmented systems were rerun over F1009 with pair-selection parameters 1 and 4, each under a ten-second/1-GiB cap and one thread. All four completed with unit basis `[1]`. This experiment supplies no evidence that smaller batches improve the rational computations: they used more rounds and larger matrices than the earlier parameter-32 runs.

| Case | Parameter | Printed pair rounds | Wall seconds | Largest column count |
| --- | --- | --- | --- | --- |
| 2 | 1 | 1117 | 0.770005 | 6817 |
| 2 | 4 | 297 | 0.265719 | 3800 |
| 2 | 32 | 43 | 0.066001 | 1743 |
| 3 | 1 | 1011 | 0.470172 | 3894 |
| 3 | 4 | 306 | 0.216106 | 2700 |
| 3 | 32 | 47 | 0.065419 | 2381 |

All runs reached printed degree 14. These are finite-field timing and order observations, not predictions or proofs about rational elimination. The parameter-32 complete records remain in `augmented-c4-cases23/`; the 19-file `augmented-c4-small-batches/` archive contains the four new complete records and the comparison script/output. Manifest SHA256: `1da49c356b698efec19b98ac2003649dc3672275b1ead8037c4a98a55bce0c11`.
