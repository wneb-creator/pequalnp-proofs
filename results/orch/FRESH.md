# Fresh strategy preservation

`lemmas/Fresh.lean` compiled with exit0 and empty logs, and passed independent review. Its neutralReaderSupport lemma gives a support bound under explicit monotonicity and two-port suffix hypotheses. It is not a circuit extraction theorem or a proof of L-meta-2592.

The source audit found checked P9 monotone16 lower bounds in L_meta_9781 and L_meta_7567. L_meta_9818 contains both monoRoot (monotone16) and signedRoot (signed15) for the same canonical nine-input truth table used in the preserved partial. This corrects the earlier incomplete claim that only a 16-gate construction was known.

The proposed one-input-NOT argument remains informal: with one positive and one negative effective reader and a size19 budget, the P9 monotone16 floor may force neutral reader types x OR A and (!x) AND B. Constant-producing alternatives would force an extra deletion, but the circuit-level deletion/counting bridge was not completed. Under the explicit neutral-reader factorization, the checked support lemma restricts A at x=false to edge assignments or one of two exceptional alternating triples of the residual six-cycle.

A preliminary source-size audit suggested that combining both P9 certificates with the current extension would exceed512KiB without pruning/compression. Python packing estimates were exploratory; no compressed Lean certificate was compiled or claimed checked. Work stopped at lease loss.
