# Bounded fixed-block companion diagnostic

This search fixes A on block01 with diagonal entries sqrt(2)-1 and -sqrt(2)-1, and normalizes B01=0, B02=1, B03=0. Exact first variation leaves five parameters and five residual equations. All ten coordinate-zero two-variable slices and all ten coordinate-zero three-variable slices were checked. Only the previously known rank-one-diagonal companion was found. This does not exclude other companions in the full five-variable system.

The three-variable batch ran with a 40-second CPU and 1 GiB address-space cap and completed at 11:13:39 UTC. No full five-variable Groebner computation was attempted. An initial attempt to factor the full quartic expression was interrupted; its log is retained as explore-factor-attempt01.log. The successful explore.py exports exact residual equations without that unnecessary factorization.

No diagonal-rank-two seed was reconstructed by these slices. The separate rational contraction certificate proves such a zero-edge pencil exists without fixing this exact block direction. These diagnostic slices are not used as a proof premise.
