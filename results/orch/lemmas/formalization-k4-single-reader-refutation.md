Strict-live subdivided-K4 derivative obstruction

The file combines constructive-k4-equality.lean with the independently compiled generic unique-reader derivative bridge, using one copy of the accepted L_meta_6659 definitions and lemmas under PEqualNP.Outside.L_meta_1479.K4Equality.

The final theorem k4_minimum_no_double_quiet states that any strict, live 10-input binary DAG computing subdivided-K4 adjacency with at most 15 gates cannot have both formal first derivatives quiet on an incident pair. The equality theorem makes every original K4 vertex have a unique-reader path to the output. At the neighboring singleton, output is false; inserting that vertex makes output true. The formal derivative therefore propagates true along the chain. Every edge has an original vertex, giving one nonquiet orientation.

This is a checked obstruction for the exact StrictLive DAG model and the full combined source compiled successfully, exit 0. It is not a refutation of L-meta-1479. A trace-preserving reduction from arbitrary 14-input circuits to this 10-input strict-live model remains unproved; semantic normalization alone is insufficient because deleting duplicate-input AND gates can change formal derivatives.
