# AND lower bounds survive free OR features

`OrEncodedAndBound.lean` proves that any input encoding preserving coordinatewise Boolean union preserves L267's negative-family bound: if M distinct negative assignments have pairwise positive unions, a monotone circuit on the encoded inputs needs at least ceil(log2 M) genuine binary AND gates. Arbitrary ORs of raw-coordinate subsets preserve union; singleton raw inputs and a false constant are included.

`SixCoreOrEncodedAndBound.lean` additionally checks all 52 six-core negative assignments and all distinct pairwise unions in Lean. Its theorem `SixCore.at_least_six_paid_ands` proves that no amount of free OR features can reduce the six-core paid AND count below six. The nine-row count228 gives eight and full-plane count704 gives ten via the generic theorem and numerical corollaries; those two finite families are not newly certified in this file.

The generic and concrete files compiled with exit0. Complete output logs and the L267 dependency build log are adjacent. Both are research artifacts importing L267 outside the final gap's allowed imports. Root and search agents were notified to discard fixed six-core3–5-AND exact-search phases.
