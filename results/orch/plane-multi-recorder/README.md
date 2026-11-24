# Separate recording of multi-dirty overapproximations

This is a recording-only delta from the independently reviewed plane-balanced-multi source. Mutation, fitness, RNG calls, baseline construction and valid-witness verification are unchanged. It preserves useful positive-complete INVALID repair seeds even when a simpler singleton-leaking state has a better overall error count.

At sampled256step intervals, candidates of size≤124 accepting every positive edge are physically expanded. A recorded dirty AND must fire on at leastone positive and one negative basis test, and its two operand signatures must be incomparable on the complete25342test basis. This is an explicit diagnostic definition on the test basis, not a structural-minimality theorem. The recorder retains the best negative-error count separately for exactly2,exactly3,or at least4 such ANDs. One latest file per category is overwritten when its count improves.

Before saving, the recorder checks exact physical size and output signature, then independently scalar-replays every complete-basis input. Each saved artifact contains all mistaken inputs and is explicitly INVALID. This hook neither declares a witness nor changes the existing fully verified witness path.

Forced-hook calibration replayed the already-reviewed123gate2dirty and108gate3dirty fixtures from plane-balanced-multi/, with exactly15746and24875false-positive cases. The recorded gates/error lists matched those fixtures. Full calibration and independent incremental review are included. Planned same-slot command: python3 SearchStochasticPlaneBalancedMultiRecord.py --seed <integer> --seconds 1200 --output-dir <scratch>.
