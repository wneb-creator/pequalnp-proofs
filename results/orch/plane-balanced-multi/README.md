# Full-plane balanced multi-cluster search

This is the exact posted42-input105-edge plane function, with target124 and known125gate baseline. It adapts the reviewed Complement12 balanced source to the existing independently audited complete basis of105positive edge pairs and25,237maximal negative assignments (25,342cases total). A target candidate must pass every complete-basis scalar case, then a Lean certificate; none is present here.

Heuristic negative errors are normalized by105/25237 and restart multipliers0.25,0.5,1,2,4. In addition to the prior penalties, occasional1/scale and2/scale penalties let one residual negative error outweigh a gate. The archive uses weighted error at most52.5 and retains active-AND diversity. These affect exploration only; the exact correctness flag and witness verifier are unchanged.

The Multi source extends the one-cluster baseline hook by partitioning disjoint point sets into one,two,or three clusters, each containing two to four points. Each selected cluster becomes a biclique on its points and their neighbor union. Every posted positive edge remains accepted, but new negative cases are accepted; these starts are explicitly INVALID. Their exact additive gate saving is the sum over clusters of(point-degree sum minus neighbor-union size). They begin with one,two,or three dirty ANDs. Valid mixed126/shared128/matching131 and redundant starts remain available.

The included INVALID fixtures have124/123/108gates and1/2/3dirty ANDs respectively, with9644/15746/24875wrong complete-basis cases. They are search seeds, not refutations. Author calibration checked96physical baselines and202736scalarcases across all four validity/dirty-count classes. Independent calibration checked96physical baselines and101368scalarcases. The earlier one-cluster author calibration checked608208scalarcases; full logs are preserved.

Planned command: python3 SearchStochasticPlaneBalancedMulti.py --seed <integer> --seconds 1200 --output-dir <scratch>. It replaces the current global-core worker at its cap, using the sameCPU slot. This heuristic establishes no lower bound, and a timeout or failed search proves no impossibility.
