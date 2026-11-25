# L-meta-1031 search checkpoint, round 4

All included runs have finished. External SAT/UNSAT results remain untrusted computations rather than Lean certificates. No full-gap counterexample was found. Earlier snapshots retain unchanged logs omitted here; all current sources and graph inputs are included.

## Multioutput matching construction

`counter_multi_sat.py` generalizes total-size synthesis to a graph output plus several OR outputs, all allowed at any gate. It uses every input assignment for the six-input matching experiment, so no representative-row assumption enters that test. Every gate must feed a later gate or one of the required outputs. Graph automorphisms must preserve the set of auxiliary OR subsets. Distinct earlier operands, nonconstant/distinct functions and sorted topological gate order use the same minimum-circuit normalization caveats as earlier snapshots. A fixed13-gate positive control produces all five requested outputs, independently verified by full64-row evaluation.

The graph is a three-edge matching; auxiliary outputs are the four even-parity transversal triple ORs. Size11 is externally UNSAT in135.6seconds. Size12 is UNKNOWN at240seconds. A hypothetical size11 construction would extend to Petersen19. A hypothetical size12 construction, after attaching four star centers and one private leaf to each, would yield24 gates on a14-vertex,19-edge graph with minimum cover7 and canonical star cost25. Those are search implications, not established circuits. The leaf-extended graph input is preserved.

## Bounded free-cone cost

`counter_count_budget.py` adds a bound on the number of binary gates needed to naively expand all nonempty free cones. For k charged gates there are2k+1 cones; their total selected source count minus(2k+1) is the charged budget for the other basis. SAT therefore supplies a valid total-cost upper bound. This bound can overcount shared free subexpressions, so UNSAT would exclude only this restricted route. The C5 control finds4OR+3AND with no truth-table errors. Partially subdividedK5 (retain matching01,23; subdivide the eight other edges) with16OR+at most5AND returns UNKNOWN at240seconds.

## AND-count checks and new minimum pruning

Count-only C7 with at most3AND is externally UNSAT0.008seconds; C9 with at most4AND is UNSAT0.201seconds. Fano incidence with at most5AND is UNSAT4.36seconds.

`counter_count_minimum.py --minimum` is an optional strengthening for a genuinely minimum AND count. At each AND value v, form the free OR r of all earlier source wires u whose true rows are contained in those of v. The gate must have a positive edge row outside r. Otherwise replacing v by r preserves all positive edge rows, can only decrease every maximal-independent-set negative row, and removes one AND. A minimum AND gate must also be read by a later cone or final output. These constraints have received independent mathematical and source review. They do not preserve total gate count, and exact-k UNSAT is not an at-most-k result unless every smaller k has been ruled out. C5 with3AND is a SAT control, fully verified. The current Fano6 minimum-pruned run is excluded from this frozen snapshot because it was still running.

No generated CNFs or solver binaries are included. Sources, exact inputs, full solver stdout/stderr, all relevant witnesses, and the one initial multioutput source-error log are preserved.
