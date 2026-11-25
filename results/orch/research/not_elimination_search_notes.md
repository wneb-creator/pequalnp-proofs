# Input-NOT exploratory synthesis

These Python searches enumerate semantic DAG states with unordered pairs of distinct available signals and binary AND/OR. They compare positive input wires against the same wires plus a free negation of input 0. Each newly computed nonconstant signal not already available creates the next state; state deduplication sorts available truth tables. Constants/copies are omitted because they cannot improve a minimum circuit for a nonconstant output. All truth table rows are evaluated exactly with Python integers.

Results: on four variables through six binary gates, both bases reach 164 nonconstant monotone functions, with identical minimum binary cost for each. On five variables through five gates, both reach 1727; through six, both reach 3587, again with identical minimum costs. The final search visits 896104 positive states and 3261710 signed states at depth five before evaluating every sixth-gate extension.

These are computation results, not Lean-certified lower bounds. They cover only the stated input/gate limits, only one negated primary input supplied free, and scalar outputs. They establish no conclusion about the ten-input Petersen function or negation of an internal wire. Full stdout/stderr logs and exact scripts are adjacent. Runtime in the logs is monotonic wall time.
