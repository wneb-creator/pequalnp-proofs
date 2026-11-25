Follow-up after the independently audited15:53 checkpoint

The unrestricted16gate cofactor/H auxiliary, with fresh and productive gates, returned UNKNOWN after119.09 seconds. Full diagnostics are archived.

An attempted prefix-A run was interrupted during validation-fixture reconciliation; it has no completed solver verdict. The prefix-V24gate positive fixture computes the cofactor and satisfies the H condition, but its final H guard is false on every prime edge, so productive-gate validation correctly rejects it. This is a nonminimal validation fixture, not a counterexample or an encoding failure. The underlying full512-row function/H checks passed independently.

Both proposed four-gate H prefixes are structurally nonminimal anyway: M=(b∨c)∧(b∨d)=b∨cd, where cd is a nonedge. On every positive edge assignment M=b, and globally b≤M. Replacing M by primary b preserves all positive edges and only decreases the output elsewhere, deleting one gate even if M is shared. This was reported to root and fresh_proof.

This motivates the new primary-bypass minimality clause. For a gate and a primary input, forbid equality on all positive specification rows together with primary≤gate on every negative row. Bypassing the gate would otherwise preserve positive outputs and could only decrease negative outputs. Exact cofactor specification then preserves full correctness. This rule is a necessary condition for a minimum realization; root has now checked that every1884 candidate has at least18 gates.

Direct target search now uses the checked equality-case rail restrictions: positive input0 occurs exactly once, in an OR; free negative input10 occurs exactly once, in an AND. No other rail references occur. With all11 primary labels present, a connected18gate binary DAG has at most19 primary-input occurrences, forcing some x1..x9 to occur once. The marked0 stabilizer gives neighbor1 and distance-two2 cases. The first case is currently running in scratch only. Freshness and primary-bypass constraints are enabled.

Validation of the new constraints passed: a31gate positive fixture obeying both rail restrictions is SAT and correct on all1024 rows; the20gate baseline is correctly rejected by the rail restrictions. The baseline remains SAT with freshness, primary-bypass constraints, SAT preset, and one-occurrence input3; requiring exactly one occurrence of input1 is correctly UNSAT.

Fixed-baseline extension check: the genuine16gate cofactor circuit has no wire covering even two of the neighbor-A singletons. Exhaustive truth-vector enumeration also found no extension by at most two AND/OR/NOT gates, even permitting free x0,¬x0,and constants. All1024 rows were used. This only excludes extensions of that fixed baseline.
