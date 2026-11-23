Countermodel to using only the separate light and heavy windows

This is NOT a counterexample to L-meta-997. It violates the full correctness
premise for the heavy outputs. It shows why that premise must be used in a
combined charging proof, beyond the separate private-gate arguments.

Let q=11 and k=9. Use independent inputs P_p and Q_p for the q^2 points of
the affine plane over F_q, and controls y_0,...,y_(k-1). For each of k slopes,
take its q affine lines; write L=kq=99 for the number of lines. A line of
slope a gets light target {y_a} union {P_p : p on the line}, and heavy target
{Q_p : p on the line}. This whole target family is linear: any two distinct
sets intersect in at most one point. The two namespaces P and Q are disjoint.

Compute H=AND_j y_j and z=NOT H. This takes k gates in total. For every point,
compute e_p=(z AND P_p) OR (H AND Q_p), taking 3q^2 gates. For each line compute
E_line=OR_{p on line} e_p with q-1 gates, then light output y_a OR E_line
with one gate. Designate E_line itself as its heavy output.

Every light output is exactly its specified OR on all assignments: if H is
false it is y_a OR OR P_line; if H is true, y_a is true already. At all inputs
above Y={y_j}, each designated heavy output is exactly OR Q_line. Its
frozen-false function is H AND OR Q_line, hence globally sound for its heavy
target. The NOT is true below weight k and false at Y.

The heavy singleton outputs are wrong: E_line has singleton support P_line,
not Q_line. This is the one essential missing hypothesis.

The total gate count is k+3q^2+Lq=1461. The mixed weighted target sum is
L(k+q)=1980, and there are 2L=198 outputs. Thus the version without full
heavy correctness would require 1980<=1659, a false inequality.

No gate qualifies for the posted refund in this construction. The only
gate singleton supports equal to a whole target are the light output
supports (each contains its control y_a). Those output wires are true
throughout the heavy window, so their outside-Y supports are the whole
outside universe, not any heavy target. All other gate singleton supports
are empty, the whole input universe, or subsets of P points with no control.

The incidence and arithmetic checks are recorded in weaker_abstraction_count.txt.
The functional identities above are a mathematical argument, not a Lean check.
