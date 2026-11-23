# A reviewed informal strengthening of the ownership bound

Status: mathematical argument reviewed independently by proof_strategy; not
kernel checked here and not a proof of the full posted statement.

Let B = sum_i (|S_i|-1) and Q = sum_i min(|S_i|-1,2). Existing Good ownership
lemmas give Q distinct AND/OR gates. A gate is Good for S when it is either
pointwise below or above OR(S), is true on at least two singleton inputs from
S, and is false at the input Z_S having exactly the variables outside S true.
Linearity makes the owner unique. Inputs and the single NOT cannot be Good.
For monotone gates, being false at Z_S implies being below OR(S).

Claim: if B > Q, any circuit with exactly one NOT has at least Q+2 gates.
Consequently the original lower bound follows whenever B-Q is at most two.
The zero-NOT case uses the existing monotone lower bound.

Suppose instead that a one-NOT circuit has at most Q+1 gates. The Q ownership
requirements and the NOT use the entire budget. Every binary gate is Good,
and each target has exactly its quota min(|S|-1,2). The NOT cannot be unused
or constant: deleting or replacing it yields a monotone circuit, which needs
B gates, so the original would need at least B+1 >= Q+2 gates.

Write the NOT as N = not h, where h is a nonconstant monotone function. Thus
N(0)=1 and N(1)=0. Take the first AND/OR gate q which effectively reads N.
Its other input p is monotone: no earlier gate depends on N. Constants and
repeated N inputs either make q constant or antitone and therefore not Good.

If q = N AND p is Good for S, its two singleton hits are also hits of p. A
primary input cannot have two such hits. If p is a prior Good gate owned by
T, then p <= OR(T), so those two distinct variables lie in both S and T.
Linearity forces T=S. Moreover q(1)=0, so q is not an exact OR output.

If q = N OR p is Good for S, q(0)=1 forces its High rather than Low condition.
The equation q(Z_S)=0 implies p(Z_S)=0 and h(Z_S)=1. If p is owned by T, its
two singleton hits must lie in S (monotonicity otherwise makes p(Z_S)=1), so
linearity again gives T=S. A primary input p=x_v is impossible: q(Z_S)=0
requires v in S; choose w in S distinct from v and evaluate at Z_S plus w.
There h remains true, p is false, and q is false, contradicting High. A false
constant is excluded by the same evaluation; a true constant contradicts
q(Z_S)=0. Finally q(0)=1 shows q is not an exact OR output.

Thus p and q are distinct Good gates for the same target S, and q is not its
output. If p is not the output either, the actual output is a third owned
gate, exceeding quota at most two. If p already is the output, it is a
monotone exact OR computation in the prefix before N is consumed. The usual
monotone predecessor count requires |S|-1 owned gates already. For |S|>=4
this alone exceeds quota two; for |S|=2 or 3 it exhausts the quota and q is an
additional owned gate. All cases contradict the budget.

The seven-variable family 02,03,0456,14,15,1236 has B=10 and Q=8. Independently,
a full-table SMT query with at most nine gates and at most one NOT was UNSAT
in 347.042 seconds. No ownership constraints were used in that query.
