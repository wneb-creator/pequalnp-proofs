# L-meta-951 independent reduction notes

No proof or counterexample to the posted statement has been obtained here.

## Exact one-NOT exposure

Let h(x) be the monotone function read by the unique NOT gate, and expose that gate as an independent Boolean input t. Write F_i(x,t) for an output, f_i(x)=OR over S_i, and F_i^b(x)=F_i(x,b). The exact output condition is F_i(x,not h(x))=f_i(x). Monotonicity of the exposed circuit gives

- F_i^0 <= f_i <= F_i^1;
- h AND f_i <= F_i^0;
- F_i^1 <= h OR f_i.

If h(Z_i)=0 at the maximal zero input of f_i, then F_i^1(Z_i)=0. Since F_i^1 is monotone and >=f_i, this forces F_i^1=f_i globally. These are the safe targets.

For hard targets with h(Z_i)=1, the lower output G_i=F_i^0 obeys Low_i and h AND f_i <=G_i. Consequently G_i(Z_j)=1 for every other hard target j, and G_i(Z_i+e_u)=1 for u in S_i.

## A false hard-piece lower bound: seven-gate Pasch example

S_0={0,1,2}, S_1={0,3,4}, S_2={1,3,5}, S_3={2,4,5}.

Seven monotone gates:

1. t=x_1 AND x_4
2. p=x_0 OR t
3. q=x_5 OR t
4. G_0=p OR x_2
5. G_1=p OR x_3
6. G_2=q OR x_3
7. G_3=q OR x_2

Each G_i <= OR(S_i), G_i(Z_j)=1 iff i differs from j, and each G_i is true on Z_i+e_u for every u in S_i. Thus the lower-piece output circuit alone can use seven gates although sum(|S_i|-1)=8. The SAT log is pasch_piece7.log. A compatible common monotone h exists, for example the union of all upward cones above Z_i; its computation cost is not included in seven.

## A transparent family of false hard-piece lower bounds

Use distinct variables a_i, b_j, c_ij for i,j<q and S_ij={a_i,b_j,c_ij}. Define t=(AND_i a_i) OR (AND_j b_j) and G_ij=t OR c_ij. These outputs use q^2+2q-1 gates, below 2q^2 when q>=3. They satisfy the same Low, cross-Z and own-Z-plus-one conditions.

For q=3, hard_piece_counterexample.py exhaustively checks all 32768 assignments. It also constructs h as the union of all upward cones above Z_i and checks h AND OR(S_i) <=G_i and h(Z_i)=1. This is not a counterexample to L-meta-951: h's cost and the other exposed NOT branch are omitted.

## Why two reduced test models are inadequate

Singleton-only union/intersection computation need not satisfy the additive bound asymptotically. One can precompute subsets describing binary coordinates and implement finite-field line-membership predicates using both coordinate polarities. This gives O(n polylog n) set-lattice circuits for a projective-plane family whose additive demand is approximately n^(3/2). This is an asymptotic argument, not a checked concrete circuit.

Even the tests consisting only of zero, all singletons, and the maximal zero Z_i are insufficient asymptotically. For each S_i of size >=4, take four distinct elements a,b,c,d and let b_i=(x_a AND x_b) OR (x_c AND x_d). Then b_i is zero on all singletons and on Z_i, but one on every Z_j for j != i. With h=b_0 OR b_1, a single NOT separates all singleton tests from all Z tests. A cheap singleton classifier a_i can then be combined as (a_i AND not h) OR b_i, matching all these reduced tests. Full input semantics are necessary.

## Persistent support does not yield the desired per-output count

Pos(f)={u : x_u=1 implies f(x)=1 for all x}. Let h=a AND b AND c, z=not h, and output=(a AND z) OR (b AND z) OR (c AND z) OR h. This is OR(a,b,c), but only the final output has at least two persistent variables. Therefore replacing the singleton support in the monotone counting proof by Pos does not directly work.

## A potentially useful certificate observation

Dually view each target as AND(S). A true parse certificate at the minimal true input S must contain all variables of S among its positive leaves, even if it uses the one NOT literal. Otherwise its positive-leaf set T is a proper subset of S; the pre-NOT function h is monotone and h(S)=0, so h(T)=0, and the same certificate remains true at T, contradicting the target. Mixing certificates for different targets can fail only when the common h becomes true on their mixed positive-leaf assignment. Every h=1 extension of a target's minimal input then needs a positive certificate avoiding NOT. A complete amortized argument would have to use both kinds of certificates.
