# Quadratic-shadow route: obstruction and local consequence

Recorded 2026-11-25. This concerns a proposed auxiliary generalization, **not a refutation of L-meta-1896**.

## The universal C4-free shadow bound is false

The proposed general statement was: if a monotone AND/OR circuit is false on singleton inputs and its accepted inputs of weight two form the edges of a C4-free graph E, then it needs at least |E|-1 OR gates, regardless of its behavior on larger inputs.

Here is a concrete counterexample using the affine plane over the prime field F7. Inputs are x[a,b] and y[s,t] for a,b,s,t in F7: 49 point inputs and 49 nonvertical-line inputs. The graph joins point (a,b) to line (s,t) iff b = s*a+t. It has 49*7=343 edges. It is C4-free: two distinct nonvertical affine lines have at most one common point (equal slopes give none; different slopes determine a uniquely).

Define the following monotone wires. Every displayed multi-input OR is implemented by a binary chain; all products are binary AND gates.

- A[a] = OR_b x[a,b], and B[b] = OR_a x[a,b].
- S[s] = OR_t y[s,t], and T[t] = OR_s y[s,t].
- W[r] = OR_(a*s=r) (A[a] AND S[s]).
- D[t] = OR_r (W[r] AND B[r+t]).
- F = OR_t (T[t] AND D[t]).

The coordinate-indicator stage uses 4*7*(7-1)=168 OR gates. Across all W[r], there are 49 product terms and seven nonempty OR groups, so this stage uses 49-7=42 OR gates. The D stage uses 7*(7-1)=42 OR gates. The final stage uses six OR gates. Total: **258 OR gates**, strictly less than 343-1=342. There are also 49+49+7=105 AND gates, for 363 gates total. All gates have fan-in two.

On one point input and one line input, each coordinate indicator has its ordinary one-hot meaning, so F is true exactly when b=s*a+t. If all inputs come from one half, every product needed to cross the two halves is false, so singleton inputs and same-half pairs are false. Thus the quadratic minterms are exactly the 343 graph edges. Higher-degree behavior is unrestricted, as required by the proposed auxiliary statement.

A complete explicit circuit was generated and evaluated in parallel bitsets on all 1+98+binomial(98,2)=4852 inputs of weight at most two. The evaluator confirms 343 accepted rows, 258 OR gates, 105 AND gates, and maximum common-neighbor count one. This is an ordinary Python finite check accompanying the algebraic argument, **not a Lean-checked result**. No claim about the actual held gap follows from it.

Artifacts:
- /tmp/oec/pequalnp-pilot-62/quadratic_shadow.py
- /tmp/oec/pequalnp-pilot-62/quadratic-shadow-f7-circuit.json
- /tmp/oec/pequalnp-pilot-62/quadratic-shadow-check.log

## Why the actual generic negative tests matter at order three

The same coordinate-marginal construction already fails a genuine generic negative row in PG(2,3). In affine coordinates, take

P = {(0,0),(1,0),(0,1)},
Y = {the vertical line x=2, the line y=2, the line y=2*x+2, the line at infinity}.

No point of P lies on a line of Y. The two sides are maximal complements: Y is all lines avoiding P, and P is all points avoiding Y. P is not collinear and Y is not concurrent, so this is exactly a generic maximal false input of the same geometric kind used by L-meta-1896.

Yet the coordinate projections of P contain a=1 and b=1 separately. The marginal circuit combines them into the absent point (1,1). The active line y=2*x+2 passes through this phantom point, so the circuit outputs true. This calculation was checked against all 13 normalized homogeneous points and lines over F3 in the same Python script.

A precise consequence: a function satisfying the full positive and generic-negative tests cannot factor solely through the separate affine-coordinate projections of the selected points and lines (even if the inputs at infinity are additionally retained). Indeed P and P union {(1,1)} have identical separate point-coordinate projections, but the former together with Y must be false, while the latter must be true by monotonicity and the incident pair ((1,1), y=2*x+2).

This suggests preserving point/line correlation as a local invariant. It does **not** justify forbidding every intermediate marginal OR: a larger circuit may recover or cross-check information downstream. A 51-OR counting proof still needs to quantify that recovery cost.

No external theorem or unverified numerical source is used here.

Script SHA256: 35a9b805feb83416393253558407e468a14e06061b623d2bf3bf01fc7f4a0db2
Circuit JSON SHA256: 02c2543787d7901d241426ebde738e16b2a2e49e2cea7db79e63a2fe93c78c12


## Exact smallest false positives of the F7 circuit

A second independent finite audit evaluated the saved 363-gate circuit on all 152096 weight-three assignments using parallel integer bitsets. The result agrees with its coordinate-marginal formula on every row. Since the previous check established correctness on all weights zero through two, every false-positive triple below is a minimal accepted assignment.

There are exactly 9702 false-positive triples with two points and one line, exactly 9702 with one point and two lines, and zero same-side triples. In fact the circuit is false on every all-point or all-line input, of arbitrary size, because its formula needs both halves nonempty.

For two points (a,b),(a',b') and one line y=s*x+t, with no actual incidence, acceptance means that the line contains one of the crossed points (a,b') or (a',b). Necessarily a differs from a', b differs from b', and s is nonzero. There are 2*choose(7,2)^2= 882 unordered point pairs with both coordinates different. Each has 2*(7-1)-1= 11 distinct avoiding lines through its crossed points. The single overlap is the line joining those two crossed points. Thus 882*11 = 9702.

The dual count follows similarly: two lines with different slopes and different intercepts determine two crossed slope/intercept lines. Their nonzero-x points contribute eleven avoiding points in total. There are 882 such unordered line pairs.

Lexicographically first examples in the saved input numbering are:

- indices (0,8,57): points(0,0),(1,1), line y=x+1;
- indices (7,50,56): point(1,0), lines y=1 and y=x.

These are mixed nonedge errors. The permitted collinear-point and concurrent-line triples of the actual target play no role in this auxiliary counterexample.

## A triple-correct uniform obstruction and its smallest error

Proof_routes proposed ANDing three copies of the marginal circuit after the incidence-preserving affine changes

x'=x+c, y'=y+c*x, for c=0,1,2.

A line y=s*x+t becomes slope s+c and intercept t-(s+c)*c. For a two-point/one-line independent triple, each of the two off-diagonal point-coordinate combinations can create an incidence for at most one c: its equation is

c*(a_j-a_i) = s*a_i+t-b_j.

If the coefficient vanishes, the proposed crossing is a real point and the assumed nonincidence rules out a solution. Dually, each of the two off-diagonal line-coordinate combinations for a one-point/two-line triple satisfies

c*(s_i-s_j) = b-s_i*a-t_j,

again with at most one solution or none. Thus at most two values of c can accept any mixed nonedge triple. Three distinct values reject all of them. Same-side inputs remain false. This algebra was independently verified on every mixed triple for q=3,5,7: 648,15000,115248 rows respectively, with no error. Together with the automatic same-side case these account for 816,19600,152096 full weight-three inputs.

The three-copy construction nevertheless has a minimal false-positive quartet for every odd prime q:

P={(0,1),(1,0)}, L={y=x,y=2*x}.

There is no actual point-line incidence. For every c, combine x'=c from the first point and y'=c from the second point into phantom point(c,c). Combine slope2+c from y=2*x and intercept-(1+c)*c from y=x. This phantom line passes through the phantom point because

(2+c)*c-(1+c)*c = c.

Consequently even the AND of every member of this entire shear family accepts the quartet. Every proper subset is rejected by the three-copy construction, so its smallest false-positive weight is exactly four. Direct finite checks verified the quartet and every proper triple for q=3,5,7,17,19.

For q=3 the quartet is contained in the generic maximal false row

P={(0,1),(0,2),(1,0)}, Y={x=2,y=x,y=2*x,line at infinity}.

Enumeration of all 13 projective points and all 13 lines confirms that these are mutual maximal avoiding sets, that P is not collinear, and that Y is not concurrent. Thus the shear family still fails an actual kind of generic negative test used by L-meta-1896.

The unoptimized three-copy construction at q=19 uses 6210 ORs for 6859 quadratic edges, below 6858. The zero-product optimization in the next paragraph improves the per-copy count to 6*q^2-7*q+2. It therefore yields a uniform counterexample even at q=17: 4851 ORs for 4913 edges, below 4912. At q=19 the optimized count is 6105. These are counterexamples to a proposed general C4-free bound strengthened by all weight-three negative tests; they do not refute the posted order-three statement.

## The zero-product optimization and a 48-OR pair-correct PG3 circuit

Regroup the affine formula as OR_r(W_r AND E_r), where E_r=OR_t(B_(r+t) AND T_t). E0 forces both some affine point and some nonvertical line to be selected. Hence A_any=B_any=true and S_any=T_any=true under E0. Since multiplication has no zero divisors,

W0=(A0 AND S_any) OR (S0 AND A_any),

so W0 AND E0=(A0 OR S0) AND E0 exactly, on every input. This E0 is a new grouping and should not be confused with the earlier t-indexed D_t.

The optimized affine cost is 4*q*(q-1) coordinate ORs, 1+(q-1)*(q-2) product-coordinate ORs, q*(q-1) equality-mask ORs, and q-1 final ORs, totaling 6*q^2-7*q+2. At q=3 this is 35.

The full PG3 incidence shadow adds four exact blocks: affine points versus vertical lines(2 ORs), infinity-slope points versus nonvertical lines(2), vertical infinity point versus vertical lines(2), and line-at-infinity versus its four points(3). Joining the affine block and these four blocks uses 4 further ORs, giving 35+2+2+2+3+4=48. The additional blocks are globally exact incidence functions. The affine block still has mixed false-positive triples, such as points(0,0),(1,1) and line y=x+1, so this 48-OR construction is only a pair-correct control.

## Reproducible artifacts for this follow-up

These are ordinary Python/algebra checks, with no new Lean execution or machine-checked target claim.

- `results/orch/quadratic-shadow-f7-circuit.json`: SHA256 02c2543787d7901d241426ebde738e16b2a2e49e2cea7db79e63a2fe93c78c12.
- `results/orch/quadratic-shadow-minimal-errors.py`: SHA256 e41104a503760f6b45818615222b7a3d3b83292a9a7c333e307a36f32bdf3213.
- `results/orch/quadratic-shadow-minimal-errors.log`: SHA256 0d2f256ff36a768afafb1ac23a20119cfcfedb646b4e383a8530a1e94d4aa982; complete stdout/stderr, exit 0.
