# Fresh analysis of the free-unary Petersen gap

Partial only: this note does not prove L-meta-1884 and gives no counterexample.

## Fanout-one reduction at the eighteen-gate boundary

The checked Unary17Check result restricts a candidate to at most one paid NOT. Normalize a hypothetical least candidate by deleting dead gates, constants, copies, invalid reads, and ignored inputs of NOT gates. Merge primary wires denoting the same literal when counting their reader occurrences. These normalizations and the following incidence count still require integration into a formal circuit theorem.

Suppose every one of the nine nonzero variables has at least two reader occurrences. The value of x0 must also reach the output, since Petersen depends essentially on it.

With one paid NOT and at most seventeen binary gates there are at most 35 incoming gate incidences. Connectedness requires at least 17 incidences from nonoutput internal gates, leaving at most 18 primary incidences. The nine other variables already consume 18, leaving none for x0. This is impossible.

With no paid NOT and eighteen binary gates there are 36 incoming incidences. At least 17 are internal, leaving at most 19 primary incidences. Thus equality is forced: the nine nonzero variables each occur twice, precisely one x0 rail occurs once, and every internal nonoutput gate has fanout one. The circuit unfolds to a 19-leaf formula. If the sole x0 rail is negative, its output is antitone in x0, contrary to essential increasing dependence. Thus the sole rail is positive, the free negative rail is unused, and the ordinary monotone KW leaf lower bound 20 excludes this formula.

Consequently every remaining candidate has a nonzero variable v with one reader. If that reader were the sole paid NOT, v would occur only negatively in an otherwise AND/OR circuit, again contradicting essential monotonicity. Its reader must therefore be AND or OR.

Setting v to that gate's controlling value collapses the gate and at least one downstream reader. The gate cannot itself be the output, because neither Petersen cofactor in v is constant. Obtaining a third deletion, or enough additional cofactor lower bound, remains the central missing step.

## The sole-reader semantic split

Write the sole reader as AND(v,H) or OR(v,H). H cannot depend on v. All dependence of the computed function on v factors through this reader.

For AND(v,H), H must be true on each of the three singleton neighbors of v. Otherwise the circuit cannot distinguish the negative singleton {u} from the positive edge {u,v}.

For OR(v,H), suppose H is monotone when x0 is fixed. This holds if H has no paid NOT in its ancestry, even when the input bank contains an arbitrary unary function of x0. Then H rejects zero and every singleton.

For any w distinct from v, Petersen has u adjacent to v such that u is nonzero, u differs from w, and u is not adjacent to w. If H were true on singleton w, adding u would keep x0 fixed and preserve H=true. The sole reader would then equal true both on the negative assignment {w,u} and on the positive assignment {v,w,u}; all other inputs to the suffix would be unchanged. This contradicts correctness. The singleton v case reduces to zero by H's independence of v, and zero is bounded by any nonzero singleton.

The finite witness property and the semantic singleton/zero rejection statement were separately formalized by lean_setup in lemmas/SoleOrPartner.lean, with a reported Lean exit0. The step relating its abstract factorization hypothesis to an arbitrary normalized circuit is still needed.

## Exceptional pairs caused by the free negative x0 rail

The same argument nearly excludes nonedge pairs accepted by H. Let S be a nonedge pair accepted by H.

- S cannot contain v, since H would then already accept the other singleton.
- S cannot meet N(v), since then v is pivotal on S itself while OR(v,H) stays true.
- Each vertex of S can neighbor at most one member of N(v), by C4-freeness.
- If some nonzero u in N(v) is not adjacent to either vertex of S, adding u preserves x0 and negativity, but makes v pivotal. This again contradicts H=true.

Therefore v must be adjacent to0 and S must cover the two vertices of N(v) other than0. There are exactly six possible combinations:

| v | S |
|---|---|
| 1 | {3,9} or {7,8} |
| 4 | {2,6} or {7,8} |
| 5 | {2,6} or {3,9} |

In each case S avoids N(0), so S union {0} is independent, and adding v makes the function true. Hence H must be false on S union {0}. Thus an accepted nonedge pair forces H to decrease as x0 changes from false to true. Every proof of H(S) must use the free negative x0 rail as well as both vertices of S, so H needs at least two distinct AND gates.

This classification was independently formalized by lean_setup in lemmas/PairLocalization.lean, with a reported Lean exit0. It has not yet produced the required third gate deletion. If v is not adjacent to0, H rejects every nonedge pair, leaving only possible unsafe independent minterms of size at least three.

## Signed-leaf LP diagnostic

I extended the root's fifteen-by-fifteen KW rectangle LP by allowing the single extra negative label not-x0. Its separating rectangles have positive rows avoiding0 and negative columns containing0. Enumerating the 31 nonempty subsets of those five columns gives a small LP.

The optimum found was 301/16 = 18.8125. The saved rational weights were checked exactly against all rectangle families and have maximum rectangle weight1, so they give only a 19-leaf lower bound. This is weaker than needed to exclude arbitrary 19-leaf signed formulas. The fanout count above avoids this issue: its 19-leaf equality case has only one x0 rail, and monotonicity forces that rail to be positive.

Artifacts: kw_negative0_lp.py and kw_negative0_lp.json. The LP is an exploratory mathematical certificate, not a Lean proof or a circuit lower bound.

## Equality pattern suggested by the sharp cofactor bound

Root's strengthened zero-paid-NOT argument uses the x0=false cofactor lower bound16 and charges both x0 rails, giving at least18 gates. An equality analysis may reduce a candidate to the two rail readers

    a = x0 OR H,
    b = (NOT x0) AND K.

The following conditional observation is useful even when one rail-reader gate lies in the other's ancestry. Let H0 be H evaluated in the x0=false cofactor. It is a monotone function of the other nine variables. Assuming the raw x0 and negative x0 rails have no other readers, correctness implies

    H0 AND (x1 OR x4 OR x5) <= f0,

where f0 is the Petersen function with x0=false.

To see this, compare an x0=false assignment z having H0(z)=true and some selected i in {1,4,5} to the assignment with x0=true and only i selected among the other coordinates. The OR rail-reader is true in both assignments. The negative rail-reader is at least its value zero in the latter assignment. Every other raw coordinate only increases. Induction through the monotone circuit therefore makes the former output at least the latter positive output. This comparison does not require H and K to be mutually independent; H0 is the cofactor value.

Consequences: H0 rejects zero, all singleton assignments, and all nonedge pairs. If H0 accepts an independent set S, then S cannot contain any of {1,4,5}, and S must meet all three opposite pairs {2,6}, {3,9}, {7,8}. The six remaining vertices induce C6, whose only independent triples are its two alternating triads. Thus these two triads are the only possible falsepositive independent assignments of H0. On the maximal-negative test columns they correspond to the two maximum independent4-sets containing0.

If the resulting sixteen-gate cofactor circuit is least, H0 must also be true on some edge pair. Otherwise setting its output to false loses no prime positive pair; monotonicity then preserves the entire quadratic output function, and constant propagation removes at least one gate. The sharp unresolved configuration is therefore a productive cofactor wire carrying both an edge pair and an unsafe alternating triad. The existing cofactor lower-bound certificate proves the sixteen-gate floor but does not classify its equality cases.

The auxiliary cofactor search has a 24-row exact monotone encoding. Relabel old vertex i+1 as new input i. The twelve edges are

    (0,1),(1,2),(2,3),(0,5),(1,6),(2,7),
    (3,8),(4,6),(6,8),(8,5),(5,7),(7,4).

The three neighbors of deleted0 have new mask25, and the two alternating triads have masks100 and386. The twelve maximal independent masks are

    25,52,58,69,100,104,138,201,274,277,385,386.

Only100 and386 avoid mask25. Thus the constraint H0 AND OR(A)<=f0 is exactly H0=false on the other ten maximal-negative rows. Require H0=true on386 and on at least one edge row. Fixing386 rather than allowing either triad loses no case: swapping the three opposite pairs {1,5},{2,8},{6,7}, while fixing {0,3,4}, is an automorphism exchanging100 and386. Counterexample agent received this encoding for a root-authorized auxiliary search; no outcome is claimed here.
