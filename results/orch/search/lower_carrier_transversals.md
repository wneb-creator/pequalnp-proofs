# Carrier tails and the remaining quadratic-normalization obstruction

Mathematical notes from the lower-bound strategy, 2026-11-25, 10:42--11:12 UTC.
These arguments have not been formalized in Lean. They do not establish the
assigned lower bound.

## A full-function statement for a carrier tail

Fix a vertex v in one shore of a bipartite graph. Its full carrier consists of
all wires true on the singleton v. List every carrier exit gate in topological
order as g1,...,gt. An exit is necessarily AND, with exactly one carrier operand
A_i and one noncarrier operand B_i. The output is not a carrier for a graph
function. Consequently every path carrying dependence on v eventually crosses
an exit.

For a neighbor w, compare the singleton w with the positive pair {v,w}. Let j be
the first exit whose value changes. Such an exit exists, since otherwise a
topological induction on noncarrier wires would make the two outputs equal.
Every earlier exit has its singleton-w value. The noncarrier operand B_j is
therefore already true on the singleton w.

Now take any assignment X containing only vertices in the shore of v, and
suppose every baseline carrier operand A_i(X,0) is true for i>=j. The circuit on
X union {w} must be true. To prove this, compare with {v,w} and induct on
noncarrier wires. At inputs the new values dominate the old ones. At exits
i<j, monotonicity from the singleton w gives domination. At every exit i>=j,
the carrier operand is already true on X, while its noncarrier operand is
handled by the induction. Other noncarrier gates are handled directly by
monotonicity.

Thus, writing a_i(X)=A_i(X,0), one has the full-function inequality

    AND over i>=j of a_i(X) <= OR over p in N(w) of X_p.

The neighborhood OR has a unique maximal false assignment, its complement.
Evaluating the displayed inequality there shows that some i>=j has

    a_i(X) <= OR over p in N(w) of X_p

for every point assignment X. This is stronger than merely saying that its
singleton support lies in N(w). In particular the last physical carrier exit
has this property for every neighbor whose first changing exit is that last
one. The argument uses all carrier exits, not only selected joint-meeting
gates.

There remains an important obstacle: a baseline function can lie below several
neighborhood ORs through v while equaling v only on singletons. Its other
minimal true inputs can be large point sets meeting all those neighborhoods.
Deleting those higher-degree terms without increasing a shared circuit is the
unproved step.

## Transversals of the remaining meeting gates

In this section the graph is the incidence graph of a projective plane.

Suppose all carrier exits are dedicated consumers h_u of ineligible neighbors,
plus meeting gates g1,...,gt. Partition the remaining neighbors among nonempty
sets B_i so that every w in B_i is carried by the non-v operand of g_i. Select
one w_i from each B_i and put W={w_1,...,w_t}. The assignment M_W selects W and
all opposite-shore vertices outside the union of their neighborhoods.

All selected w_i and every ineligible neighbor u lie in the pencil at v.
Distinct members of this pencil intersect only at v. Therefore every dedicated
h_u has its v-carrier operand true on M_W, regardless of t: any other vertex of
N(u) lies outside the union of the selected neighborhoods. No condition t<q+1
is needed here.

Every g_i has its non-v operand true on M_W. If all its v-carrier operands were
also true, noncarrier topological induction would make adding v irrelevant to
the output. This contradicts the graph function. Hence some A_i rejects M_W.
Its same-shore singleton support is contained in the union of the selected
neighborhoods, and its opposite-shore singleton support avoids W.

There is a useful necessary finite covering condition. Project the same-shore
singleton labels of A_i other than v onto the unique pencil line through v;
call this footprint T_i. Every transversal W must contain some T_i (and avoid
the corresponding opposite-shore singleton labels). Under a uniformly random
transversal of disjoint blocks B_j, the probability of T_i being contained is
zero if it lies outside their union or contains two values in one block;
otherwise it is the product of 1/|B_j| over its occupied blocks. The sum of these
probabilities is at least one. This is a necessary condition only and is not a
gate-count bound.

## Unique use does not justify deleting a dirty singleton rectangle

Use point variables p,x and line variables a,b,c. The circuit

    g = p AND (a OR b)
    h = a OR (x AND c)
    output = (g AND h) OR (x AND b)

computes exactly p*a OR x*b. All extra terms in its expansion contain one of
these two edges. The raw input p appears only in g. Nevertheless replacing g
by p produces a false positive at p=x=c=1, a=b=0. Thus rowwise
meet-irreducibility does not establish a valid local deletion in the full
circuit. This circuit is nonleast (seven gates versus three), so it does not
refute a global leastness/rewiring claim. Its raw bypass and useless pair gate
also mean it is not a counterexample to stronger rectangle-cut hypotheses.

## Scope of a pure-rectangle cut theorem

For any bipartite edge function on m>=1 point and n>=1 line inputs, replace every
point input p by p AND OR(all lines), and every line input l by OR(all points)
AND l. Leave the original circuit as an arbitrary AND/OR postprocessor of
these terms. On an input with both shores nonempty the terms equal the raw
inputs. If a shore is empty all terms are zero, as is the edge function.
Therefore this transformation preserves the full function and costs

    (m-1)+(n-1)+m+n = 2m+2n-2

additional gates. Every cut term is a singleton rectangle. If every vertex has
an opposite-shore nonneighbor, as in the present projective planes, all these
rectangles are dirty. Thus an
unrestricted sharp lower bound for arbitrary monotone postprocessing of such
rectangle cuts would already imply a superlinear lower bound for unrestricted
bipartite graph circuits, even after subtracting this linear overhead. The
exception for dirty singleton rectangles on both orientations is essential to
the current cut theorem.

## Search topology justified by the established normal form

In a least strong-normal circuit, no dirty gate can consume a below-output
wire: AND is excluded by the no-below-output operand property, and OR by strong
OR normality. Each clean AND has dirty operands. Liveness makes every clean
AND reach the output through clean ORs. If there are k clean AND roots, the
root-versus-top-OR counting lemma gives at least k-1 original top OR gates.
One may therefore reorder all dirty gates first, then all k roots, then an OR
chain of k-1 gates, without increasing size.

Global sorting by greatest operand index must not be imposed additionally
without proof: an early-operand clean root postponed past later dirty gates can
violate that ordering. Sorting within the separate blocks is the safer scope.

If the dirty prefix contains no AND, all roots are products of variable ORs.
Cleanliness and C4-freeness make them stars, and their top OR is read-1. Hence
an under-canonical search target must contain a dirty-prefix AND. This cut is
not imposed on a canonical positive control.

## Literature context actually read

The project page https://pequalnp.com/papers/note-1, dated 24 November 2026,
was opened on 25 November 2026. Its prior-work section reports that the explicit
superlinear monotone graph-function problem was open in Jukna 2005 Problem 24,
and distinguishes general monotone Boolean circuits from the multilinear,
tropical and arithmetic bipartite C4-free lower bounds discussed in Jukna 2014
Remark 10. The original papers were not opened under this job's host restriction.
This is context from that page, not a claim that the historical status remains
unchanged in all later literature.
