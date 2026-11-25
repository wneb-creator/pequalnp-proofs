# Algebraic construction notes for L-meta-9775

Status: no twenty-four-gate construction found. The ordinary star circuit has
twenty-five gates. The target has nineteen edges, no four-cycle, and minimum
vertex cover seven; regrouping ordinary stars alone cannot achieve the target.

## The suppressed cubic core

Suppress the four degree-two vertices 0,2,7,12, adding edges (8,10), (8,13),
(1,3), (3,5). The resulting ten-vertex cubic graph has fifteen edges and vertex
cover number six. Its only four-cycles are

    (1,3,5,9) and (4,10,8,13).

They are vertex-disjoint. The seven remaining edges are

    (1,13), (5,10), (3,11), (4,11), (6,11), (6,8), (6,9).

The graph census is saved in core_analysis.py/.json. It was checked by direct
enumeration, not Lean. A natural eighteen-gate circuit for the core is the OR
of these six terms:

    (1 OR 5) AND (3 OR 9)
    (10 OR 13) AND (4 OR 8)
    1 AND 13
    5 AND 10
    11 AND (3 OR 4 OR 6)
    6 AND (8 OR 9).

Their separate costs are 3,3,1,1,3,2, followed by five OR gates. Each square is
changed into a six-cycle by subdividing its two adjacent edges at one vertex.
The local square cost is three; the local six-cycle star cost is eight. Lifting
the two square gadgets independently therefore gives twenty-eight gates.
Reusing star sums with connector edges recovers the ordinary twenty-five-gate
construction, but no further saving has emerged.

## Checked nonlinear Fano seed

The existing checked L_meta_3313 contains a thirty-gate full-Fano circuit. Its
nonlinear gadget, with a=3, b=5, x=8, y=9, is

    H = (a OR y) AND (b OR x) AND (a OR b)
      = ab OR ax OR by.

It is shared between x(H OR U) and y(H OR V). Their disjunction simplifies to

    ax OR by OR xU OR yV.

The two mixed cubic terms are absorbed by ax or by. This is a legitimate
nonlinear sharing identity, but the gadget's cost exceeds the ordinary local
factorization: even with (a OR b) already present for another star, H costs
four additional gates and saves only one OR in the pair of filters. This
explains the thirty-versus-twenty-seven gap for that fixture. Deleting the two
specified incidences has not changed this balance in a useful way.

The larger checked L_meta_3679 does beat every AND-flat circuit, but its
mechanism relies on many common neighborhood elements. Its reusable value
has the form S OR xy = (S OR x) AND (S OR y), with later ORs absorbing xy.
Here each pair of neighborhoods intersects in at most one vertex, so their
common linear part is already a free input wire. That particular mechanism
does not offer a saving.

## Limits

These observations exclude only the explicit local constructions described
above. They are not a general lower bound, do not prove the posted statement
false, and do not exclude a more global nonlinear circuit of size twenty-four.

## Shared neighborhood-OR synthesis

The seven right-input neighborhood ORs currently use twelve gates. Producing
all seven with eleven AND/OR gates would immediately give the requested
twenty-four-gate circuit after seven star multipliers and six final ORs.

The script multioutput_sets.py encodes this narrower synthesis problem in
CNF. It chooses an unordered pair of earlier wires and an AND/OR operation at
each gate, and requires each target output to occur on some gate wire.
Constants and copies are omitted. This is a constructive search restriction;
no complete general lower-bound reduction is claimed from an UNSAT result.

Two semantic modes were tested:

* Seven singleton rows: a union/intersection set-lattice relaxation.
* Fourteen rows: those singletons plus the maximal negative complement of each
  target neighborhood. Monotonicity makes these rows sufficient to identify
  each target OR function exactly.

Both encodings returned SAT on the pinned ordinary twelve-gate circuit, whose
decoded outputs were then checked on all128 input assignments. Both unpinned
eleven-gate searches ended UNKNOWN after thirty seconds. Neither was UNSAT,
and neither produced a candidate circuit. The four solver logs, DIMACS files,
and JSON summaries are preserved as multioutput-*. No solver job remains
active after these capped runs.

## Elementary obstruction for the shared-OR route

The singleton-set relaxation itself needs at least twelve gates. The following
argument is pen-and-paper and has not been translated to Lean.

Take a smallest union/intersection circuit starting with the seven singleton
sets and producing all seven target sets. Remove empty-set computations,
copies, and repeated set values. The seven distinct targets have two sets of
size two and five of size three. Their pairwise intersections have size at
most one, and the two size-two targets intersect in one element.

If the circuit had at most eleven gates, at most four gates would produce
auxiliary sets. Let p count auxiliary pairs, q auxiliary triples, and l
auxiliary sets of size at least four, so p+q+l≤4.

Every target triple produced by union needs a prior auxiliary pair contained
in it: neither operand may equal the triple, and two singletons cannot make
three elements. One auxiliary pair can serve at most one target triple,
because different targets intersect in at most one element. Thus at most p
target triples are produced by union.

Every target triple produced by intersection needs two proper supersets,
both of cardinality at least four. These are auxiliary gates. One unordered
pair of set values has only one intersection, so at most l(l−1)/2 target
triples are produced this way. Consequently

    5 ≤ p + l(l−1)/2,  p+q+l ≤ 4.

The only possible case is l=4 and p=q=0. All target triples must then be
produced by intersection. Before the first large auxiliary set, only atoms
and the two target pairs can exist; their unions have size at most three
because the target pairs intersect. Neither union nor intersection can
produce that first large set. This contradiction establishes the twelve-gate
lower bound for the set relaxation, and hence for exact neighborhood-OR
implementations. It retires the proposed eleven-gate multioutput macro but
does not establish the full twenty-five-gate graph lower bound.

## Upstream9774 comparison

The newly supplied negative L_meta_9774 graph differs by replacing edge(1,9)
with edge(2,12). It is not isomorphic to the current graph: distances among its
four degree-two vertices are1,3,4,4,5,5, whereas ours are2,2,3,3,5,5.

All four current degree-two vertex deletions0,2,7,12 are isomorphic to upstream
deletion0 and to upstream deletion9. There are exactly eight matches among the
196 one-vertex-deletion comparisons. Explicit permutations are preserved in
cofactor_compare.json. The upstream proof itself uses whole-graph topology
classification rather than an explicit cofactor reduction.

## Private-weight generation and review

private_weights.py generates exact witnesses for the upstream ValidPrivate,
cost_one, and cost_two rules. There are560 independent vertex masks and36
maximal independent sets. The search gives260 strongest subset-key weights,
of which130 are irredundant. They exclude every Bplus≤9 case, leave five
Bplus≤10 masks127,1290,4757,8488,16256, and leave117 Bplus≤11 masks.

The output schema is exactly the upstream tuple(K,T,J,k,m,p,a). Geometry p
packs i,j,x,y,z in four-bit nibbles; a packs A_f in fourteen-bit fields at
shift14f. The emitted rows are in private_weights_generated.txt. Root's checked
WeightClassification.lean uses these rows and proves the unconditional23-gate
floor plus the five/117-mask classifications. The independent source review
is ../../REVIEW-weight-classification-fresh.md.

An alternate direct optimization over each actual ineligible set K, all
J⊆K, and geometry supplied by any K vertex agrees on all560 masks. Its report
is private_weights_coverage.json. Extending T to cardinality seven gives no
additional weight, including the exploratory extension that transfers a
three-point cost-two witness to a larger T by carrier monotonicity. Those
extended data files are not used by the checked WeightClassification source.

## Conditional shared-empty-wire rewrite

For a shared empty-singleton-support wire q=a AND R, the identity

    (q AND S) OR ((q OR b) AND T)
      = (a AND (R AND (S OR T))) OR (b AND T)

uses five gates on either side when R,S,T are already available. It removes
q's shared empty-support use and instead shares T, which is nonempty in the
intended neighborhood application. This may help the remaining pure-side
Bzero=1 case. By contrast, factoring two branches of the form(q OR b) AND T
costs one extra gate. Two exact other-neighborhood filters each intersect the
exceptional degree-three neighborhood in at most one point, so they cannot
alone preserve its three incident edges.

This is only a conditional local identity and a coverage observation. A full
circuit-path normalization to this form has not been proved; larger contexts
and other nonlinear terms remain a genuine missing step. Root instructed this
agent to pause additional mathematical search after the final classification
review. No jobs remain active from this agent.
