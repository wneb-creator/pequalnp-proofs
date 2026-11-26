Independent W(3,3) matrix obstruction audit

This is an intermediate counterexample, not a refutation of L-meta-4970. The circuit has 14,559 gates; all 40 point vertices give a cover, so the posted conclusion follows numerically from 160+40 <= 14559+1.

Geometry and witnesses

MatrixObstruction.py constructs the 40 projective points of F3^4 and the 40 totally isotropic two-dimensional subspaces for the alternating form x0*y2-x2*y0+x1*y3-x3*y1. It checks degree four, 160 incidence edges, connectedness, no four-cycle, and girth eight. An independently constructed Euler tour orients each edge once, with outdegree two at every vertex. The two outgoing neighbors Q_v give 80 distinct star supports. Their edge images partition all 160 edges into 80 two-edge classes, so witness-overlap connectivity has 80 components.

Circuit and exact output algebra

For a point a and line b, let

    R_a = OR(N(a)) OR AND(nonN(a)),   A_a = a AND R_a,
    S_b = OR(N(b)) OR AND(nonN(b)),   B_b = b AND S_b.

The output is (OR_a A_a) AND (OR_b B_b). To implement R_a without computing the pure star OR(N(a)), use the Boolean identity

    OR(N(a)) OR AND(nonN(a))
      = AND_{z in nonN(a)} OR(N(a) union {z}).

The same identity implements S_b. This identity is exact: if some neighbor is true, both sides are true; otherwise both sides say every nonneighbor is true.

For an input with active points X and active lines Y, any active target edge makes both factors true. Conversely, suppose there is no active edge and both factors are true. Choose a in X and b in Y witnessing the two factors. With no active edge, these witnesses force nonN(a) subset Y and nonN(b) subset X. Hence there can be no edge in nonN(b) times nonN(a). The script independently checks that each of the 1,440 nonincident pairs (a,b) has exactly 129 edges in this rectangle, a contradiction. Alternatively, every edge would have an endpoint in N(b) union N(a), giving at most 2*4*4=32 edges, contradicting 160. This is an algebraic proof for all inputs, not an exhaustive 2^80 truth-table claim.

Avoiding extra star ORs

For every nonneighbor z of a centre v, the script chooses t in Q_v such that z and t have no common neighbour. Such a t exists because girth eight prevents a nonneighbor from meeting both members of Q_v. Each clause is built as z OR t, then OR Q_v, then OR each of the two remaining members of N(v). Every new clause OR contains the pair z,t, so none of these pure OR supports is a star. The only other OR gates join A terms or B terms; their singleton supports are empty and they are true on the all-true input, so they are not pure disjunctions. Exact singleton-support calculations and common-neighbor intersections verify that the only pure-star OR gates are the initial 80 Q_v gates. Each edge has exactly one available serving root, so all 80 witness classes are forced; an alternative selection of serving witnesses cannot reduce their count.

All clause gates and witnesses are monochromatic at the level of raw OR reach. Every A and B term is an AND and resets raw OR reach. Thus all joins and the final output satisfy the posted T0 condition. Every gate is an actual binary AND or OR with earlier operands.

Matrix rank and bad-OR failure

On an edge-pair assignment, A_a is true exactly for edges at a, and B_b exactly for edges at b. Therefore A_a AND B_b is active on precisely the singleton edge (a,b) when incident, and on no edge-pair assignment otherwise. The active row-column graph is the connected 80-vertex incidence graph, of graphic rank 79. The 80 witness classes each label two edges, so no forest can select an edge from each of all 80 labels. This refutes the unqualified labelled-matrix/Rado inequality that would require rank at least the number of witness classes.

For the semantic bad-OR condition used in productiveOr_not_bad, only the 39 joins of A terms and 39 joins of B terms are bad: both operand singleton supports are empty. All clause OR gates have nonempty operands and monochromatic singleton support. Thus bad-OR count is 78, below cc-1=79. This refutes that separate bad-OR bound as well. It does not refute the joint inequality that can also charge unused AND capacity. The construction is not claimed to be a size-minimal circuit.

Normalization scope

Every actual circuit gate is true on at least one target edge-pair assignment; the edge-active normalizer cannot discard any gate on this criterion. Every gate other than the final output is also true on an explicitly supplied independent input. The 82 tested independent inputs are the two full palettes and {v} union nonN(v) for each vertex v. Consequently, only the final gate is semantically below the target. In particular, there is no safe AND below another AND. Both edge-active and this top-form normalization condition already hold.

Files

MatrixObstruction.py is the tracked independent constructor/checker. Running it writes independent-gq-audit.json and independent-gq-certificate.json under the supplied --output-dir; these generated files are not tracked. The first is the summary. The second records the points, lines, edges, Euler orientation, actual gates, matrix term wires, clause initial pairs, and an explicit edge in each nonedge complement rectangle. Save complete stdout and stderr separately as MatrixObstruction.log.

Reproduce with Python 3: `python3 results/swarm/MatrixObstruction.py --output-dir /tmp/oec/pnp-swarm-4970-orch/matrix-recheck`. Save complete stdout and stderr to MatrixObstruction.log. This is a finite circuit audit plus the explicit all-input algebra above, not a Lean proof of the full construction.
