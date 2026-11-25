Recorded 2026-11-25T16:47:49.338584+00:00

# L-meta-1884 structural analysis

Status: no complete proof or refutation. No new Lean declaration for this gap was produced by this agent. Existing L-meta-4970 checked components are separate and do not establish this statement.

## Exact task and established dependencies

The input has ten mapped original variables plus one free unary function of variable 0. The hard normalized form is the ten original inputs plus free complement of input 0, with at most eighteen AND/OR/NOT gates.

The lemma-search agent confirmed the ordinary Petersen lower bound excluding eighteen gates is still open (L-meta-4031). The nine-variable graph obtained by deleting a vertex has checked lower bound sixteen, L-meta-670 / L-meta-4033. The full Petersen pivotal condition is already checked as L-meta-6081; do not reprove it. L-meta-7314 normalizes the free-complement problem to an ordinary eighteen-gate circuit except a precise eighteen-gate/output-28/no-NOT-reading-input-10 case. These dependency facts were read from local sources and the lemma-search agent; they do not close the goal.

## Valid mathematical observations, not newly Lean-checked here

1. With no actual NOT gate and no effective use of positive input 0, the circuit is nonincreasing in original variable 0: its only varying source is complement 0, and AND/OR preserve its direction. Petersen is increasing and essential in variable 0. Therefore that subcase is impossible. Out-of-range reads and constant gates do not change this argument. The output cannot itself be the ignored positive-input wire, because the target is not a literal.

2. With exactly one actual NOT gate and positive input 0 unused, the unique NOT must receive a signal depending on complement 0 and must influence the output. Otherwise the same nonincreasing argument applies. This gives a necessary dependency path, but no adequate gate saving has yet been proved.

3. A live fan-in-two circuit with eighteen gates cannot give every one of the ten effective original variables at least two input-reader incidences: at most thirty-six input ports are available, at least seventeen are needed to connect the live gates to the output, leaving at most nineteen source incidences. Unary NOT gates only strengthen the inequality. Care is needed to combine positive/complement copies of input 0 and eliminate unused gates before applying it.

4. Restricting input 0 to false removes the free unary source, so three gate savings would contradict the checked nine-variable lower bound sixteen. Restricting another variable leaves the free complement of 0; adding a NOT to represent that complement may consume one gate. Thus three arbitrary savings at a nonzero vertex alone do not contradict the ordinary nine-variable bound. If enough binary gates are saved and the signed lower bound is available, a stronger argument may apply.

5. A unique positive OR reader is a real obstruction, not an impossible circuit pattern. If y is a neighbor of x and yz is an edge, then

    (x OR (y AND z)) AND OR(N(x))

computes the x-star together with yz, since y belongs to N(x). The variable x has a unique OR reader. Constant propagation under x=false removes only that OR, but semantic absorption reduces the remaining expression to yz. Therefore a proof based solely on syntactically killed AND/NOT readers misses legitimate patterns; extra absorption or a structural theorem is required.

6. The normalized exceptional pattern of one OR reader of positive 0 and one AND reader of complement 0 can lose exactly two gates under 0=false, leaving a sixteen-gate circuit for the vertex-deleted graph. The existing lower bound allows this boundary case. Classifying or further normalizing such optimal restricted circuits could resolve it; no such classification was established here.

## Promising but unproved route

The global-bridge agent proposed a signed-binary Petersen lower bound of seventeen, using the checked signed nine-variable lower bound and a no-pair-funnel argument. If completed, an eighteen-gate candidate would have at most one actual NOT gate. This is a reduction of the search space, not a completed Lean theorem in this work.

Within that case, transporting the sole NOT through its input cone is obstructed by fanout: a signal may be needed both positively and negatively. Monotonicity of the final function does not justify deleting or replacing the NOT locally. No size-preserving NOT purification theorem was found in the local checked proofs.

The finite certificate source for the nine-variable lower bound is available, but the child audit found no committed certificate generator. Regenerating a ten-variable certificate is substantial work; the existing nine-variable build plus replay is reported to take roughly forty-four minutes.

## Further near-monotone case split

The zero-NOT antitonicity observation is already subsumed by checked L-meta-7312: when positive input 0 is unused, it produces an actual NOT gate whose value changes false to true between assignments {1} and {0,1}. Thus no new proof of that trace is needed.

A concrete unformalized subcase can be eliminated by three constant-propagation savings. Assume positive 0 is unused, there is a unique actual NOT, its input wire is h, and the hard exception excludes the NOT reading the free complement directly. If h is true when only the free complement is true, then setting original input 0=false makes h constantly true: before the sole NOT the circuit is monotone, and constant propagation detects this positive certificate. The gate producing h disappears, the NOT becomes false and disappears, and an output-relevant reader of that NOT disappears. The NOT cannot itself be the output since the vertex-deleted Petersen function is nonconstant. These three savings would contradict the checked sixteen-gate lower bound. This has not been implemented in Lean here.

The remaining case has h false when only the free complement is true, although h must be true when the free complement and any one of the three neighbors of 0 are true. Thus the NOT must receive additional positive input support.

Already in the special case h=(complement 0) AND q, the cut at the NOT has the form

    F0 = A OR (B AND NOT q)

with A and B monotone and A <= F0. The three neighbor-singleton traces force q to accept those neighbors. For any edge e of the vertex-deleted graph, degree three and girth five give a neighbor v of 0 nonadjacent to both endpoints of e. If q(e)=false and B(e) is responsible for accepting e, then q(e+v)=true and therefore A(e+v)=true. This does not imply A(e)=true: A may contain a conditional cubic term e AND v. Consequently monotonicity alone does not remove the NOT. One would need a size argument showing these compensation terms are wasteful. The factorization h=(complement 0) AND q is a special case, not a consequence of merely having one direct AND reader of the free complement; later OR gates can add terms independent of that source.
