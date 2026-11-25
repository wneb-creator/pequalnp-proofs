# Why the unrestricted support-mask merge inequality is false

Paper derivation; not a Lean proof. Independently reviewed by proof_route on
2026-11-25, including the primary-source parameter premise. This refutes an unrestricted generalization of
the mask-only auxiliary statement `L_meta_7995.cnt_main`, not the exact-function
claim L-meta-2585. It does not apply when the row wires compute genuine pure ORs.

The proposed unrestricted specialization, with exit set E and label set Lab empty,
would say that M occurring triples with pairwise intersection at most one require
at least 2M total carrier exits plus carrier merges. The bound |P| <= 7 cannot simply be
dropped, even if arbitrary auxiliary mask sizes are allowed in a proposed proof.

Use the primary construction in Nets Hawk Katz, *On the CNF-complexity of bipartite
graphs containing no K2,2's*, https://arxiv.org/pdf/1206.6068, read 2026-11-25.
Fix a small epsilon > 0, say epsilon = 1/4. For sufficiently large d the construction
gives a C4-free graph G=(V,W,E_G), with |V|,|W| <= N=d^10, at least
c N d^(1-epsilon) edges, and k=O(log d) clause graphs:

    G = intersection_j ((A_j x W) union (V x B_j)).

More precisely, Katz's proof retains at least N/2-4d^5 rows of degree at least
c d^(1-epsilon): it starts with at least N/2 such rows and at most 2d^5 copies
of K2,2, then removes the V vertices participating in those copies. W is
unchanged, so surviving row degrees are unchanged. This yields the edge bound
above for sufficiently large d.

In particular, each nonempty row neighborhood is

    N(v) = intersection_{j: v notin A_j} B_j.

First construct all k subsets B_j of the label set P=W using binary unions of
singleton inputs. This costs at most kN gates. Construct every needed nonempty
row neighborhood using at most k intersections per row. The total preprocessing
cost is O(N log d). Empty clause sets that are irrelevant can be omitted; a
nonempty row cannot select an empty clause set. Every partial intersection for a
nonempty row contains the full neighborhood, and hence remains nonempty. If a row
selects no clause, construct W itself with at most N-1 unions.

There are O(log N) dyadic row-degree buckets. Choose one bucket with degrees in
[r,2r] carrying at least |E_G|/O(log N) edges. If it has a rows, then

    a r = Omega(|E_G| / log N).

Buckets with bounded r cannot carry that many edges for this graph, so the chosen
r tends to infinity. Color each element of W independently and uniformly into
q=floor(r/3) color classes. For a row of degree t in [r,2r], the expected number of
color classes meeting its neighborhood in exactly three elements is

    q * binom(t,3) * q^(-3) * (1-1/q)^(t-3) = Omega(r).

The implied positive constant is uniform for t in [r,2r] and all sufficiently
large r, because t/q remains in a fixed compact interval near [3,6]. Therefore
some coloring produces

    M = Omega(a r) = Omega(|E_G| / log N)
      = Omega(N d^(1-epsilon) / log d)

three-element row/color cells. Cells from the same row are disjoint. Cells from
different rows intersect in at most one label by C4-freeness. Hence these M
triples are all distinct and form the required linear family.

Construct the nonempty color classes using at most N binary unions. For each
three-element cell, add one binary intersection of its row mask with its color
class mask. The entire union/intersection network now has

    S <= O(N log d) + N + M < 2M

gates when d is sufficiently large. All its computed masks are nonempty.
Repeated operand indices, if any occur during preprocessing, can be bypassed by
idempotence, decreasing S without losing a support occurrence. The final
row/color intersections have distinct operand indices because each row has
degree greater than three whereas its intersection has size exactly three.
Consequently every input and gate belongs to carrierT(P), every carrier exit set
is empty, and every gate is a carrier merge. This gives M occurring linear
triples with exitArcs.card + merges.card = S < 2M.

The network is a legitimate binary monotone Boolean circuit if unions and
intersections are interpreted as OR and AND. Its semantic singleton supports
are exactly the masks constructed above. Its higher-degree behavior is not
claimed to be a linear family or an exact graph function. This distinction is
exactly why MixedLinear, which assumes purity on all outside-row assignments,
does not contradict the construction.

The conditional source theorem and the elementary random-coloring calculation
give an asymptotic existence obstruction; no explicit finite gate list or Lean
certificate is supplied for this asymptotic family. The separate 18-gate star
example gives an explicit failure of the narrower small-mask auxiliary lemma.
