# One-sided relaxed factor and derivative-killing wrapper

This is a sufficient construction target for L-meta-2602. No qualifying plane factor has been constructed.

Let G be the 26-input order-3 incidence function. Suppose H is a legal monotone binary AND/OR circuit with distinct earlier operands satisfying these finite conditions:

1. H accepts all 52 incidence-pair assignments.
2. H rejects all 702 mixed maximal independent-set assignments.
3. H rejects the pure-line full assignment, with all points false and all thirteen lines true.

H may accept pure-point blocking sets. By monotonicity, its only possible extra true inputs beyond G are pure-point blocking sets: a pure point set that misses some line extends to a mixed maximal independent set, and every independent input having a nonempty line side extends either to a mixed maximal independent set or to the pure-line full assignment. Conversely, every true G input contains an accepted incidence pair. Thus, writing L for the disjunction of all thirteen line inputs, H AND L equals G on every input.

Every singleton is rejected by H. Line singletons lie below the rejected pure-line full assignment. A point singleton extends to a mixed independent set by adding any nonincident line, and then to a mixed maximal independent set. Each point has nine nonincident lines.

Append the following circuit to H:

- Compute L using twelve binary OR gates.
- Compute F1 = H AND L using one AND gate.
- Compute F2 = H AND F1 using one AND gate, and designate F2 as output.

The final function is G because H AND (H AND L) equals H AND L. At each singleton, both operands of the final AND are false. Hence the formal directional derivative recurrence at that gate is zero for both target directions, regardless of the earlier derivative values. Forward recurrence supplies the required complete traces.

The appended L root is a fresh wire, so it differs from the earlier H output. F1 is another fresh wire, so the final operands H and F1 also differ. All new gates read earlier wires. Acceptance of an incidence pair ensures the H output is an actual earlier wire. The construction adds exactly fourteen gates. Therefore a qualifying H with g <= 50 gates would produce at most64 gates. If g+14 is below63, repeatedly append AND(current output, retained H output). These gates preserve G and both zero derivatives, and their operands remain distinct. This reaches63 gates.

A material limitation: before the final redundant AND, F1 is already an ordinary circuit for G with g+13 gates. Consequently H with g <= 50 would also give an ordinary circuit of size at most63. The larger H budget does not bypass the possible64-gate ordinary lower bound. No such lower bound or qualifying H is claimed here.

The accompanying h1_one_sided_control.py verifies a four-input matching example. Its factor H computes x0*y0 OR x1*y1 OR x0*x1, accepts the two matching edges, rejects the two mixed maximal independent sets and the pure-line full mask, and accepts the pure-point full mask. Appending line OR, F1 and F2 gives seven legal gates. All sixteen truth assignments and both formal derivative directions for each matching edge are checked. This is a control of the algebra, not a plane result.
