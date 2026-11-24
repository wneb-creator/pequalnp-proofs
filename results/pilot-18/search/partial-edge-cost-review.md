# Partial-edge support cost: rigorous extension of L-meta-1407

Verdict: PASS. Let G be the posted C4-free ambient graph. Let W be any wire
produced through a prefix of m binary AND/OR gates, every AND clean for G.
Let S be W's singleton support, assumed proper. Let H consist of the edges
uv of G for which W is true on the two-vertex row {u,v} and u,v are outside S.
Then

    m >= |S| + |E(H)| + tau(H) - 1.

W may accept higher-degree inputs. It need not be F_H, and intermediate ANDs
need not be clean for H. These facts do not invalidate the proof below.

## Empty-support partial output: two graphs in the counting proof

First consider a circuit with an empty-support output R that accepts every
edge row of some subgraph H of an ambient C4-free graph K. All its ANDs are
clean for K. Remove free constants and aliases without increasing gate count;
if the output is nonzero, no TRUE constant is needed in the retained circuit.

For each retained wire w, use its actual singleton support S(w) and its actual
two-input-row truth predicate, just as in L-meta-1407. Clean ANDs have empty
support. Their operand supports are disjoint and every cross pair is an edge
of K. The C4-free property implies that at least one operand support has size
at most one.

Define B to be the union of ALL cross-support edges of ALL retained AND gates.
Then B is a subgraph of K and is C4-free. Every cross pair at an AND is an edge
of B by definition, and every edge of B has a witnessing AND by definition.
The original helper edge_finset_gate_bound can therefore be applied to B,
without changing its hjoin or ownership proof. It yields

    |E(B)| <= number_of_ANDs + number_of_ORs_with_support_size_greater_than_one.

The helper edge_birth, using the empty support at R, gives H <= B. Its
induction needs the two-row evaluation rules, disjoint AND operand supports,
and acceptance of the particular output edge; it does not need equality of
the output function with F_H. Therefore the same upper bound holds for |E(H)|.

Separately apply cover_half with target graph H and the same wire supports
and two-row truth predicates. This helper's signature requires acceptance of
all H edges and the small-side property for every AND. It does NOT require
that every AND cross pair belongs to H. The small-side property was already
obtained from K's C4-free property. Thus it constructs a cover of H satisfying

    tau(H) <= 1 + number_of_ORs_with_support_size_at_most_one.

The AND count and the two OR counts partition the retained gates, as in
gate_partition_count. Adding the inequalities gives

    |E(H)| + tau(H) <= retained_gate_count + 1.

This proves the empty-support partial-output bound. It deliberately does not
apply the final published L-meta-1407 theorem directly to H: that theorem's
exact-output and AND-clean-for-H hypotheses are stronger than the present ones.

Relevant source inspected in lean/PEqualNP/Outside/L_meta_1407.lean:
gate_partition_count at line 479; cover_half at line 533; edge_birth at line 637;
edge_finset_gate_bound at line 680; the final combination in total_from_model.

## General proper support

Set S to zero. The restricted wire has empty singleton support and accepts
exactly the previously defined H edge rows. Every retained AND is clean for
the ambient induced graph G[V minus S]. If H has an edge, the restricted
output is nonzero. The reviewed pure-S OR-component argument removes at least
|S| gates: with a pure-S OR nodes and b boundary OR nodes, a+b >= |S|.
Applying the partial-output bound to the remaining circuit gives

    |E(H)| + tau(H) <= m-|S|+1.

If H has no edges, the desired inequality is merely m >= |S|-1. Proper support
ensures W is false at the empty input and true at each S singleton, so W depends
on all |S| distinct S variables. Binary fan-in dependency counting proves that
bound even when W accepts higher-degree inputs after restriction.

Full support must be exempt because free TRUE can have full support at no cost.
The exceptional full-support case must not be subjected to the |S|-1 argument.

## Exact existential-cover encoding

For prefix gate g, use m=g+1. For each ambient edge uv define

    q[uv] = edge_value[uv] AND NOT support[u] AND NOT support[v].

Introduce eleven cover bits c[v] and require, for every ambient edge,

    NOT q[uv] OR c[u] OR c[v].

When support is proper, impose

    sum(support) + sum(q) + sum(c) <= g+2.

Existence of these cover bits is equivalent to
|S|+|E(H)|+tau(H) <= g+2: any satisfying c is a cover, while a minimum cover
witnesses the converse. Cover vertices in S are unnecessary but need not be
explicitly forbidden; an existential solution can set them false. The q bits
should represent the stated conjunction. At full support q is identically zero;
the cover clauses may remain, but the cardinality bound must be disabled.

This formulation uses the accepted edge mask itself and avoids a 2^27 lookup.
It is a necessary condition for every prefix wire, independently of which
tail template later reads it. No solver behavior or runtime improvement is
claimed by the mathematical review.

## Cheaper consequences and joint-output observation

For nonempty H, tau(H)>=1, so m >= |S|+|E(H)|. A stronger inexpensive cover
lower bound sums exact covers of the accepted edges on the three vertex-disjoint
cycles (1,4,8), (3,6,7), and (0,9,5,2,10). Alternatively any accepted matching
has cardinality at most tau(H). These are weaker substitutes for existential
cover bits, not needed if the exact formulation is used.

For meet5, each proper-support leaf covers every ambient edge. Comparable
supports give redundant factors because W_S=F OR OR(S); the smaller support
already implies the larger-support factor. Distinct necessary leaves may thus
be considered an antichain of supports. Their prefix outputs must be OR gates,
and no direct edge may join two of these outputs, since such an OR read would
force support containment.

Consequently an output requiring all 17 available prefix gates cannot coexist
with an incomparable full-edge output of lower bound 16. Their slots would
have to be 17 and 16 respectively; the last OR cannot read the preceding one,
so its dependency cone would have at most 16 gates. This excludes the proposed
support-only family {8,10}, {4,6}, {3,4}, whose individual bounds are 14,16,17.
It does not by itself exclude all support families or prove the gap.
