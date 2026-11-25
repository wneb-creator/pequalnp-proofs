# Exact linear outputs with small pairwise intersections

Research note, 2026-11-25, algebraic_witness. This is a mathematical argument, not a new Lean certificate and not a proof of L-meta-1896.

Let a monotone Boolean DAG on variables indexed by V have outputs exactly

    f_i = OR { x_v : v in S_i },

where distinct output supports satisfy |S_i intersection S_j| <= 1. Then the number of binary OR gates is at least

    sum_i (|S_i| - 1),

with an empty support contributing zero. Arbitrary internal AND gates and arbitrary sharing are allowed. This proves 39 for thirteen exact four-variable pencil outputs without a simultaneous OR-only normalization theorem.

For a fixed nonempty target S, let z be the assignment whose true variables are V minus S. For every wire g write L(g) = { v : g is true on the singleton assignment {v} }. If g(z) is false, monotonicity gives L(g) subset S.

Process the DAG in topological order while maintaining a graph on S. Maintain that L(g), for every processed wire g false on z, lies within one connected component; the assertion is vacuous for an empty L(g). Initially, a relevant input has a singleton support. Constant false has empty support, and constant true is never false on z.

At an AND gate false on z, at least one child is false on z. The parent's singleton support is contained in that child's support, so the invariant needs no graph edge. At an OR gate false on z, both children are false on z, and the parent's singleton support is their union. Add at most one graph edge between the two child components when both supports are nonempty and lie in distinct components. Every such charged OR has |L(g)| >= 2.

The output is false on z and has L(output) = S. Thus the final graph connects all of S and at least |S|-1 OR gates have been charged. Each charged OR satisfies both L(g) subset S and |L(g)| >= 2. A gate charged for two distinct targets would therefore have a two-element support contained in their intersection, which is impossible. The targetwise charges are disjoint, proving the sum bound.

Two limitations prevent applying this directly to the posted problem:

1. A posted point cofactor need not be an exact linear output. It may accept concurrent triples of lines outside the point's pencil. Its value on the full complement of that pencil can consequently be true, although it rejects all required cap negatives.
2. The thirteen point cofactors are restrictions of one circuit, not thirteen outputs of one unchanged circuit. A gate's singleton support and value at the chosen negative assignment can differ between point restrictions. The disjointness argument cannot identify these different charges with disjoint global OR gates.

Rejecting the 104 pure triples themselves would not repair the first limitation. A separator may have a higher-degree minimal term containing an allowed triple, such as x_p AND y_a AND y_b AND y_c for three concurrent lines avoiding p. This term is below the maximal allowed function W but vanishes on the pure line triple; its p-cofactor is still nonlinear. The description of W by 156 minimal terms is not a description of the minimal terms of every separator between the incidence function and W.

A separate contextual fact holds under the posted promise. If a wire g has a singleton context v with x_v AND g pointwise below the final output, every singleton accepted by g must be a neighbor of v: otherwise a forbidden nonedge pair would be accepted. Since the incidence graph is C4-free, two or more accepted singleton variables determine at most one such vertex context. This does not yet charge the whole DAG. A useful edge trace can instead use a context containing both variables of the accepted edge; termwise removal of this redundant edge context need not correspond to a shared-DAG transformation with no extra OR gates.

Allowed-host literature searches on 2026-11-25 did not locate an applicable primary theorem establishing |E|-1 OR gates for all exact C4-free Boolean edge functions. That general claim remains unverified here. The arithmetic monotone-circuit survey previously read at https://github.com/dasarpmar/lowerbounds-survey/blob/master/chap_simpleLBs.tex concerns addition/multiplication circuits and does not justify a Boolean normalization with idempotent AND. No search snippet has been treated as a theorem or evidence of applicability.
