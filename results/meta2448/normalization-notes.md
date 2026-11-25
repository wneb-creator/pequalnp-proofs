# L-meta-2448 normalization work

The posted target asks for a minimum monotone fan-in-two circuit for the exact
edge function, with a star profile. No graph promise approximation is involved.

## Checked components located

- `L_meta_2666.lean` proves minimum existence by an explicit monotone graph DNF
  and `Nat.find`. The geometry agent has adapted it to the new namespace.
- `L_meta_1600.lean` proves star ownership for an AND gate whose truth implies
  the graph function on every input. Its proof uses soundness only on pair
  inputs. The adapted `PairSound.lean` weakens the premise accordingly and
  checked successfully at SHA
  `1a67c916b04fec82bf8b9e8f5bc0c7ccca1ef613ed995b611d41b9849a8aba9f`.
  It also proves that a nonstar circuit on a C4-free graph has an AND accepting
  a nonedge pair, including the possibility of a singleton input.
- `L_meta_2668.lean` proves every AND of a minimum circuit is crucial on some
  accepted edge: erasing that gate to false makes the output reject that edge.
- `L_meta_4181.lean` produces a no-larger least circuit in TopForm. This forbids
  a globally sound AND from lying below another AND; it does not make all ANDs
  sound.
- `L_meta_1499.lean` is the clean-AND exchange used to reduce `andPairs` while
  preserving the dirty-AND count.
- The repository auditor found `L_meta_3653.lean`, which removes dirty ANDs in
  a restricted bipartite, one-dirty-gate, singleton-firing situation. Its
  additional fixed-point, liveness and operand conditions are substantial.
  It does not supply the arbitrary-dirty-gate normalization needed here, and
  triangle-free/C4-free graphs need not be bipartite.

## Remaining obstacle

Pair-soundness of every AND is sufficient, but we do not have a size-preserving
normalization establishing it for a minimum circuit. The simplest unsafe
product on the path with edges ab, bc, cd is

    ((a OR c) AND (b OR d)) AND (b OR c).

It uses five gates and accepts exactly those three edges. A star construction
uses four gates:

    (b AND (a OR c)) OR (c AND d).

This illustrates a local saving when the operand and cleanup cones are private.
In a general circuit, those OR cones may be shared elsewhere. Distributing or
reassociating the cleanup can then increase the number of gates, so the example
is not a general exchange proof.

The algebra agent is examining contextual and cost arguments. In particular,
reassociating adjacent ANDs preserves the gate count; moving through an OR is
free only under an additional side-branch soundness condition. No such
condition has yet been proved for every required branch.

No minimum star-profile theorem, refutation, or full normalization has been
established by this component.

## Later constraints and the unresolved pooling cost

The checked `EdgePruning` component justifies a semantic repair that decreases
the output and retains every graph-edge pair. `EdgeContext` proves that a wire
accepting both endpoint singletons of an actual graph edge can only have a sound
monotone context if that context rejects every singleton. Neither component
proves a size-preserving circuit transformation.

In a least TopForm circuit, the final OR region can be viewed as the union of its
clean AND outputs. Two such outputs with the same exact operand q would factor:

    (q AND g) OR (q AND g') = q AND (g OR g').

This saves one gate after rebuilding the final OR region, even if g and g' have
other uses. The argument is mathematical only here. It excludes shared exact
operands of distinct clean AND outputs, but not different OR-only paths from a
last dirty gate into those outputs.

For a last dirty gate g, expansion of those paths gives a cofactor expression

    output = R OR (g AND (K1 OR ... OR Kr)).

Building the pooled context may require r-1 additional OR gates. Setting g to
false is only guaranteed to delete g and its direct readers. Thus this expansion
alone does not pay for a repair under arbitrary branching and sharing.

A narrow nonlinear cleanup case is easier: if a private g=A AND B feeds
h=g AND C and C rejects every singleton, reassociate to (A AND C) AND B. Whenever
C accepts a pair, its cone has a true AND gate, since an OR-only accepting trace
would accept an endpoint singleton. Consequently neither replacement AND owns
that graph edge. This preserves the number of gates, but requires a private g
and suitable topological reordering; it is not formalized here.

A singleton-accepting cleanup may have singleton support outside the product
sides. For two disjoint owned edges with sides {a,c} and {b,d}, an outside vertex
e adjacent to a and c is compatible with triangle/C4-freeness (the path
b-a-e-c-d). Such a context singleton can explain sound higher-degree terms
without helping the product's accepted quadratic edges. Removing those terms
from a shared context still lacks a gate-cost argument.

No general pooling, arbitrary-sharing exchange, or minimum star-profile theorem
has been established. These observations are not Lean-checked results.
