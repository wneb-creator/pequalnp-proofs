# Two-junk structural investigation

This is a strategy result and a finite counterexample to an overstrong intermediate claim, not a refutation of L-meta-2583 or of a least-circuit theorem.

## Existing elimination results and their limits

L_meta_5412 is directly relevant. For a bipartite graph without four-cycles, a least circuit at a lift fixed point cannot have exactly two junk ANDs if both junk gates are pure double-star flags. Each flag must compute `OR(Ci) AND OR(Di)`, with both sets of size at least two, and there must be an incident center pair z,z' such that every point of Ci is adjacent to z' and every point of Di is adjacent to z. The source's `main` at line 7633 dispatches the two-center, three-center, and four-center cases. Its `master_surgery_bound` at line 1941 explicitly uses leastness to compare against a replacement circuit.

The flag hypotheses are substantial. Accepting at least two graph edges is not enough to derive them, even for an acyclic bipartite graph and even after all the ordinary normalization properties are imposed.

L_meta_5391 addresses a useful nested pair: the first junk g has pure OR operands, is read only by the second junk T, and T's other operand is pure OR. Its surgery also requires each further AND reached from T to be below the target and have a literal input as its other operand. It supplies a replacement deleting two junk gates with an explicit edge-repair cost. The final-other-operand-is-a-literal condition remains a real restriction, not a consequence of TopForm.

L_meta_7895 provides an accounting dichotomy for exactly two junk gates. Either `2 ≤ 2*centreless + otherOR`, or a particularly narrow chain occurs: each junk has a unique reader, there are no centreless gates, there is one other OR, and every Ustar edge is accepted at both junk gates. This is useful for a low-overhead case split, but the first branch by itself says nothing proportional to the number of Ustar edges.

## A normalized two-junk core on a forest

Take the path `a-b-c-d-e`, whose function is

```
F = ab OR bc OR cd OR de.
g = (a OR c OR e) AND (b OR d)
h = g AND (b OR c OR e)
f = h AND (a OR c OR d)
```

Boolean simplification gives

```
h = ab OR bc OR be OR cd OR de
f = F.
```

Using the shared OR `(c OR e)`, this is a nine-gate circuit. Exactly g and h are dirty ANDs. Both accept all four path edges. The only clean AND is the final output f, so TopForm holds. Every gate is live. Every OR gate has only OR/input ancestors; therefore no OR reads a target implicant, and the circuit is a lift fixed point. None of the operands of its three ANDs is below F. Every proof tree for an edge at f has at least four leaves drawn from its two endpoints, so the top is a repeated-read core; read-two proof trees exist for every edge.

The accepted-edge graph at g is the four-edge path itself. It is not a double star: no edge's two endpoints cover the path's four edges. The second junk h is not even a pure OR-times-OR Boolean function; its five quadratic minterms form `K(3,2)` with one cross pair removed.

The exhaustive script `search/two_junk_core.py` checks all 32 assignments, all stated normalization properties, and proof-tree multiplicity vectors. It completed with exit code 0. Complete output is in `search/two_junk_core.stdout`; stderr is empty. This is a finite Python verification, not a Lean theorem.

Crucially this circuit is not least: `b AND (a OR c)` OR `d AND (c OR e)` uses five gates. The example therefore does not contradict L_meta_3760, L_meta_5412, or the posted goal. It does show that bipartiteness and normalization alone do not force an odd cycle in a multi-edge junk core. Even a forest supports the obstruction. A purported proof of two-junk elimination must use leastness quantitatively.

This path is also an induced incidence subgraph of every plane of order at least two: choose three noncollinear points a,c,e and their two joining lines b=ac and d=ce. Thus the local geometry cannot rule out this shape. Embedding such a core into a full incidence circuit still does not make that full circuit least.

## Consequence for the next proof attempt

The promising local distinction is not odd versus even cycles. It is whether the nonliteral filters and mixed-color OR gates needed to clean a non-flag junk rectangle pay for a replacement by stars. In the example, the two extra filters remove the two bad cross pairs; their OR costs make the replacement strictly cheaper. L_meta_5412 already implements this type of comparison for two pure flags. Extending it to a nested non-flag gate must track shared OR gates and edge-repair costs rather than assume that the forbidden shape is geometrically impossible.

No general two-junk elimination or unrestricted sharp charge was established in this investigation.
