# Mixed OR guards in a projective-plane edge circuit

These are mathematical observations, without a Lean certificate. The rectangle-cut results in `quadratic_structure.md` assume a different input architecture. The observations here do not establish the posted theorem or exhibit a smaller plane circuit.

## Pinning mixed raw OR gates

Let `G` be a bipartite graph, and let a monotone circuit `C` compute its edge function. Pick any collection of physical gates computing `x_a OR y_b` for pairs `(a,b)` in a set `K`. The gates can have arbitrary fanout. Let `H` be the function of the circuit with all these outputs pinned to one. Form a directed graph on the point and line vertices by orienting every edge of `G` from point to line and adding a reverse arc `b → a` for each pair in `K`. Let `R` be the bipartite relation in which `(p,l)` belongs to `R` exactly when there is a directed path from `p` to `l`. Then on every assignment

```
F_G ≤ H ≤ F_R.
```

The first inequality is monotonicity. For the second, if none of the selected lines `Y` is reachable from the selected points `X`, take the set of all reachable vertices starting in `X`, including `X` itself. Enlarge the selected points to all reachable points and the selected lines to all nonreachable lines. This extends the given assignment and is independent in `G`: a line adjacent to a reachable point is reachable. Every guard is true, as a reachable line `b` makes its guard partner `a` reachable. On this independent extension the pinned circuit agrees with the original and is false. Monotonicity now gives the conclusion on the original assignment. Conversely an independent extension satisfying all guards must mark all reachable points as selected and all reachable lines as unselected, by following each kind of directed arc. This proves the exact criterion for existence of such an extension.

For a single guard `x_a OR y_b`, every newly reachable pair belongs to `N(b) × N(a)`. A false positive of `H` must omit `a,b` and contain a point on `b` and a line through `a`. The latter statement also follows by adding each guard endpoint separately, making the original circuit true on both larger inputs. A guard can exclude many nonedges at once. For an incident pair `a,b`, the conjunction

```
(OR X over N(b)) AND (OR Y over N(a)) AND (x_a OR y_b)
```

computes the union of the full stars at `a` and `b`. Pinning its mixed OR to one admits all `(d−1)²` off-center crosses, where `d` is the common degree. None of those crosses is an edge because a 4-cycle would result.

In a plane of order `q`, `q+1` guards suffice to make `R` complete. Take a point `p0` off a line `L0`. List the `d=q+1` pencil lines through `p0` as `b_i` and set `a_i=b_i∩L0`, indexed cyclically. Choose guards `x_(a_(i+1)) OR y_(b_i)`. The incidence arcs `a_i → b_i` and the guard arcs `b_i → a_(i+1)` form a directed cycle. Every point reaches a pencil line and every line is incident to a point on `L0`, which proves completeness. When all these guards are true, `F_G` equals `(OR X) AND (OR Y)`. For `q≥2`, the raw guard pairs form a matching of size at least three. No positive two-input flag satisfies all guards at once. The domain identity thus supplies no circuit saving for the whole function.

## Mixed OR features and raw nonemptiness

Consider a circuit whose monotone combining part receives only physical raw mixed OR features `x_a OR y_b` and the mixed-nonemptiness indicator `(OR X) AND (OR Y)`. Arbitrary sharing of features is permitted. Then at least `|E|=N(q+1)` distinct mixed OR features are needed. The same conclusion holds if arbitrary point-only monotone bypass signals are also supplied.

A blocking point set meets every line. It has at least `d=q+1` points: if there is an outside point, the `d` pencil lines through it have pairwise disjoint intersections with the blocking set, while the whole point set has more than `d` points. A blocking set of size exactly `d` is a full line. Otherwise choose a line determined by two of its points that also contains some outside point `r`. Every one of the `d` lines through `r` needs a blocker, while this line already has two, contradicting the cardinality. Thus every line determined by two chosen points is contained in the set, and the size gives equality with that line. The dual statements hold for line sets.

For fixed `l`, let `A_l` be the point partners appearing in the features `x_a OR y_l`. For every `p` on `l`, the set `{p} ∪ A_l` must block every line. Indeed, take a line `m` disjoint from this set if there is one. On the independent assignment `({p}∪A_l,{m})`, every feature previously true on `(p,l)` stays true. A feature with point `p` still has it, and a feature with line `l` now has its point partner. The global nonemptiness signal remains true, and point-only signals can only increase. This contradicts monotonicity of the combiner. Thus `|A_l|≥d−1`. If `|A_l|=d−1`, every point of `N(l)` would have to lie outside `A_l`, and adjoining any one of them would give a full line by the blocking-set characterization. Since `d−1≥2`, all these lines contain the same two points of `A_l` and are identical. The common line contains `N(l)`, hence equals `l`, forcing `A_l ⊆ N(l)`, a contradiction. Therefore `|A_l|≥d` for all `l` and there must be at least `Nd` distinct features. In the architecture without bypasses the dual argument also gives at least `d` features incident to each point. The primitive features are pairwise incomparable as physical upstream gates. Their joins to the output require at least `Nd−1` additional binary gates, regardless of any further gates used to construct the nonemptiness indicator.

The same argument gives at least `d` mixed features at each line `l` outside a specified set of raw line bypasses if those raw bypasses and arbitrary point-only monotone signals are permitted. On the positive test `(p,l)` every other raw line signal is zero.

If the nonemptiness guards are instead applied at the output in an identity `F_G = H AND (OR X) AND (OR Y)`, a pure point set accepted by `H` has to block all lines: adding a disjoint single line would otherwise give a false positive. Thus every such set has size at least `q+1`, with equality only for a complete line. The transposed statement holds for pure line sets. Enlarging `F_G` by arbitrary pure predicates accepting only blocking sets is compatible with the output guards. This rules out attempts to add same-shore pairs and then repair the result solely by checking nonemptiness of both shores.

## Gates true on both pure extrema

In an arbitrary exact circuit, delete simultaneously all gates true on both the all-points-only and all-lines-only assignments. Every input still has a directed path to the output in the remaining graph. For a point, compare all-lines-only against that assignment with the chosen point added. The output changes from zero to one, so following a changing operand backwards gives a path from the only changing input. All its wires are false on the all-lines-only assignment. The transposed argument covers line inputs.

Let `S` contain the vertices on one such path per input, including the output. The induced subgraph is connected undirected. If it contains `g` gates and all `2N` inputs, it has at least `2N+g−1` internal arcs. If `b` incoming predecessor arcs of its gates originate outside `S`, it has exactly `2g−b` internal predecessor arcs, counting repeated operands with multiplicity. Thus `g≥2N−1+b`. The full circuit size is at least `2N−1+b` plus the number of gates outside `S`, which includes all gates true on both pure extrema. Deletion in this argument certifies connectivity only.
