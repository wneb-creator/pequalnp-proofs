# Private degree-two line cores and missing neighborhood ORs

These are mathematical arguments for finite monotone circuits. They have not been formalized in Lean. The full projective-plane bound remains open in this attempt.

Use a strict live binary AND/OR DAG on all essential point and line variables. Pruning constants, repeated operands and dead wires only shrinks a circuit. For a nonoutput wire its surplus is its outdegree minus one. The total surplus equals the gate count plus one minus the number of inputs.

Write `B(w)` for the set of point labels `i` for which `w` accepts the input containing only `x_i`. Write `f_j` for the OR of the point neighbors of line `j`. A row is present if some wire equals `f_j` on the entire subcube with all lines zero. Other rows are missing.

## A missing row consumes a branching wire

Starting at `y_j`, walk toward the output while there is one consumer. Stop at the first wire with at least two consumers, or at the output. Call the stopping wire `b`. Because the path taken so far was unique, `b` dominates every path from `y_j` to the output.

Set all other line inputs zero and leave the points `X` free. The output depends on `y_j` only through `b`. With all points one, changing `y_j` from zero to one flips the output, so the baseline value of `b` is zero even at all points one. Monotonicity gives `b(X,0)=0` on the entire baseline. Independently pin `b=1`, set all lines zero and call the resulting output `h(X)`. Pinning `b=0` gives zero. Thus

`f_j(X) = b(X,e_j) AND h(X)`.

The OR of a nonempty point set `S` has a unique maximal false point assignment, the complement of `S`. If this OR equals a meet of finitely many monotone functions dominating it, one of the functions must equal the OR, by evaluating at that maximal false assignment. If `b` is the same first branching wire for two lines with incomparable neighborhoods, `h` dominates both neighborhood ORs, so differs from both and `b(X,e_j)=f_j(X)` for both. If `b` is the output, the same conclusion holds directly.

Every sibling on the unique initial path is independent of `y_j`. With all points one, all OR siblings must be zero for the path to carry the `y_j` flip. Consequently they are identically zero on the baseline. The remaining AND siblings multiply, giving `b(X,e_j)` as the meet of their baseline point functions. If that meet equals `f_j`, a sibling is an actual wire equal to `f_j` on the baseline. In particular, in any family of pairwise incomparable missing rows, the first branching wires exist, are distinct, have surplus at least one each, and have empty point support `B(b)`.

## Point wires with a connected singleton-support path

For each point `i`, let `R_i` consist of wires reachable from `x_i` along a directed path, including its endpoints, on which every wire has `B(w)={i}`. These sets are disjoint. The reachability condition is necessary: an AND of two multipoint-support wires may recover exactly the singleton support `{i}`.

The input `x_i` is the unique raw input of `R_i`, and every other member has at least one parent in `R_i`. The output has empty point support. Writing `E_i` for the number of arcs from `R_i` to its complement, the sum of outdegrees on `R_i` counts those exits plus at least `|R_i|-1` internal arcs. Hence `surplus(R_i) ≥ E_i-1`.

For a present row `j` and `i` in its neighborhood `S` of size at least two, trace back from its baseline wire toward `x_i`. Evaluate each wire on the singleton of `i` and on the complement of `S`, with all lines zero. Start with values `(1,0)`. At an OR choose a child that is one on the singleton. At an AND choose a child that is zero on the complement. The other required value holds automatically. The path terminates at `x_i`, the only input with this pair of values. Every wire on it contains `i` in its point support and has support contained in `S`. In the forward direction, the first wire whose support has size at least two gives an exit from `R_i` to a support of size at least two contained in `S`. Distinct rows of a linear incidence system, meaning rows with at most one shared point, give distinct exits.

For another row `l` incident to `i`, use the positive assignment `(x_i,y_l)` and the negative assignment consisting of `y_l` and all points outside `N(l)`. The same backward trace from the output again terminates at `x_i`: `y_l` belongs to both assignments, and only `x_i` belongs to the positive alone. The forward path exits `R_i`, and the target's point support is contained in `N(l)`. It cannot equal `{i}`, since a pure `{i}` successor of an `R_i` vertex also belongs to `R_i`. The target might have singleton support different from `{i}`, which is harmless: it cannot be any of the exits to a multipoint support for a different present row. When `N(l)={i}` the target must have empty point support.

## Exact private degree-two core

Let there be `k` point centers, with at least one private degree-one line per center. Suppose every nonprivate line has degree two and no two of them have the same endpoints. Let `s` count nonprivate lines and `t` count the present nonprivate lines. For every center, its private line supplies one extra exit beyond one exit per incident present nonprivate line. Summing the pure-carrier surplus bounds therefore gives at least `2t`. The `s-t` missing nonprivate lines have incomparable neighborhoods, and their first branching wires have empty point support, so contribute `s-t` further surplus disjoint from those carriers. The total surplus is at least `s+t`, hence at least `s`.

If the number of private lines is `a`, the graph has `k+a+s` input variables and `a+2s` edges. Its point-star circuit has `a+2s+k-1` gates, exactly `inputs-1+s`. The unrestricted lower bound just proved matches it. A `k`-point arc with a tangent per point gives this type of core on restriction. The full conic in an odd-prime coordinate plane has `k=q+1`, one tangent per center, and `s=binom(k,2)`.

## Every linear incidence system with line degree at most two

The previous statement extends to the case where some or all private tangents are absent. Discard isolated inputs and assume the incidence graph has at least one edge. Form the simple graph `H` of degree-two lines on the point centers. Include all point centers as vertices of `H`, including centers attached only to private lines. Let `h` count connected components of `H` that are trees and have no private line anywhere in the component. Write `D` for the centers with neither a private line nor an incident missing degree-two line.

For every point center outside `D`, get one additional exit beyond its incident present degree-two lines, using a private line or the two-assignment path for an incident missing line. The pure-carrier estimate is then `2t-|D|`. Distinct missing degree-two line first forks supply another `s-t` units. The resulting surplus is at least `s+t-|D|`.

Each connected component of `H[D]` with a neighbor outside `D` has at least `v-1` internal present edges and at least one present edge to the outside, where `v` is its number of vertices. All these edges are distinct across components of `H[D]`. Each component closed in `H` has no private line and has all its edges present. A closed component has at least `v` edges unless it is a tree, when it has `v-1`. Thus `t≥|D|-h` and the total surplus is at least `s-h`.

If `k` is the number of centers and `a` the number of private lines, the size lower bound is `k+a+2s-h-1`. There is a cover of size `k-h`: take all centers in each component other than the `h` trees and take all degree-two line vertices in each of those trees. This cover is minimum. In a component with a private line, match the root center to that line and each other center to the line of its parent edge in a spanning tree. In a component with a cycle, match each cycle vertex to the line of its following edge and extend with a spanning forest rooted at the cycle. In one of the `h` trees, matching each nonroot center to its parent-edge line saturates the line side. These disjoint matchings have total size `k-h`. In each component the cover chosen is one whole side, so its stars partition the incident edge set. The corresponding circuit has `|E|+k-h-1=k+a+2s-h-1` gates. This proves the exact unrestricted bound `|E|+minimum vertex cover size-1` throughout this class, including the incidence graphs obtained by subdividing the edges of any simple graph once. The observation that a minimum center degree of two suffices without private lines is due to the fresh-math strategy.

## Missing rows in a full plane

For a plane of order `q`, write `d=q+1`, `N=q²+q+1`, and let `M` be the missing lines, `m=|M|`, `U` their union. Give each point one exit for every incident present line, and one more exit if it belongs to `U`, using any incident missing line. The root-connected pure carriers give at least `d(N-m)+|U|-N` total surplus. The distinct first branching wires of all missing rows give `m` more. Thus

`gates ≥ N(q+2)-1 - qm + |U|`.

One may also interchange the two colors. The formula proves the target when `|U|≥qm`, including all `m≤3` and missing lines contained in a pencil. A pencil of `m>0` lines covers `qm+1` points. When `m=0`, the point-carrier exits alone give exactly the desired lower bound. The expression loses information when many missing lines have different intersections. Neither the identity for the sum of locally restricted surpluses nor a compensating charge for this loss has been established.
