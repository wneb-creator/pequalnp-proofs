# Exact lower bound from a layer of rectangle terms

This is a mathematical argument. It has not been formalized in Lean. It applies to restricted classes of circuits for the stated plane function.

## Arbitrary monotone postprocessing

Let `G=(P,L,E)` be a finite bipartite graph with at least one edge and no 4-cycle. A rectangle term is a physical binary AND gate whose two inputs are pure binary OR networks for `A ⊆ P` and `B ⊆ L`, with nonempty supports. The terms may share all pure OR computations. The output is computed by an arbitrary monotone binary circuit whose inputs are the outputs of the terms. Shared term and combining gates are permitted. Every input-to-output path in this construction passes through a term. There is no bound on the depth of the combining circuit. Discard dead terms.

**Theorem.** Suppose every term with line support `B={l}` satisfies either `A ⊆ N(l)` or `|A ∩ N(l)| ≤ 1`. If the circuit computes `F_G`, it has at least `|E| + τ(G) − 1` gates, where `τ(G)` is the vertex-cover number. The transposed condition on point-singleton terms also suffices.

For each edge `(p,l)`, compare its positive two-input assignment with the independent assignment `M_p` consisting of `p` and all lines outside `N(p)`. At least one term must be true on the edge and false on `M_p`, since otherwise every term value on the edge would be bounded by its value on `M_p`, contradicting monotonicity of the combining circuit. Select one such term. Its rectangle satisfies `p ∈ A` and `l ∈ B ⊆ N(p)`.

* If `|B| ≥ 2`, assign the selected term to point `p`. No other point can be assigned that term, since two points cannot both be incident to two lines of `B`. Every edge selecting this term has center `p` and its line in `B`.
* If `B={l}` and `A ⊆ N(l)`, assign the term to line `l`. Every edge selecting it has point in `A`.
* If `B={l}` and `A` contains a nonneighbor, this term can serve at most one edge by hypothesis. Assign that edge's term to `l` and use no pure OR gates for it.

Let `t` be the number of distinct selected terms. The centers of these `t` terms form a vertex cover, so `t ≥ τ(G)`. We next count at least `|E|−t` pure OR gates. Within the group at a point `p`, let `s` be its number of terms and `U` the union of their line-side supports. The OR networks for the `s` outputs have at least `|U|−s` non-singleton-support gates. One proof contracts all singleton-support computations to their input label. Each remaining connected component of the union of the ancestor graphs contains an output, so there are at most `s` components. Counting input vertices, binary gates and arcs gives the stated bound. All counted supports have at least two elements and are contained in `N(p)`; none can be counted at a different point. The number of edges that selected these terms is at most `|U|`. Dually apply this argument on the point-variable side to the clean line-singleton terms at each line `l`. For each remaining dirty line-singleton term, the edge count is at most one and the claimed pure OR contribution per edge minus one per term is zero. Distinct line groups do not share charged gates, by absence of 4-cycles. Counted gates on opposite shores are also disjoint. Summing over the groups gives the bound `|E|−t`.

The circuit contains the `t` selected term AND gates. There are also at least `t−1` further joining gates. Indeed take one path from each selected term to the output. In their connected union each selected term is a source because its inputs are pure, while every nonsource has indegree at most two. The union therefore contains at least `t−1` nonsources, all of which lie downstream of a term and hence are disjoint from the pure input-OR computations. The total is at least `(|E|−t)+t+(t−1) ≥ |E|+τ(G)−1`.

In particular, a smaller circuit of this form must have a term `A × {l}` with at least two genuine neighbors of `l` and at least one nonneighbor in `A`, and a term `{p} × B` with the analogous property. Terms with both sides of size at least two may be arbitrary throughout the theorem.

**Whole-neighborhood terms.** Suppose each rectangle is `A × N(A)` or `N(B) × B`, where a set's neighborhood is the union of its members' neighborhoods. The sets may overlap, both types may be mixed, and the combiner can be any monotone circuit using only these terms. Every term whose line side is `{l}` is clean. For `N(B) × B` this follows directly. For `A × N(A)` with `N(A)={l}`, nonisolated vertices of `A` are all adjacent to `l`; isolated vertices may first be discarded from the graph and construction, or one may assume there are none. Hence the theorem applies to every nonisolated `C4`-free graph in this construction class. At a projective plane it gives `N(q+2)−1`. For the seven-point module it gives 34 since each point has degree four, every line has degree at most four, and regular edge counting from any point subset verifies Hall's condition for a matching saturating all seven points. This extension does not require that the rows have the same degree if their saturation is known by another argument.

## Independent one-shore preprocessing and the two-sided deficit bound

Let a primitive term be `u(X) AND v(Y)`, where the operands can be arbitrary monotone one-shore circuits that are shared among the terms. The two shores' preprocessing gates are disjoint. First allow extra point-only signals into the final monotone combining circuit. In the comparison of `(p,l)` with `M_p`, those extra signals agree. A separating term still exists. Write `A` and `B` for the sets of singleton inputs accepted by `u` and `v`. Its selection implies `p ∈ A`, `l ∈ B` and `v(L \ N(p))=0`. In particular `B ⊆ N(p)`.

For `s` arbitrary one-shore roots that all reject the complement of a set `U`, the number of distinct binary OR gates that both reject this complement and accept at least two singleton inputs is at least the size of the union of the roots' singleton supports minus `s`. At a wire rejecting the reference complement, take as its labels all singleton inputs accepted by the wire. Other wires receive no labels. At an AND rejecting the reference, choose a rejecting child. Its labels include the parent's labels. At an OR rejecting the reference, both children reject it and the parent's labels are the union of their labels. Starting with a frontier of the `s` roots, eliminate wires in reverse topological order. A wire with at most one label spends one unit of frontier size. A multilateral OR can replace one frontier vertex with two and charges at most one new gate. A chosen AND operand replaces one vertex by one. This gives the asserted bound. All charged gates have singleton support contained in `U`. This counting principle is represented by `Mergers.frontier_bound` and `BoundaryMerger.labels_step` in the local Lean files.

Call a term on singleton line support `B={l}` dangerous if `u(P \ N(l))=1` and at least two points of `N(l)` belong to `A`. A singleton-point dangerous term is defined by transposition. The basic theorem extends with no dangerous singleton-line terms. For line-side roots use the complement of `N(p)` as reference, for clean point-side roots use the complement of `N(l)`, and assign at most one edge to each remaining thin singleton-line term. Nonlinear computations recognizing multiple input variables simultaneously are therefore permitted in the side networks. The theorem also permits arbitrarily many dangerous terms all bearing one fixed line label. For that label `l`, restrict the point side to `N(l)` and use all-zero reference. Every charged gate accepts at least two distinct original singleton labels in `N(l)`. It is disjoint from every clean group's charged gates since those have their entire singleton support in another line's neighborhood.

Now exclude both kinds of raw bypass, so the dual argument also applies. Let `g_P,g_L` count distinct dangerous term gates and `k_P,k_L` count their distinct singleton labels. Let `d_P,d_L` be the maximum degrees of points and lines. For each line with any dangerous terms, group all selected line-singleton terms by that label. Keep one such line under the restricted argument and drop the pure-OR charges at the other dangerous line labels. Each dropped label costs at most `d_L−1` in the bound, since its terms serve at most `d_L` distinct edges and any nonempty group contains at least one term. All `g_P` dangerous singleton-point terms are unselected in the row comparisons. For their only potentially positive point `p`, they accept `M_p`. At any other singleton point they already reject the positive edge. The total number of physical term gates is therefore at least the number selected plus `g_P`. Counting every physical term and the at least one-less joining gates gives two more units for each unselected term. Consequently

```
size ≥ |E|+τ−1 + 2g_P − (d_L−1) max(k_L−1,0),
size ≥ |E|+τ−1 + 2g_L − (d_P−1) max(k_P−1,0).
```

In particular if both maximum degrees are at most three, every such circuit has the full `|E|+τ−1` lower bound, with arbitrary dirty terms on both shores. For a strict improvement both `k_P` and `k_L` would be positive, and the two inequalities would require `2k_P+1 ≤ 2(k_L−1)` and `2k_L+1 ≤ 2(k_P−1)`, a contradiction. With maximum degree four on both shores, strict improvement forces at least four dangerous labels on each shore by adding the inequalities with the smaller of the two labels isolated.

For the seven-point order-three module with 28 edges and 12 nonempty lines, the point degree is four and the maximum line degree is three. The inequalities for a strict improvement give `k_L ≥ k_P+2` and `2k_L+1 ≤ 3(k_P−1)`, whence `k_P≥8` despite there being only seven points. This rules out all circuits with the described primitive cut at 33 gates and proves its 34-gate optimum in this class. The asymmetric-degree deduction is due to the root agent.

For `AG(2,3)`, the same asymmetric degrees require `k_P≥8`, `k_L≥10`. There are then at least 18 primitive gates and 17 joining gates. A pure side circuit with `r` gates can put at most `binom(r+1,2)` different unordered pairs of singleton input labels together on the support of any of its wires, counting the union of all such pairs. In fact each undirected component with `r_i` gates has at most `r_i+1` input labels by the indegree bound, and summing `binom(r_i+1,2)` gives at most `binom(r+1,2)`. Each dangerous line label has two distinct accepted point neighbors, and different lines give different pairs. Hence the point-side network has at least four gates. If it has exactly four and recognizes the ten required pairs, equality forces a connected component on five point inputs and all ten pairs must determine distinct affine lines. These five points would have no three collinear. Each of the four affine directions has at most two disjoint pairs among five such points, for a total of at most eight pairs. This rules out four point-side gates. The line-side network needs at least four gates for the eight distinct pairs arising from dangerous point labels. Thus the total size is at least `18+17+5+4=44`, attaining the point-star lower bound in this model. This excludes an entire class at the affine 43-gate search threshold and supplies no general lower bound for the unrestricted circuit.

## The full order-three plane with a rectangle-primitive cut

The unrestricted one-shore preprocessing and monotone postprocessing model above, with all input-to-output paths crossing a term, needs at least 64 gates for every plane of order three. This statement uses the mathematical counting argument and the small finite integer verification below. The model permits arbitrary dirty singleton terms on both shores and arbitrary nonlinear one-shore preprocessing gates. The unrestricted posted circuit model permits mixed OR computations and bypasses outside this construction.

Suppose the gate budget is 63 and let `t` be the total number of live term gates. Row and column selections may be fixed arbitrarily as in the previous argument, marking one distinguishing term for every edge in either orientation. Let `a,b` count the distinct dangerous singleton-point and singleton-line labels that have dangerous terms selected by the column and row selections, respectively. Nonselected dangerous labels are unnecessary in the count. The two-sided deficit proof with these selected labels in place of the global dangerous counts is unchanged. It gives `a,b≥4`. The corresponding selected dangerous terms are physically disjoint, as a term with a thick opposite support has at least two singleton labels on that shore. Thus `a+b≤t`.

Write `s_R` for the number of distinct row-selected terms, `r_R` for the number of these with line-side singleton support of cardinality at least two, and `f_L` for the number of selected dangerous line labels whose line group serves four edges with just one term. The line group at `l` consists of the selected row terms with line support exactly `{l}`. Use `s_C,r_C,f_P` for the transposed selection. Each selected term serves at most four edges, so `s_R,s_C≥13`. All dangerous singleton-point terms under consideration are absent from the row selection, so `s_R≤t−a`, and `s_C≤t−b` by symmetry.

The uncharged contribution of a dangerous line group after dropping its pure ORs is at most two except at its `f_L` full groups, where it is three. We can always charge the largest one by the one-line restriction argument. For `b>0` this gives

```
D_R ≤ 2b + f_L − (3 if f_L>0, else 2),
63 ≥ 52 + 2t − s_R − 1 − D_R.
```

The subtraction of two when `f_L=0` is sound even if all group contributions are smaller than two: after retaining one group at most `b−1` groups of cost at most two remain. Transpose for `D_C`.

Define `h(k)=ceil(16k/(k+3))` for `0≤k≤13`. Any `k` points have at least `h(k)` neighboring lines, and the dual bound holds. If `z_l` counts chosen points incident to a line, the sums of `z_l` and `z_l²` are `4k` and `k(k+3)` by the unique line through two points. Cauchy's inequality proves the statement for `k>0`, and `h(0)=0`. The centers of all row-selected terms cover all edges. There are at most `r_R` point centers and `s_R−r_R` line centers. At least one singleton-line term is selected for each of the `b` labels. Hence

```
0 ≤ r_R ≤ s_R−b,
h(max(0,13−r_R)) ≤ s_R−r_R.
```

At any full group its one term accepts all four point singletons of that line. These four point input wires lie in one connected component of the point-side preprocessor. Distinct full lines intersect, so all the `f_L` full-line neighborhoods together lie in one component when `f_L>0`. The component contains at least `h(f_L)` inputs and requires at least `h(f_L)−1` gates. The pair count used for the affine module supplies a second lower bound `j(b)`, the least `j` with `j(j+1)/2 ≥ b`. Thus the pure point-side gate count is at least `max(j(b),h(f_L)−1)`, and the line side at least `max(j(a),h(f_P)−1)`. Together with `2t−1` for the term and joining gates, these costs must fit the same budget of 63.

Finally at least `s_R+s_C−t` terms have been selected in both orientations. Each shared term either belongs to the `r_R` row terms with at least two line labels, belongs to the `r_C` column terms with at least two point labels, or has a singleton support on both shores. A term of the last kind serves at most one edge in either selection. If `w` such terms occur in both selections, the 52 assignments and the four-edge maximum per selected term give

```
w ≤ min(floor((4s_R−52)/3), floor((4s_C−52)/3)),
s_R+s_C−t ≤ r_R+r_C+w.
```

The following enumeration of a relaxation checks these integer inequalities. For fixed `t,a,b,s_R`, it takes the smallest feasible `f_L`, minimizing the point-side cost, and the largest feasible `r_R`, maximizing the overlap bound. Exchanging the shores permits `a≤b`. The tuples meeting all bounds except the final overlap test have the following counts and maximum allowed overlap minus required overlap.

| `t` | 17 | 18 | 19 | 20 | 21 | 22 | 23 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Tuples | 1 | 1 | 2 | 7 | 8 | 10 | 5 |
| Maximum difference | −9 | −8 | −6 | −5 | −3 | −2 | −2 |

All other `t` have zero tuples before the overlap test. Every displayed difference is negative. Thus a 63-gate circuit in this model is impossible. This calculation can be reproduced with Python's integer operations as follows.

```python
from collections import Counter
from functools import cache

def h(k):
    return (16*k + k + 2) // (k + 3)

def j(k):
    return next(r for r in range(14) if r*(r+1)//2 >= k)

@cache
def sides(t, absent, labels):
    result = []
    for s in range(13, t-absent+1):
        need = 52 + 2*t - s - 1 - 63
        fs = [f for f in range(labels+1)
              if 2*labels + f - (3 if f else 2) >= need]
        rs = [r for r in range(s-labels+1)
              if h(max(0, 13-r)) <= s-r]
        if fs and rs:
            result.append((s, max(rs), max(j(labels), h(min(fs))-1)))
    return result

count, best = Counter(), {}
for t in range(13, 33):
    for a in range(4, 14):
        for b in range(a, 14):
            if a+b > t:
                continue
            for sr, r, px in sides(t, a, b):
                for sc, c, py in sides(t, b, a):
                    if 2*t-1 + px+py > 63:
                        continue
                    count[t] += 1
                    w = min((4*sr-52)//3, (4*sc-52)//3)
                    gap = r+c+w - (sr+sc-t)
                    best[t] = max(best.get(t, -1000), gap)
assert all(gap < 0 for gap in best.values())
```

## Counting directly in a partition implementation

Let `G` be a `d`-regular bipartite graph with `N` vertices on each shore, `d ≥ 2`, and with no 4-cycle. Write `F_G(X,Y)` for the monotone edge function. For a partition of the points, a point-oriented quotient has one term for each nonempty block `A`, of the form

```
(OR of points in A) AND (OR of lines in the union of the neighborhoods of A).
```

Its factor is the OR of those terms. A line-oriented quotient interchanges the two shores. Each factor majorizes `F_G`. Consider any finite conjunction of these factors that equals `F_G` on every input. Allow all binary pure OR computations to be shared freely across factors, as well as shared term ANDs and shared gates combining the terms to produce the final output. The argument counts gates in the associated circuit, where the block terms are present and are ancestors of the output. It does not cover arbitrary Boolean rewrites that eliminate the individual terms.

**Theorem.** Such a circuit has at least `N(d+1)−1` gates. The ordinary point-star circuit attains this value. The number and orientations of the quotient factors are unrestricted.

Call a vertex visible if it is a singleton block of a quotient oriented on its own shore. Write `a,b` for the counts of visible points and lines and `v=a+b`. For each visible point `p`, the circuit contains its canonical term `x_p AND OR(N(p))`. The OR requires at least `d−1` binary gates of support size at least two. Every gate counted here depends on a subset of `N(p)`. Indeed, in a pure OR circuit no input dependency is lost along a path to its root. A pure OR output on `s` distinct labels requires at least `s−1` non-singleton gates, by contracting singleton-support gates and counting gates in the connected ancestor graph. The corresponding counts for different points are disjoint, since two neighborhoods share at most one line. Apply the same argument on the other shore to the visible lines. This counts `v(d−1)` pure OR gates and `v` distinct term AND gates.

For any marked subset of `t≥1` distinct term ANDs, at least `t−1` further gates join them to the output. To see this, take one directed path from each marked term to the output, and take the union. Every marked term is a source of this union because its inputs are pure and no other term can precede it. The union is connected as an undirected graph, every non-source has indegree at most two, and all vertices other than the marked sources are additional gates. Consequently there are at least `t−1` such gates. Its nonsource vertices are disjoint from the pure OR gates counted in the proof, because these are syntactically pure input-OR computations. Thus each marked term contributes one term gate and one unit toward the joining count, with a single overall subtraction of one.

If `v≥N`, the visible terms already give the claimed bound. Assume `v<N`. For each invisible point `p`, take the independent input consisting of this point and all the lines outside `N(p)`. Some factor rejects this input. Its graph is exact on row `p`, since its row contains `N(p)` by majorization and contains no other line by rejection. A point quotient can be exact on `p` only when `{p}` is its block. In fact distinct point neighborhoods have equal size at least two and share at most one line. Thus the chosen factor is line-oriented.

In the selected partition of lines, every block `B` meeting `N(p)` is contained in `N(p)`. Otherwise its term accepts a nonneighbor line together with point `p`. Mark the blocks containing at least one invisible neighbor of `p`. Each marked block has at least two lines, as a singleton would make that line visible. Within any given `p`, the marked blocks are disjoint. Blocks assigned to different points meet in at most one line. They also meet the neighborhoods of the visible points in at most one line. Hence their pure line OR gates contribute another `sum_B (|B|−1)` distinct gates, disjoint from the previous count. Their term gates are distinct from one another because each has a different line-side set `B`. They are distinct from canonical terms because the line side and the point neighborhood of `B` both have size at least two. Mark these term gates as well.

Write `J` for the number of edges with both endpoints invisible. At most `d v` edges are incident to the visible vertices, so `J≥d(N−v)`. Each of the `J` edges belongs to one of the marked blocks for its point, which gives `sum_B |B|≥J`. Each block has `|B|≤d` and therefore `|B|+1≥(d+1)|B|/d`. Combining the pure, term and joining counts gives

```
size ≥ v(d+1) − 1 + sum_B (|B|+1)
     ≥ v(d+1) − 1 + (d+1)J/d
     ≥ N(d+1) − 1.
```

When `v<N` there is an invisible edge and therefore a marked term, so the joining argument always has `t≥1`.

## Two arbitrary quadratic supergraph factors

Let `R` and `B` be sets of extra nonedges on the same shores as `G`. The identity `F_G = F_(G∪R) AND F_(G∪B)` on every input holds exactly when for every `(p,l)∈R` and `(s,t)∈B`, at least one of `(p,t)` and `(s,l)` belongs to `G`. Necessity follows from testing the assignment consisting of the four endpoints. For sufficiency, any assignment accepted by both factors either contains a true edge or contains one extra edge of each color, whose endpoints then contain a true edge. In particular the point projections of `R` and `B` are disjoint, and their line projections are disjoint.

Suppose the first supergraph coalesces all point neighborhoods in some block `P` with `|P|≥2`. Assume the plane has degree `d≥3`. For any `p∈P`, choose `s∈P` different from `p`. There are at least two distinct lines in `N(s)` outside `N(p)` and each supplies a red nonedge on row `p`. Every point of `P` belongs to the red point projection. A blue nonedge `(u,t)` therefore has `u` outside `P`. If `t` missed `p`, then `u` would be incident to both of the chosen lines through `s`, which contradicts the absence of a 4-cycle. It follows that `t` must be incident to every point in `P`. A noncollinear block thus forces the second supergraph to equal `G`. A collinear block confines every blue addition to the common line.

This also excludes a two-factor exact conjunction when both factors are proper quotients, even if either factor coarsens both coordinates. Any proper coordinate partition merges two points or two lines. A point merge changes at least two columns, since `d−1≥2`; a line merge changes at least two columns, since the two line neighborhoods are incomparable. Dually every merge changes at least two rows. The one-column or one-row restriction from the first merge precludes a proper quotient on the other factor.
