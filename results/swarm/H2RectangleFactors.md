# Matching bound for a product of rectangle DNFs

Status: mathematical proof, independently reviewed; not formalized in Lean in
this file. This is a helper result for L-meta-4970, not a proof or refutation of
that gap. Rectangle occurrences are counted separately in each factor; the
result does not account for arbitrary circuit sharing.

Let `E` be a nonempty finite bipartite graph with no four-cycle. Write `F_E`
for the Boolean function that is true when the selected left and right vertices
contain an edge of `E`. Suppose, **on every Boolean assignment**,

`F_E = AND_{i=1..t} F_{R_i}`, where `R_i = UNION_{j=1..r_i} (A_ij × B_ij)`.

Here `t >= 1`, all `r_i >= 1`, and a rectangle term means
`OR(A_ij) AND OR(B_ij)`. Rectangles may be empty. Put `N = SUM_i r_i`.
For every matching `M` in `E`, with `m = |M|`,

`m <= N - t + 1 = 1 + SUM_i (r_i - 1)`.

Equality only on edge-pair assignments would not suffice for this result.

## Controllers and owners

Every factor contains every edge of `E`: evaluate the full equality on that
edge pair. For a matched edge `(a,b)`, evaluate instead on the left singleton
`{a}` and the set of all right nonneighbors of `a`. The output is false, so
some factor is false. That factor is true on `(a,b)`; choose one of its
rectangles containing `(a,b)`. Its right side must be contained in `N_E(a)`,
since otherwise it would be true on the false baseline. Assign this rectangle
the row owner `a`.

The symmetric baseline gives a rectangle with column owner `b`, whose left
side is contained in `N_E(b)`. Rectangles are tagged by both factor and index.
The row assignment is injective: a rectangle assigned to two distinct matched
rows would contain both matched columns in both rows' neighborhoods, producing
a four-cycle. The column assignment is injective by the same argument.

Thus exactly `m` rectangles have a row owner and exactly `m` have a column
owner. Each rectangle has at most one owner of each kind. Its number of missing
owners is zero, one, or two; the total number of missing owners is

`D = 2N - 2m`, which is even.

Call a rectangle doubly owned when it has both owners. If its owners are `a`
and `b`, its central pair `(a,b)` is an edge of `E`.

That central edge cannot lie in a different doubly owned rectangle. Indeed,
if the latter has owners `c,d`, all four pairs `(a,b)`, `(c,b)`, `(a,d)`, and
`(c,d)` are edges, using the latter rectangle's containment and controller
properties. The global injections ensure `a != c` and `b != d`, contradicting
the absence of a four-cycle.

In particular, every other factor must cover a doubly owned rectangle's central
edge using one of its rectangles that is not doubly owned.

## Removing a factor with one rectangle

If a factor is the single rectangle `A × B`, then `E` is contained in it.
Project every assignment by setting variables outside `A` and `B` to false.
This preserves `F_E`. In every other rectangle, replace its sides by their
intersections with `A` and `B`.

If another factor remains, that factor implies `OR(A) AND OR(B)`: every one
of its projected rectangle terms does. Consequently, the product of the
remaining projected factors equals `F_E` on all assignments, and the factor
`A × B` can be deleted. Retain empty rectangles if necessary, so `N` and `t`
both decrease by exactly one. Recompute the controller assignments for this
new factorization. Nonempty `E` ensures that no remaining factor is identically
false.

Repeat until either one factor remains or all factors have at least two
rectangles. In the one-factor case the row injection gives `m <= N`, which is
the desired bound. The quantity `N - t` is preserved by every deletion.

## Counting the missing owners

It remains to consider `r_i >= 2` for every factor, using freshly chosen owners.

If some factor consists entirely of doubly owned rectangles, every other
factor has no doubly owned rectangle. Otherwise the central edge of a doubly
owned rectangle in another factor would have to belong to a doubly owned
rectangle in the first factor, which was ruled out above. Each of those other
factors therefore contributes at least two missing owners, and
`D >= 2(t - 1)`.

Otherwise every factor contributes at least one missing owner. Call a factor
thin if it contributes exactly one. A thin factor has exactly one singly owned
rectangle, all its other rectangles are doubly owned, and there is at least
one of the latter because `r_i >= 2`.

There cannot be four thin factors. Among their four singly owned rectangles,
choose two with the same kind of owner. Suppose these are row owners `a_1`
and `a_2`; the column-owner case is symmetric. Choose a doubly owned rectangle
from each of the other two thin factors, with central edges `(c_3,b_3)` and
`(c_4,b_4)`. Each central edge must belong to the unique rectangle that is not
doubly owned in each of the first two factors. Their row-controller properties
therefore give all four edges

`(a_1,b_3), (a_1,b_4), (a_2,b_3), (a_2,b_4)`.

The global owner injections give `a_1 != a_2` and `b_3 != b_4`. This is a
four-cycle, a contradiction.

There are consequently at most three thin factors. If their number is `s`,
all other factors contribute at least two missing owners, so

`D >= s + 2(t - s) = 2t - s >= 2t - 3`.

Since `D` is even, `D >= 2t - 2`. Substituting `D = 2N - 2m` proves
`m <= N - t + 1`.

## Scope and provenance

The baseline-controller and two-factor owner argument came from the swarm's
earlier work. Helper-2 supplied the four-thin-factor contradiction and the
general missing-owner count, together with the full-function absorption step.
The statement, controller construction, absorption, and counting argument
received independent mathematical review. This document makes no Lean-checker
claim. It does not establish the served OR-gate bound or handle arbitrary
dependencies between circuit factors.
