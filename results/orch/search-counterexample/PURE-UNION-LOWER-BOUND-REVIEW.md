# Independent audit: the restricted39-OR lower bound

The charging argument is sound for the following precise architecture: there are13line-input variables; every paid gate is a binary OR of earlier pure-union wires; each of13outputs is an arbitrary free conjunction of available wires. Output p must accept each singleton line in its four-line pencil T_p and reject every four-line cap disjoint from T_p. Under these assumptions, at least39OR gates are necessary. This is an audited mathematical argument, not a Lean theorem and not the unrestricted51-OR statement.

## Guards and the geometric inequality

An output factor must have support containing T_p, because that factor is true on all four required singleton assignments. At each required cap, at least one such factor is false. Call an available union support useful when it contains a pencil and is disjoint from some four-cap. A useful support contains at most three pencils: the points avoided by any four-cap form a three-point set. Repeated equal support nodes may be counted separately without weakening the argument.

For a target p with no exact-pencil union node, divide its useful guards into a private guards, containing only T_p, and b shared guards, containing at least one other pencil. Every private guard strictly contains T_p, so choose an extra line from it. For every shared guard choose one other pencil point q.

The54four-caps disjoint from T_p correspond bijectively to pairs {q,r} of other points in different lines through p. The associated graph is K_{3,3,3,3}. If up to two extra private lines are chosen, restrict to vertices outside their union. Each remaining graph edge corresponds to a cap containing all selected extra lines, so all private guards are true there. Some shared guard must therefore be false. Its chosen other pencil point is an endpoint of that graph edge. The chosen shared points consequently form a vertex cover, with cardinality at most b.

With zero, one or two distinct chosen extra lines, the remaining part sizes are respectively (3,3,3,3), (2,2,2,2), and (2,1,1,1). Their minimum vertex-cover sizes are9,6,3. If the two chosen lines coincide, the minimum is6, which is stronger. Thus `3a+b ≥ 9` whenever a≤2; it is immediate for a≥3. Each target without an exact-pencil node therefore receives at least3units when private guards give credit1 and shared guards give credit1/3.

Each guard gives at most1total credit: a private guard belongs to one pencil, and a shared useful guard contains at most three pencils. This count is over the targets lacking exact-pencil nodes only.

## Exact pencils and disjoint ancestry

If an exact-pencil node exists for p, its pure-union ancestry contains at least three distinct nontrivial OR nodes: four distinct input variables cannot be united by fewer than three binary joins. Every ancestor support is contained in T_p. For distinct pencils p,q, these nontrivial ancestry nodes are disjoint, because T_p and T_q intersect in only one line. Such an ancestor cannot be a useful guard for any different pencil, so these charges do not overlap the preceding guard charges for targets lacking exact nodes.

If e targets have exact-pencil nodes, select three ancestry nodes for each. The other13−e targets require at least3units each from disjointly charged guard nodes. Therefore the total number of OR gates is at least `3e+3(13−e)=39`.

There is also equality rigidity. If exactly39gates existed with a target lacking an exact-pencil node, every gate would have to receive total credit1. Consider the earliest useful guard for any such target p. Its two parents are inputs or earlier OR nodes; the latter cannot be guards for any missing-exact target by minimality, so equality forces them to be selected ancestry nodes for exact pencils. Each parent then meets T_p in at most one line. Their union cannot contain all four lines of T_p, a contradiction. Thus every39-gate solution in this restricted architecture computes all13exact pencils.

## Independent finite checks and limitation

`audit_pure_union_lower_bound.py` independently checked3,016useful support masks;702cap/graph-edge correspondences;37,206private-extra incidences;5,616shared-pencil incidences; and715residual vertex-cover cases, including coincident chosen lines. The residual vertex-cover numbers were also checked by enumerating independent sets, not merely by applying the multipartite formula. Complete results are in `pure-union-lower-bound-independent-audit.{json,log}`.

The proof does not extend as written to free AND gates inside OR operands. An exact-pencil singleton signature can then arise by intersection filtering rather than by union ancestry contained in that pencil. That breaks the ancestry charge and the earliest-guard equality argument. The pending arbitrary-AND50-OR search is unaffected; the restricted pure-union38-OR query has no solution if its encoding matches the stated architecture.
