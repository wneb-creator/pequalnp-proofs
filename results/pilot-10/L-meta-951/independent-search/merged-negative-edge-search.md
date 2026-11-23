# Deferred synthesis optimization for the E3 core

This is a search design, not a proof or a completed solver result.

The E3 family is 013,024,0567,125,1468,2378 on nine variables. Its target sum
is fifteen. The reviewed graph equality argument says any fourteen-gate
counterexample has one NOT with exactly one ordinary consumer and no ordinary
gate whose only route to an output goes through that NOT. These graph premises
are not fully kernel checked in this work.

Merge the NOT and its consumer into one node of cost two. The resulting
synthesis problem has thirteen nodes, one of which is one of these asymmetric
operations:

* q = (NOT h) AND p;
* q = (NOT h) OR p.

All other nodes are ordinary binary AND/OR of cost one. The pair (h,p) must not
be sorted as if the special operation were commutative. Require exactly one
special node, and its h input to be a prior internal Good gate if adopting the
additional tight-ownership premise. That premise is a separately argued
condition; a conditional search must label it explicitly.

The standard semantic verification must reevaluate all 512 assignments. A
candidate is translated to the actual Lean gate model by inserting a NOT of h
immediately before the special node, replacing that node by the corresponding
ordinary AND/OR, and renumbering subsequent wire references. This uses fourteen
actual gates. Any free true constant must still be accounted for, though reduced
function-distinct models normally cannot use constants nontrivially.

For positive-path pruning, the h-to-special-node edge is negative and must be
excluded. The p-to-special-node edge remains positive. All ordinary edges into
ordinary nodes remain positive. Every node must be a requested output or have
a positive path to one. Standard topological ordering still treats both edges
as dependencies, so the negative edge is excluded only from positive-path
pruning, not from circuit evaluation or dependency ordering.

A positive control can reuse goodsource_control11: delete its NOT node and
merge it with the first negative-chain OR, giving ten nodes of total cost
eleven. Its outputs are OR01 and OR2345, with target sum four, so it is merely
a consistency control and not a lower-bound counterexample.

This optimization was deliberately not launched before the scheduled gap
reassessment; current E3 queries and their logs remain authoritative.
