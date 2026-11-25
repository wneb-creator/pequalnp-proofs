The six-literal local repair experiment
=======================================

Run from the repository root:

```
python3 results/orch/finite/literal_six_local_budget.py
```

The variables are `z,p,q,r,a,b`, numbered `0,1,2,3,4,5`. Consider

```
g = (z OR p) AND (z OR q)
qgate = (z OR r) AND (a OR b)
j = g AND qgate.
```

For the graph with edges `za,zb,pq,ra`, the top signal `j` is below the graph
function; the first two AND gates own graph edges, and `j` owns none. This
graph is a forest. In a minimum correct full circuit containing this local
hybrid `g`, the mandatory edge `pq` follows from the separately proved
singleton-pivot lemma; the local cluster alone does not imply that edge.

Deleting all three AND gates and injecting a single safe signal that covers
every graph edge accepted by either predecessor requires that signal to be
the complete graph function on these six variables. The experiment gives all
six raw inputs, both constants, and all four original OR outputs for free,
and permits arbitrary binary AND/OR gates with sharing. It enumerates all
semantic states through three new gates and tests every possible final gate
at depth four. No solution uses four or fewer new gates. A five-gate solution
is verified on all 64 assignments:

```
(p AND q) OR (a AND (z OR r)) OR (z AND b).
```

The final-gate scan first filters OR operands to functions below the target
and AND operands to functions above the target; these are necessary
conditions, so this filtering is exhaustive. Duplicate available truth
tables are omitted because any use can be redirected to the earlier signal.
States are sets of available truth tables; their order/history has no effect
on future semantic reachability. Both free constants make this lower bound
at least as permissive as the actual circuit language.

The result rules out this particular three-slot protected-signal repair.
It does not rule out redirecting individual predecessor wires, reclaiming
old OR sources, or using other parts of the circuit. It does not refute the
posted ownership-existence theorem, which has separately been proved for
all forests in `../lemmas/forest_route.lean`. The finite lower bound here is
computational evidence only, with no Lean certificate.

The program also enumerates every graph on these six vertices containing
the three forced edges `za,zb,pq` and having no triangle or four-cycle.
There are 76. Of those, 42 contain neither additional rectangle edge `ra`
nor `rb`, 17 contain `ra`, and 17 contain `rb`. Both cannot occur together,
since they and `za,zb` would make a four-cycle. Extra graph edges outside
these six vertices are not enumerated.
