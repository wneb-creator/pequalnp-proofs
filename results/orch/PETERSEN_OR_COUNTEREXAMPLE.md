# Eight OR gates for a ten-edge graph of girth at least five

`lemmas/PetersenOrCounterexample.lean` gives an ordinary-kernel-checked counterexample to the proposed separate lower bound `number of OR gates ≥ number of graph edges − 1`. It does not refute L-meta-1031: its circuit has fourteen gates, while this graph has a thirteen-gate vertex-cover circuit.

The eight-vertex graph has edges 04, 05, 07, 13, 15, 16, 23, 24, 37 and 46. It is the Petersen graph with two adjacent vertices deleted. Lean verifies that it has ten edges, no triangles and no four-cycles.

Writing juxtaposition for AND, define

```
a = x1 OR x4
b = x0 OR x3
c = x3 OR x4
d = x5 OR (a b c)
e = (x6 a) OR (x2 c)
f = x0 OR x1
output = e OR ((d f) OR (x7 b))
```

This uses eight OR gates and six binary AND gates. The AND-only triple conjunction uses two gates. Lean verifies the explicit fourteen-gate circuit on all Boolean assignments and proves public binary-monotone legality, the OR count, total size, and the strict inequality `10 > 8 + 1`. Its first AND owns the disjoint graph edges 04 and 13, explaining why this is not a circuit satisfying the posted star-ownership conclusion.

The exact native SAT model found the original eight-OR witness in 0.04 seconds. Its decoder independently checked all 8,361 CNF clauses and all 256 Boolean inputs. The displayed algebra removes absorption redundancies and has a separate ordinary Lean proof. Complete small SAT artifacts are in `native-petersen-minus2/`.

Lean source: 64 lines, SHA256 `4d99e41a42ec5d0a68874bfdcf786ceca1599919258573fae6b2c46022b0a4c6`. Build exit 0 with empty complete log `petersen-or-lean-03.log`. Axiom audit `petersen-or-axioms.log` reports only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The finite lemmas use ordinary `decide +kernel`; no native reflection is used.

The library's L-meta-3143 separately establishes a total-size lower bound of thirteen for an isomorphic graph. The vertex relabeling from this graph to that file's graph is `[1,4,3,7,2,0,6,5]`, independently identified by the library-search agent. That existing lower bound makes a twelve-gate SAT search on this graph unnecessary.
