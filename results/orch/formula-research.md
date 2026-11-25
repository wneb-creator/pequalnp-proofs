# Formula route and duplicate-gate fallback for L-meta-9811

Research date: 2026-11-25 UTC. Repository and primary-source searches did not
find a theorem eliminating negations at no size increase for arbitrary
formulas computing this bipartite C4-free quadratic graph function. This is
not a claim that such a theorem does not exist.

## The exact cost conversion needed

For a fanout-one output tree with B binary gates and U unary NOT gates,
after removing irrelevant/constants-only parts, the number of input-literal
occurrences is B+1. Pushing NOT gates to input literals by De Morgan laws
preserves the number of binary gates in a tree; the resulting conventional
De Morgan formula treats negated literals as free. Thus an S-gate formula
with S=B+U gives a De Morgan formula with at most S+1 leaves.

Consequently a lower bound of 26 leaves for arbitrary De Morgan formulas
would exclude every formula with at most 24 counted gates. A monotone-only
26-leaf bound does not suffice. Leaf count and counted-NOT gate count must
not be interchanged.

## Repository result

`lean/PEqualNP/Defs/DeMorganFormula.lean` defines `DMFormula`, with AND/OR
binary nodes and positive or negative input literals. `HasLeafSize` counts
literal occurrences, including repeated variables, and does not count
negation separately.

`lean/PEqualNP/Outside/L_meta_121.lean:424` proves the exact arbitrary-formula
bound for the path graph on n vertices:

```
2 ≤ n → (HasLeafSize n pathFunction s ↔ n + n/2 ≤ s+1)
```

For n=14 this is 20 leaves, not the 26 needed here. The theorem is for path
adjacency `i.val+1=j.val`, not an arbitrary C4-free graph. A focused search
of formula/fanout references found no broader applicable `HasLeafSize`
theorem. Search lists and theorem headers remain in the job scratch directory
as `formula-files.txt`, `formula-focused-files.txt`, and
`formula-theorem-headers.txt`.

## Primary literature actually read

Ilan Newman and Avi Wigderson, *Lower Bounds on Formula Size of Boolean
Functions using Hypergraph-Entropy*, Theorem 2 and the accompanying
Krichevskii lemma, Section 2.2. Read 2026-11-25:
https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/HNW96/entropy.pdf

Their model is an AND/OR tree with positive or negated literals; size means
number of leaves. Theorem 2 gives L(f) ≥ n H(G(f)) when f rejects singleton
inputs, with the relevant singleton contribution zero. Section 1 property
4(d) gives H(G) ≤ 1 for bipartite graphs on all n vertices. Thus this method
can yield at most 14 for the present graph, far below 26. The lemma produces
a monotone function accepting the original two-element positive inputs and
rejecting singletons, at no larger leaf size, but may add two-element positive
inputs. It therefore does not preserve the target graph or its C4-freeness.

Stasys Jukna, *On Graph Complexity*, ECCC TR04-005 revision 1, Section 7.2
and Theorem 7.3. Read 2026-11-25:
https://eccc.weizmann.ac.il/report/2004/005/revision/1/download/

The triangle-free/C4-free theorem in this source concerns monotone formulas,
with lower bound |E|/2, and monotone circuit depth. It does not provide an
exact arbitrary-formula gate bound. Its graph-representation magnification
result concerns correctness on selected two-element assignments, which is
weaker than computing the target graph function on all assignments.

## Ready duplicate-gate lemma, if needed later

`lean/PEqualNP/Outside/L_meta_4105.lean:141` contains the private lemma
`no_duplicate_wire`. For an `IsMinimalCircuit n C`, each gate output differs
on some assignment from every earlier wire:

```
i < n+j → j < C.gates.length →
∃ x, wires(C,x)[i] ≠ wires(C,x)[n+j]
```

The proof constructs D by deleting gate j and redirecting every later source
and the circuit output through `aliasWire`. The full dependency block is
lines 5–201, about 9.3 KB / 197 lines; `no_const_gate` and the later gate-shape
classification are unnecessary. For a circuit minimal only among AO circuits,
the same construction keeps each operation unchanged and preserves source
list lengths. One can establish `Monotone2 D` and invoke AO minimality in
place of the unrestricted-minimality call at line 197. This adaptation has
not been compiled here.

An OR gate reading the same earlier wire twice computes that earlier wire,
so the lemma excludes it in a minimal circuit. However the current
`no_empty_or_chain` argument already excludes the empty-primary extra-OR
case structurally; the lower-bound agent confirmed no minimality or
duplicate-removal premise is needed for that case.
