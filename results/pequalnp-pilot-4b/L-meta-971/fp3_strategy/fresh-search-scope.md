# L-meta-971 independent probe

> Archive note: These are historical research-phase notes. Statements that no repository files were changed describe that phase, before this authorized archival checkpoint. Scratch paths and unpreserved search artifacts below are provenance, not archive dependencies.

The 27-gate Heawood lower bound remains unproved and unrefuted by this work. The direct star construction uses 27 gates. A proposed split into at least 20 OR gates and at least 7 AND gates remains plausible but unproved here.

## Exact finite searches

`free_and.py` treats AND gates as free: every counted OR gate has two operands, each an arbitrary conjunction of inputs and earlier OR outputs; the final output is another arbitrary conjunction. Empty conjunctions and constant false factors are allowed. This represents every monotone circuit with the specified OR budget, regardless of its AND count.

For exact monotone correctness it suffices to accept every graph-edge support and reject every maximal independent set. Monotonicity extends those constraints to all assignments. The Heawood graph gives 21 positive rows and 37 negative rows.

| Graph and constraint | Result | Time |
|---|---|---:|
| C5, at most 3 OR, exact function | UNSAT | 0.016 s |
| C6, at most 4 OR, exact function | UNSAT | 0.228 s |
| C5, at most 3 OR, only weights 0,1,2 | UNSAT | 0.014 s |
| C6, at most 4 OR, only weights 0,1,2 | UNSAT | 0.601 s |
| Heawood, at most 19 OR, exact function | UNKNOWN: timeout | 60 s |
| Dual Heawood, at most 6 OR, exact function | UNKNOWN: timeout | 60 s |

The last row equivalently asks for an original Heawood circuit with at most 6 AND gates and any number of OR gates. SMT-LIB instances and JSON results are beside this report. These are external Z3 solver results, not Lean-checked certificates. Earlier fixed-total-gate probes were weaker: C5 with seven total gates and at most three ORs was UNSAT, while C6 with eight total gates and at most four ORs timed out.

Both Heawood searches were repeated with a sound symmetry constraint that lexicographically orders the two conjunction-selection masks of each OR gate. Both repetitions again timed out after 60 seconds; their filenames end in `_sym`.

## Counterexample to the cumulative safe-meet partition invariant

This proposed invariant is false even for the five-vertex path with edges

```
ab, bc, cd, de.
```

Use only two OR gates, with AND gates free:

```
g = ab OR de
h = g OR c.
```

The three available AND-meets `g`, `b AND h`, and `d AND h` are all globally bounded above by the path edge function. Their accepted edge-pair sets are respectively

```
{ab,de}, {ab,bc}, {cd,de}.
```

They therefore connect all four target edges, with partition rank three, despite only two OR gates. Safety is exact on all assignments: expanding either product gives only monomials containing a path edge. `validate_partition_counterexample.py` independently checks all 32 assignments. The randomized search also found equivalent examples inside C6 and a rank-four example with three ORs inside C5.

This does not refute the desired OR-count lower bound: combining the safe pieces into the entire target still requires another OR gate. It specifically refutes using the connected-component rank of all available safe meets as the global potential, even with credit carried over from previous unsafe ORs.

## Local decrease of safe-meet cover number also fails

A less aggressive potential is the minimum number of available safe meets needed to cover all target edges. Its decrease in one OR step can still exceed one. On C5 with edges `ab,bc,cd,de,ea`, take

```
g1 = a OR b
g2 = (e AND g1) OR (c AND d)
g3 = a OR c.
```

Before adding `g3`, every safe meet accepts at most one edge, so the covering number is five. Afterwards `b AND g3` accepts the pair edges `ab,bc`, while `g2 AND g3` accepts `cd,ea`; the single edge `de` completes a three-piece cover. These are globally safe. Thus one OR lowers the cover number by two, spending credit from earlier ORs. The random-prefix checker enumerated the complete finite AND-closure at each prefix; its trace is `c5_partition_cover.json`.

A cumulative bound `number of ORs + minimum safe cover size >= number of edges` would suffice, but is equivalent to the original OR bound: joining a safe cover of size c requires only c-1 further ORs. Neither this equivalent restatement nor the failed local decrease establishes the target.

## Concrete remaining proof issue

A possible stronger claim is that a monotone circuit with no true singleton and a C4-free graph of true pairs has at most one more true pair than its OR count. The small cycle searches support this, but no proof is available. In a first-OR induction, if either operand is a monomial of size at least two, suppressing it can change at most one pair input while removing an OR; this case is easy. The unresolved case is a first OR between two distinct singleton inputs. Sharing that OR across different pair contexts can save gates locally; later AND filters remove unwanted pairs. Any valid count must account for that filtering and for the cost of eventually joining all surviving safe pieces. The failed partition invariant forgets the latter cost.
