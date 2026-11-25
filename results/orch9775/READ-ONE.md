# Checked conditional lower bound for L-meta-9775

`ReadOneFloor.twenty_five` proves that a circuit computing the posted 14-input
graph function has at least 25 gates if it satisfies both `TopForm.IsAO2 14 C`
and `ReadK.IsReadK 14 C 1`.

`IsAO2` requires AND/OR gates with exactly two strictly earlier operands.
`IsReadK ... 1` is a semantic proof-tree condition: every prime implicant has
an accepting proof tree that reads each variable at most once. It is not a
restriction on the total number of gate inputs that use a variable. The theorem
does not exclude arbitrary monotone circuits of size 24, and does not prove or
refute the posted statement.

The specialization uses the checked upstream theorem
`PEqualNP.Outside.L_meta_2237`. `GraphFacts` supplies the exact graph, the absence
of 4-cycles, its 19-edge count, and a vertex-cover lower bound of 7. The latter
uses the seven disjoint matching edges
`(0,8), (1,7), (2,13), (3,11), (4,10), (5,12), (6,9)`.
Thus the upstream inequality `edges + cover <= gates + 1` gives 25 gates.

Rebuild from the repository's `lean/` directory with the pinned toolchain and
Mathlib cache already available:

```sh
lake build PEqualNP.Outside.L_meta_2237
export LEAN_PATH="$(pwd)/../results/orch9775/lemmas"
lake env lean --root="$LEAN_PATH" -o "$LEAN_PATH/CircuitHarness.olean" "$LEAN_PATH/CircuitHarness.lean"
lake env lean --root="$LEAN_PATH" -o "$LEAN_PATH/GraphFacts.olean" "$LEAN_PATH/GraphFacts.lean"
lake env lean --root="$LEAN_PATH" -o "$LEAN_PATH/ReadOneFloor.olean" "$LEAN_PATH/ReadOneFloor.lean"
```

All three helper exports and the upstream project build succeeded. The two
specialization exports produced empty stdout and stderr. Complete diagnostics
are archived beside this document; `read-one-validation.json` records hashes.
An additional axiom audit of the lower bound, no-four-cycle fact, and cover
bound found only `propext`, `Classical.choice`, and `Quot.sound`.

These are dependency-test sources: they import other helper modules and the
existing Outside theorem. They are not a standalone one-file submission.
