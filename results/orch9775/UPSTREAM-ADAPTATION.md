# L-meta-9774 adaptation status

The upstream result at revision `790ef40780fc680c09cde228f2229fe058bd6e08`
proves that its particular 14-input graph has no monotone circuit with at most
24 gates. Its graph replaces our edge `(1,9)` with `(2,12)`.

These graphs are not isomorphic. In the upstream graph the degree-two vertices
are `{0,1,7,9}` and induce the edge `(1,7)`. In our graph they are
`{0,2,7,12}` and induce no edges. A relabeling therefore cannot transfer the
completed lower bound directly.

The upstream proof has three main parts:

1. General normalization to a strict, live binary DAG, followed by semantic
   support and wire-sharing inequalities.
2. Graph-specific private-witness inequalities and exhaustive finite
   classification of possible sets of inputs that do not occur at branching
   wires.
3. Further support restrictions and finite resolution certificates excluding
   the remaining configurations.

The first part is now independently recompiled in `UpstreamDagTools.lean`.
It is upstream lines 1–3468, with only the outer namespace renamed and closed.
It includes the stricter normalization that removes repeated operands and
dead gates and makes the last gate the output; the earlier IsAO2 helper did
not itself state those additional properties.

`UpstreamGraph.lean` adapts upstream lines 3470–3776 to our graph. Its finite
adjacency check, exact circuit normalization, private-witness charging rules,
one- and two-merge bounds, support occurrence rules, and projected-support
counting theorem all compile. The two full bipartition cases also compile after
replacing their neighborhood masks and corresponding vertex witnesses. The
module includes the unchanged generic compact-weight API from upstream lines
3933 and 4055–4089, but excludes the upstream graph's weight tables and masks.

Both exports completed with exit 0 and empty stdout and stderr. Full logs and
source hashes are recorded in `upstream-framework-validation.json`. This is a
checked reusable framework, not yet a proof or refutation of L-meta-9775. The
remaining private-witness tables and final finite exclusions must be generated
and checked for our graph.

Rebuild `UpstreamDagTools.lean` before `UpstreamGraph.lean`, setting `LEAN_PATH`
to this directory's `lemmas/` folder and using that folder as Lean's `--root`.
Only the first module imports `PEqualNP.Defs`; the second imports the first.
Final single-file assembly can inline both bodies and retain only the Defs
import.
