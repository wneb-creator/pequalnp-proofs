# Declaration dependency collector

This is optional development tooling. Do not inline these files into a proof
submission: they use Lean elaborator commands and print diagnostic strings.

`DependencyCollector.lean` exports the command

```lean
collect_own_dependencies PEqualNP.Outside.L_meta_9775 within PEqualNP.Outside.L_meta_9775
```

Create a separate driver that imports the compiled final proof module and
`DependencyCollector`, then invokes that command. Export the collector first
with `lake env lean --root=<tooling-directory> -o <tooling-directory>/DependencyCollector.olean <tooling-directory>/DependencyCollector.lean`.
Add that directory to `LEAN_PATH` when checking the driver. Save the complete
driver stdout and stderr. Lines beginning `OWN` followed by a tab are reachable
constant names.

The collector inspects both constant types and values, including opaque
theorem proof values. It also records inductive constructors and recursors.
It follows names under the supplied namespace prefix, plus declarations in
the same modules as reached owned declarations, retaining private auxiliaries.
For a fully inlined proof module this includes all of its reachable constants.

This is evidence for pruning, not a source-to-source transformation or a proof
check. Preserve namespace structure, instances, attributes, and other commands
needed by elaboration; a tactic may rely on declarations that disappear from
its final kernel proof term. Recompile every pruned candidate and rerun the
repository checker before using it.

The smoke test verifies a chain of type/value dependencies and checks that an
unreferenced declaration is omitted. It also successfully traversed the real
`relabel_Bplus` proof, finding 74 owned constants. Validation streams and hashes
are preserved in this directory.
