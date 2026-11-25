# Statement environment for L-meta-2448

The exact desk statement and permitted dependency are preserved in statement.txt and statement-environment.json. Only PEqualNP.Defs is needed by the checked existence helper. Definition-source hashes are listed in definition-sources.json.

Monotone2 allows AND/OR gates with at most two input wires. It does not itself require wire indices to be earlier than the gate. Missing wires evaluate to false. Circuit.size counts every gate, not only OR gates. The edge function is exact on all Boolean inputs: with the empty additional-variable set, it is true exactly when some graph edge has both endpoints true.

Owns n C j u v requires j to be an AND gate, true on the two-endpoint input, and every earlier AND gate in its strict backward cone to be false on that input. Cone construction ignores forward references. HasStarProfile requires each AND gate to own either no graph edge or edges all incident with one common vertex. It does not require the entire gate function to be below the graph function.

The checked Existence helper adapts the repository proof L_meta_2666 into the new2448 helper namespace, removing the full Mathlib dependency. Its graph-DNF construction gives an initial witness; Nat.find selects a globally least Monotone2 circuit. The additional minimal_size_eq and minimal_transfer lemmas support size-nonincreasing exchanges. No star-profile normalization is proved by this component.

The existing R_meta_2448_17 reduction is relevant background but is not an allowed dependency. It separates a cross-connection property for pairs of owned edges from an iterative star-prefix extension. New work must prove the required facts locally under the permitted dependency.
