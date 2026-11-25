# Portable partial checkpoint for L-meta-2448

This file is a checked collection of helper results. The posted theorem requiring a globally minimum circuit with a star ownership profile remains unproved. It is not a completed proof or a refutation.

The 2234-line file depends only on `PEqualNP.Defs`. It contains the previous 1114-line checkpoint followed by seven independently checked components: reader deletion, four-gate repair construction, true-AND count monotonicity, conditional graph repair, forced-false cofactor properties, concrete pure-product graph repair, and the repair count comparison. Composition removes only dependency lines from the appended components. All other source bodies are unchanged; exact input hashes appear in `candidate-manifest.json`.

The combined Lean run passed, and a separate cached probe audited every one of its 172 declarations, including definitions. Their only axioms are the standard `propext`, `Classical.choice`, and `Quot.sound`. Full output and resource statistics are retained in the logs. The probe contains validation commands and is not part of the candidate proof file.

The repair results retain their explicit pure-input, center, prefix, and counting hypotheses. They do not establish the general normalization step. The official checker was not run on this scratch module; the root agent owns the named target and its checks.
