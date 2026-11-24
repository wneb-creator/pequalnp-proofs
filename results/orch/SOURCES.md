# Sources and attribution

The full baseline in lean/PEqualNP/Outside/L_meta_3679.lean is the proof by pmatos from https://github.com/open-goat/pequalnp-proofs/pull/7597, commit e9cda5db21dc52789a13ef56b978b57d7ef5897a. It was fetched and independently built locally. It is preserved here with attribution while adapting custom helper types and an instance to the repository plain-file rules. No originality claim is made for that baseline.

Our independently developed partial lemmas and 39-vertex Tarjan witness are preserved under results/orch/lemmas. The team discovered the same Tarjan reduction before locating the existing PR.

Final adaptation: all six custom helper types became built-in encodings; the global adjacency instance was removed; only PEqualNP.Defs is imported. Exact posted negation and final checker passed.
