# Matching-clause counting support

`MatchingCNF.lean` proves that fewer than `2^n` positive clauses, each containing at least one endpoint from every one of `n` disjoint pairs, admit a satisfying assignment choosing one endpoint per pair. The formal statement uses a Boolean clause-membership function and explicit pair-cover hypotheses.

The source imports only `PEqualNP.Defs`. Its checked theorem uses only `propext`, `Classical.choice`, and `Quot.sound`; the complete build output and independent source review are included. Reproduce from the repository `lean/` directory with the pinned toolchain using `lake env lean /path/to/MatchingCNF.lean`.

This is a generic counting lemma. It supplies no circuit or TopForm normalization and does not prove the full gap L-meta-2373. The root job measurements are in `../packed-replay/validation.txt`.
