# L-meta-2732 lower-bound strategy

Started 2026-11-25 around 05:28 UTC. Root owns the lease and submission.

## Established repository facts

- The standard star circuit has 27 gates; this is only an upper bound for unrestricted circuits.
- `lean/PEqualNP/Outside/L_meta_1983.lean:842`, `pairCleanBound`, proves that a circuit for a C4-free graph with every AND gate rejecting every false input of weight at most two has size at least `edge_count + vertex_cover_number - 1`.
- For Heawood, the edge count is 21 and vertex-cover number 7. The same file proves the 27-gate bound for circuits with no nested AND gates. Consequently a 26-gate circuit needs a nested AND and an AND accepting a false input of weight at most two.
- Existing unrestricted bounds in `L_meta_1483.lean` and `L_meta_5670.lean` give 20 gates, not 27.
- All three live reductions for this gap already exist: `R_meta_2732_3`, `_427`, `_773`. The first contains 58 extremal input rows and 65 canonical first-two-gate patterns.

## New checked partial

`DirtyFilter.lean` (59 lines) compiled on 2026-11-25 around 05:34 UTC using `lake env lean`, exit 0 and empty diagnostic output. The complete log is `/tmp/oec/pequalnp-pilot-70/lower-bound/dirty-filter-lean.log`.

Its main lemma `safeFilter_doubleStar` says: for a rectangle-free bipartite relation, if a union of selected rows and selected columns inside A×B consists only of edges, and both A and B have at least two vertices, the selected pairs lie in one row together with one column. Supporting lemmas prove uniqueness of selected rows and columns. This is a generic combinatorial building block, not a proof of the assigned gap or a circuit lower bound. Independent review by `sat_review` passed.

## Open obstruction

Conjectural route: a circuit with only one pair-dirty AND can be converted without increasing size to a pair-clean circuit; this would force at least two pair-dirty ANDs in any 26-gate witness. Filtering a raw dirty rectangle is controlled by the new double-star lemma. Two unresolved issues are previously computed clean-edge contributions inside its operands and gate accounting when the dirty gate feeds several later filters. No claim that the normalization theorem is true has been established.

## Auxiliary finite search prepared

`/tmp/oec/pequalnp-pilot-70/lower-bound/pairdirty_synthesize.py` extends the reviewed synthesis encoding with 85 additional negative rows: zero, 14 singletons, and 70 nonedge pairs. Each gate has a flag equivalent to being an AND that accepts one of these rows, and at most one flag may hold.

The 26-gate instance has 143 distinct rows, 14,063 variables and 451,723 clauses. Exact files: `pairdirty1-26.cnf`, `pairdirty1-26.map.json`; complete generation log `pairdirty1-generate.log`. Root requested preparation only until a CPU slot is free. An UNSAT result would address only this restricted search and would still need a Lean certificate bridge.

## Research caveat

Read 2026-11-25: Stasys Jukna, *Disproving the single level conjecture*, https://eccc.weizmann.ac.il/report/2005/021/ . It shows that assuming all quadratic functions have comparably small single-level circuits is invalid in general. No same-size normalization for the bipartite C4-free Heawood case was found. Such a normalization remains UNVERIFIED here. The ECCC PDF text extraction was corrupted; only the readable landing-page abstract and repository proofs support the statements above.
