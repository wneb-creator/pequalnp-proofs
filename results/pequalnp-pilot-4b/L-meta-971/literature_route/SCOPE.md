# L-meta-971: checked local graph-function lemmas

Status: intermediate semantic lemmas only. This file neither proves nor
refutes the posted 27-gate Heawood lower bound.

`CoreLemmas.lean` proves a Boolean identity for extracting a safe OR branch,
adjacency forced by a singleton gate support and a safe singleton context,
and uniqueness of such a context when there are two distinct singleton
supports and the graph has no rectangular four-cycle. A circuit-level
rewiring theorem and the global OR-gate counting argument are not included.
The two structural claims were independently reviewed by `formal_audit`.

The file is standalone and imports only `Mathlib`. Dependencies: Lean
v4.36.0 and Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

`validation.json` records the successful replay check and source hash.
`CoreLemmas.lean.log` is the complete combined stdout/stderr; an empty log
means no diagnostics. This is an ordinary Lean check, not a successful
posted-statement checker verdict.

From `lean/`:

```sh
lake env lean ../results/pequalnp-pilot-4b/L-meta-971/literature_route/CoreLemmas.lean
```
