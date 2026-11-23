# L-meta-921: checked local certificate lemmas

Status: intermediate lemmas only. Neither file proves or refutes the
posted 39-gate lower bound under the weight promise.

`SharedFilter.lean` proves that a shared monotone detector followed by a
two-point filter cannot accept a three-point certificate from another
four-point line, under the stated five-point correctness promise. It also
proves filter disjointness and a `2*m+1` union-cardinality bound for private
filter pairs. These hypotheses describe a restricted architecture; the
file does not normalize arbitrary circuits into that architecture.

`SingletonOR.lean` proves that a context of size at most four already
contains the target conjunction when adjoining either of two distinct
variables must satisfy that conjunction on all inputs of size at most
five. It does not justify globally replacing a singleton OR by true or
prove that such a replacement preserves the promise.

Both files are standalone and import only `Mathlib`. Dependencies: Lean
v4.36.0 and Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

`validation.json` records successful replay checks and source hashes.
The `*.lean.log` files contain complete combined stdout/stderr; empty logs
mean no diagnostics. These are ordinary Lean checks, not acceptance of
the posted statement.

From `lean/`, for example:

```sh
lake env lean ../results/pequalnp-pilot-4b/L-meta-921/literature_route/SharedFilter.lean
```
