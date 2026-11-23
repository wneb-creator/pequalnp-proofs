# L-meta-952: cofactor-substitution obstruction

Status: a checked counterexample to an intermediate substitution strategy,
not a refutation of the posted circuit-size lower bound.

`CofactorObstruction.lean` defines a small Boolean expression that returns
`x` when its auxiliary input is `NOT a`. Neither constant substitution
works for all inputs. For two such outputs, no common replacement that is
monotone in `a` preserves both outputs. The example is redundant and makes
no assertion about the minimum size of an equivalent monotone circuit.

The file is standalone and imports only `Mathlib`. Dependencies: Lean
v4.36.0 and Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

`validation.json` records the successful replay check and source hash.
`CofactorObstruction.lean.log` contains complete combined stdout/stderr;
an empty log means no diagnostics. This is an ordinary Lean check, not a
successful posted-statement checker verdict.

From `lean/`:

```sh
lake env lean ../results/pequalnp-pilot-4b/L-meta-952/literature_route/CofactorObstruction.lean
```
