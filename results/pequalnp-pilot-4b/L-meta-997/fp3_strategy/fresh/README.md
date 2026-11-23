# L-meta-997: checked special case |y| <= 2

This artifact proves only the special case `y.card <= 2`. It does not prove the full L-meta-997 statement.

The checked theorem is `PEqualNP.Outside.L_meta_997.Small.small_one_not` in `SmallWindow.lean`. Under pairwise line intersection at most one, fan-in at most two, all NOT gates restricted to index `t`, exact OR outputs, and falsity of wire `n+t` at `y`, it proves:

```lean
(∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card)
  ≤ C.gates.length + m
```

The theorem also requires `y.card <= 2`. Within this scope its conclusion is stronger than the requested bound: no refund term is needed. The low-weight truth premise is unnecessary. Empty `y`, absence of a NOT gate, and an unavailable `t` are handled by the proof.

## Contents and dependencies

- `SmallWindow.lean`: the complete checked source. The heavy-ownership machinery from `lean/PEqualNP/Outside/L_meta_988.lean` is inlined and renamed into `PEqualNP.Outside.L_meta_997.SmallBase`. Root's checked NOT-freezing bridge is also inlined in the `Window` namespace. No scratch-module import is required.
- `SmallWindow.log`: the complete successful compile output, including the final axiom audit.
- `manifest.json`: scope, validation provenance, and SHA-256 hashes.

The only imports are `Mathlib` and `PEqualNP.Defs`; use the repository's Lean/Mathlib environment. The final axiom audit for both `small_of_monotone_window` and `small_one_not` reports only `[propext, Classical.choice, Quot.sound]`. No `sorry`, new axiom, or `native_decide` was introduced.

## Validation

Compilation exited zero. The preserved source and log are byte-identical to the successful scratch run. The command was:

```sh
/tmp/oec/pequalnp-pilot-4b/with-lean.sh lake env lean /tmp/oec/pequalnp-pilot-4b/fp3_strategy/meta997/fresh/SmallWindow.lean
```

Working directory: `/workspace/pequalnp-proofs/lean`.

To check the preserved source in the configured repository environment, run from `lean/`:

```sh
lake env lean ../results/pequalnp-pilot-4b/L-meta-997/fp3_strategy/fresh/SmallWindow.lean
```

Only this result directory was written during preservation. Nothing was staged, committed, or pushed by this subagent.
