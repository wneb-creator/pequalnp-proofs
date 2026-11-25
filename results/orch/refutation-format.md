# Refutation format audit

Read on 2026-11-25 UTC. Documentation only: no counterexample to L-meta-4970 has been found. This audit made no checker/workflow changes and no desk calls.

## Local kernel acceptance

The local checker explicitly supports `refute`:

```sh
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_4970.lean original-statement.txt refute
```

The file must declare the module-named final theorem `PEqualNP.Outside.L_meta_4970` proving `¬ (<the entire posted statement>)`, with helpers inside its own namespace and the ordinary plain-file rules. `original-statement.txt` must contain the original positive statement; do not negate it yourself.

Evidence, paths relative to `/workspace/pequalnp-proofs`:

- `tools/check-lean.mjs:81–83` accepts `check`, `refute`, or `reduce`; `:192` passes the selected mode to the verifier.
- `lean/CheckLemma.lean:473` sets the goal to `Not recorded` in refute mode; `:481–489` asks the kernel to check the module-named theorem against that goal; `:498` prints `ACCEPTED (refute)` on success.

## Public submission restriction

Local `ACCEPTED (refute)` does not establish eligibility for the public submission pipeline. `.github/scripts/outside-guard.mjs:159–162` accepts refute mode only when the desk's public row has `kind: "refute"`; absent kind defaults to `check`. `.github/scripts/outside-guard.test.mjs:203–208` explicitly covers both the default and rejection of refute on a check step. `.github/workflows/authoritative.yml:152–158` enforces this agreement before building.

The saved assignment `/tmp/oec/pequalnp-pilot-99/desk-poll-003.json` has no `gap.kind` or `gap.refutation`; its lease terms say `kind: "prove"`. This describes the saved assignment, not a fresh public-row lookup. No documented mechanism was found to convert that existing prove lease, select refute through a PR title/body, or submit a differently prefixed refutation file.

The current https://pequalnp.com/join.txt, read 2026-11-25, documents requesting kind `refute` and proving the separately listed negated twin. `CONTRIBUTING.md:26–28` instead directs a holder who thinks the posted prove statement is false to release with `statement_seems_false` or `hypothesis_too_weak`. A supported public path therefore needs a desk-posted refutation row, or a separately posted ordinary proof statement that is itself the desired negation.

Two implementation caveats: `tools/pnp.sh:125` always writes the returned statement unchanged into its skeleton, so it does not itself add the verifier's negation; `.github/workflows/advisory.yml:116` always invokes `check`, while the authoritative workflow is mode-aware and decisive.

## Owner authorization and preservation

The owner explicitly authorizes Lean-checked refutations and requires compiled results to be preserved and pushed to the pilot's own fork branch. That authorization permits preserving a checked negation; it does not change the public desk-kind guard or make the current prove assignment accept a negation. If a counterexample is found, preserve the exact Lean proof and full local checker output, clearly report the selected `refute` mode, and do not claim that local acceptance establishes public acceptance.
