# L-meta-4675 research checkpoint

The posted theorem is **not proved or refuted**. The named Lean file compiles as a collection of helper lemmas, but does not declare `PEqualNP.Outside.L_meta_4675`. The exact checker therefore rejects it with `no-theorem`. Do not submit these partials as a proof PR.

Work branch: `pnp/pilot-163` on `wneb-creator/pequalnp-proofs`. Upstream base: `72f7a118`. Lean/toolchain and Mathlib remain pinned by the repository. Only `PEqualNP.Defs` is an allowed project import. `statement.txt` is the exact assigned statement; `allowed-imports.json` records its imports. Root lease acquired 2026-11-25 17:06:33 UTC; lease handling remains solely with the root pilot.

## What is checked

- Exact graph/cardinality bridge for the bipartite edge function, and the desired conclusion under the extra pair-clean-AND hypothesis.
- A same-function, no-larger AO2/T0 circuit that is least among AO2/T0 circuits and has TopForm. Every gate is pivotal on some edge input; there are no unused gates and the output is last.
- Top-level OR/AND balance under that constrained minimum. Existing residual accounting is adapted without substituting unrestricted minimum.
- Original and stronger large-lambda residual accounting, followed by conditional bridges to the exact posted conclusion. The extra residual certificate is explicit.
- Singleton-mixed OR gates lie outside lambda and are in the paid OR budget. This means accepting singleton inputs of both colours, not arbitrary dependence on both colours.
- A private pair of identity buffers feeding an OR can be merged when their raw supports have one colour; a minimum cannot contain this pattern.
- Cofactoring an input to false inside a region whose entire outside boundary is OR-masked by that same input preserves semantics and T0. A direct internal read then yields strict size reduction.
- Bank-support, matching, anchored-box, centre-hit and raw OR-DAG cut-count tools, with their respective hypotheses explicit.

`assemble.py` reproducibly assembles the named file from frozen standalone sources in `lemmas/`. It removes duplicated prefixes. A seven-lemma axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining mathematical obstacle

Let U be Ustar, c the centreless clean AND count, j the junk AND count, and o the OR count outside largeLam. The conditional route needs a cover S of U with |U|+|S| <= 2c+j+o. Normalization and the accounting around this certificate are checked. The certificate is not proved. A successful argument must charge shared dirty computations globally; local gate necessity and boundary counts alone are insufficient.

Do not use these false shortcuts:

- T0 is syntactic OR reach. AND buffers can hide semantic mixing.
- The separate residual cover claim tau(U)<=c+j fails for a verified 8-gate double-star circuit. The combined bound holds there at equality five.
- Independent per-centre raw-bank factoring fails for a 13-gate circuit even with TopForm, contextual gate necessity and OR-branch necessity. The explicit regression is Lean-checked and also proves a 7-gate equivalent, so it is not a minimum and does not refute the gap.
- Last-dirty-gate reader complexity is not bounded by a constant without paying upstream construction.

## Validation and search evidence

`validation.txt`, `TIMELINE.md`, `NOTES.md`, complete build/checker outputs and standalone sources are preserved in this branch. `lemmas/counterexample-manifest.md` distinguishes completed finite exhaustive scopes, heuristic failures, discarded encodings, positive controls and UNKNOWN timeouts; its JSON hashes every archived input/source/log. These searches are not Lean proofs of the general statement.

To rebuild from a prepared checkout, run `lake exe cache get` once in `lean/`, then `lake build PEqualNP.Outside.L_meta_4675`. Never run `lake update`. The exact checker command from repository root is `node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_4675.lean results/orch/statement.txt check`; it is expected to reject until the exact theorem is supplied.

If completing a submission, the PR must add only the named Lean file. Keep these research archives on the fork branch/history; do not include them in a proof PR diff. No reduction submission is authorized for the acquired lease.
