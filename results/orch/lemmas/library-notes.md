# Library inspection and last-NOT component

2026-11-25 13:46–13:50 UTC, status_1035 agent.

- L-meta-1035: all-state GitHub search returned no results. Full open-PR census was 777 PRs across eight pages, final `hasNextPage=false`, none with 1035 in title/head. Root obtained definitive desk `not_open` response.
- L-meta-2592 has three checked reductions already: `R_meta_2592_318` (factor last NOT and separate the resulting monotone suffix), `_408` (normalize invalid reads and unused gates, then lower bound), `_271` (at least 15 binary gates, then exclude 1–4 NOT gates). New reduction submission is blocked by the stated three-reduction ceiling unless intake explicitly changes that status.
- Sibling L-meta-2590 has reductions `_1`, `_491`, `_932`, but no proof file found. The last is a long semantic trace normal-form reduction; useful normalization techniques but no closed lower bound.
- `PEqualNP.Defs` and its definition modules have no theorem/lemma declarations found. The only allowed project module therefore supplies definitions, not a ready Petersen lower bound. Proof modules outside the root cannot be used as imports for this gap.
- `LastNotFactor.lean` develops the generic factorization hypothesis of `_318`: split at the last NOT, choose the prefix output as the NOT's first input (fallback to a missing wire for empty inputs), retain the monotone suffix and original output. The construction explicitly respects forward/missing reads and empty NOT inputs.

This is a partial component, not a proof of L-meta-2592.

Reusable checked lower-bound machinery located later:

- `lean/PEqualNP/Outside/L_meta_5971.lean` (2847 lines): for the 9-input, 12-edge Petersen vertex deletion, at least 13 non-NOT gates. Generic U2 translation and restriction DP occupy most of the proof. `petEdges` starts at line 1836, `dp_sound` at 2658.
- `lean/PEqualNP/Outside/L_meta_8033.lean` (7136 lines): same graph needs at least 15 total gates and at least 13 binary gates plus every NOT. Combines truth-table certificates with a first-branch grouping argument. `least_petersen_five_branches` is at 7041, `petersen_binary_lower` at 7087.
- `lean/PEqualNP/Outside/L_meta_9818.lean` (7810 lines): a 10-input 13-edge Petersen subgraph needs at least 17 gates, by reducing to a 9-input certificate.
- These are not allowed project imports for the leased gap. Any reused proofs must be copied into the one submission file and obey its plain-file restrictions.

2026-11-25 13:51 UTC: proof_strategy independently reviewed `LastNotFactor.lean`; mathematical semantics and forbidden-feature check passed. Empty NOT inputs, invalid/forward reads, output in the prefix, suffix numbering, and size all accounted for. Compilation still pending cache availability.

Correction after broader exact-form search: `L_meta_8295.lean` already proves this same generic last-NOT factorization. `LastNotFactor.lean` is an independently re-derived helper, not a novel accepted result or a new solution of a desk step.

Compilation succeeded after adding the final definitional equality step and removing one redundant simp argument: `lake env lean ../results/orch/lemmas/LastNotFactor.lean` exited 0 with no output. Full stdout/stderr: `/tmp/oec/pequalnp-pilot-96/lastnot-build-2.log`. Root notified immediately for reviewed preservation.

Further exact component found by proof_strategy: `L_meta_4725.lean` already proves `15 + notCount C ≤ C.size` for the full Petersen function; `L_meta_6194.lean` supplies the equivalent 15 non-NOT bound. Reduction `_271` therefore only leaves the one-to-four-NOT exclusion.

`DeadNotPad.lean` is now checked locally: prepend an unused `NOT []` gate, increment all original internal wire references and the output by one, and preserve the original Boolean function and fan-in constraints. The circuit gains exactly one gate and has a NOT; an originally final output remains final when the original circuit has positive size. This supplies the padding step needed when truncation discards every original NOT. The proof covers missing and forward references by relating accumulators `xs ++ ys` and `xs ++ true :: ys`. Namespace: `PEqualNP.Outside.L_meta_2592_aux.Pad`.

`lake env lean ../results/orch/lemmas/DeadNotPad.lean` exited 0 with no output; full stdout/stderr `/tmp/oec/pequalnp-pilot-96/deadnot-build-2.log`. proof_strategy independently reviewed the mathematics and forbidden features before root was notified for preservation.

Independent review delivered for proof_strategy's `NormalizeForSat.lean` and `TruncateForSat.lean`: mathematical semantics passed. The normalizer preserves existence of a NOT, but not exact NOT count because a zero-input AND becomes NOT of the free-false input. The normalizer's legal-index bound correctly counts the extra free-false input. Truncation is sound even for original forward reads because sequential gates never retroactively change earlier reads. Recommended composition: truncate at the original output, pad a dead NOT if all NOTs were lost, then canonicalize to the extra-false-input model.

`EraseFreeFalse.lean` now supplies the inverse semantic bridge, with no canonical-gate assumptions. On a circuit with `n + 1` inputs whose last input is fixed false, keep indices below `n`, map index `n` to `n + C.size` (permanently missing), and shift every higher index down one. The transformed circuit on `n` inputs has exactly the same gate count, operation list, NOT count, fan-in property, and output function. A positive-size final output remains final. The proof handles arbitrary gate operations and invalid or forward reads through a paired accumulator invariant; the sentinel remains missing through the final evaluation as well as every gate.

`lake env lean ../results/orch/lemmas/EraseFreeFalse.lean` exited 0 with empty stdout/stderr in `/tmp/oec/pequalnp-pilot-96/erase-false-build-2.log`. few_not independently reviewed the mathematical and format details: PASS. A deterministic Python sanity run checked 6804 cases across 0–5 inputs, 0–8 gates, empty/extra operands, and input/forward/missing reads and outputs: all passed; complete output is `/tmp/oec/pequalnp-pilot-96/erase-false-sanity.log`. Root was notified immediately for preservation. This bridge lets the existing binary-gate lower bound apply to the canonical free-false model without losing NOT-count information.
