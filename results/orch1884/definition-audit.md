# L-meta-1884 definition and input-map audit

The exact statement concerns an at-most18-gate AND/OR/NOT circuit evaluated on eleven input wires: ten mapped primary values `x ∘ π`, followed by one free unary value `u (x 0)`. The target is the specified15-edge Petersen function. No counterexample or definition loophole was found in this audit.

## Model details that affect the proof

- `MetaComplexity.FanInTwo` explicitly restricts each gate operation to AND, OR, or NOT and its input-list length to at most two. MOD and majority operations are excluded.
- Backward validity is not required by this class. A nonexistent or forward wire is read as false at evaluation time. Constants, empty gates, unary gates, and repeated references are permitted.
- Empty AND and empty NOT evaluate true; empty OR evaluates false. A NOT gate uses its first input and ignores any second input. These are the library semantics, not additional free operations.
- The actual input-list length is eleven. Gate j therefore produces wire11+j. The free unary input is wire10. A translation using ten as the gate-wire offset would change the statement.
- The output index is arbitrary and also defaults to false when nonexistent. A circuit computing the nonconstant target cannot exploit that default as its whole output.
- The map π is not assumed bijective. The free unary function has four possibilities: constant false, constant true, identity, or negation. Thus dropping primary input0 is potentially harmless when the unary wire retains its information; dropping another primary vertex is not.

## Checked essential-input partial

`lemmas/InputEssentiality.lean` uses the exact target expression and a fixed adjacent neighbor for each of the ten vertices. Its `map_covers_nonzero` proves that any circuit computing the target on every input must have every vertex other than0 in the image of π. It assumes neither FanInTwo nor any gate bound, because the argument concerns only indistinguishable input lists.

For a missing nonzero vertex v, the singleton of its neighbor and the pair consisting of v and that neighbor give identical eleven-wire inputs to the circuit, but the target values are false and true. The file also exports `missing_nonzero_counterexample` in the existential-witness form and `map_surjective_of_zero`, which proves surjectivity once0 is also in the image.

Standalone Lean compilation completed with exit0. Complete output is `/tmp/oec/pequalnp-pilot-103/1884-essentiality-first.stdout` and `.stderr`; stdout contains one unused-simp-argument warning and stderr is empty. Source:64 lines,2641 bytes, SHA256 `c4b010fe68ff746b09f3f7fa40edc9a7b83471e23f7626ef2af1b9d797f145e2`. This is a partial lemma, not the posted size bound or a local-checker verdict.

## Normalization direction

The exact same-size rewiring theorem is already checked in the repository as `L_meta_2594`, and the arbitrary unary input can already be normalized to a supplied negation using `L_meta_2596`, with its stated exceptional-output condition handled by `R_meta_1884_773`. The essentiality partial above is independent of those normalization results; it does not replace the remaining free-negated-input lower bound.

The rewiring mechanism replaces each original raw-input reference i<10 by π(i), while leaving the unary wire10 and all gate/invalid indices at least11 unchanged. The transformed circuit is evaluated on `List.ofFn x ++ [u (x 0)]`. Since both old and new input lists have length eleven, all later wire offsets agree, and this preserves size and allowed operations even when π has repetitions. No duplicate normalization development was undertaken here after the existing theorem was identified.

If π omits0 as well, correct computation requires the unary wire to distinguish false from true. That leaves identity or negation. If π includes0, the checked coverage result makes π surjective, hence bijective on the finite ten-element type. Neither observation makes the difficult eighteen-gate lower bound immediate; no least-circuit or exact target theorem is silently assumed.

## Checked sole-OR structural partials

`lemmas/SoleOrPartner.lean` proves a semantic consequence of a sole OR reader of a nonzero input v. Its hypotheses explicitly require monotonicity of the other operand H on every fiber with x0 fixed, independence of H from v, and factorization of the final target through the OR output and the other coordinates. Under these hypotheses H rejects zero and every singleton. The circuit-to-factorization bridge is not supplied by this file.

`lemmas/PairLocalization.lean` contains that same base and extends it to nonedge pairs. If H accepts such a pair, the unordered pair must be one of exactly six cases: v=1 with {3,9} or {7,8}; v=4 with {2,6} or {7,8}; v=5 with {2,6} or {3,9}. In every case H rejects the assignment obtained by adding vertex0. Kernel-checked finite witness lemmas and the symbolic factorization argument establish these claims. This says nothing about arbitrary circuits that do not satisfy the stated hypotheses and proves no total gate bound.

The standalone extended source compiled successfully with empty output logs `1884-pair-local-third.stdout` and `.stderr` in the job scratch directory. It has192 lines,7990bytes and SHA256 `7c2b16f0f72f9a6aff93389bf20c612631c0967290cc5ba6c597637620310280`. Independent review is recorded in `REVIEW-pair-localization.md`.

`lemmas/LiveDirectional.lean` proves that a false-to-true change of the target of `Extended.Live false` must be present in an initial live root. It also packages the consequence when exactly one permitted root can increase. The false mode is essential: the result is not asserted for signed binary operations. This small scratch-import helper compiled successfully with empty `1884-directional-first` logs and is reviewed separately. Final integration must inline its required Binary17 base; importing a prior Outside proof is not a submission format.
