# Gate elimination route

Explored independently for L-meta-10760 on 2026-11-25.

## Reusable formal lemmas

`lean/PEqualNP/Outside/L_meta_927.lean` has a self-contained simplification/relabeling/gate elimination framework in lines 1–1124. Relevant final lemmas:

- `one_gate_at` (1041): for an essential variable p and nonconstant restriction f[p:=b], a circuit of size s yields a circuit for the restriction of size at most s-1.
- `gate_elim_at` (1083): if both restrictions are nonconstant, one of the two has a circuit at most s-2.
- `dep_lower_set` (170): dependence on k variables needs at least k-1 gates.

These lemmas cover unrestricted AND/OR/NOT circuits, so they are sound lower-bound tools for this task. They cannot be imported directly; helpers must be copied under the target namespace.

## Computed strength and limit

A dynamic program applying dependency bound, fixed-value elimination, and two-gate branching to every partial assignment found a lower bound of only 8 (344 restriction states).

Exact biclique-cover formula DP gives the following upper bounds on the seven zero restrictions:

| removed input | monotone upper bound |
|---|---:|
| 0 | 10 |
| 1 | 10 |
| 2 | 10 |
| 3 | 10 |
| 4 | 10 |
| 5 | 10 |
| 6 | 9 |

Consequently, even exact six-variable base lower bounds cannot make a simple one-gate elimination reach beyond 11. The two-gate branch is still weaker because f[p:=1] has many singleton minterms. This route alone cannot establish the current 14-gate upper bound.

## Structural observation about the single NOT

The complement graph has no triangle. Its nine edges (the target graph nonedges) are:

[(0, 1), (0, 3), (1, 2), (1, 6), (2, 3), (2, 5), (3, 4), (4, 5), (4, 6)]

Hence the graph has independence number 2. Its edge function is true on every assignment with at least three true bits and false on exactly 17 inputs (empty, 7 singleton inputs, and 9 nonedge pairs).

Let u be the monotone function entering the only NOT. If u ≤ f pointwise, replacing that NOT by a constant-true AND gate yields a same-length monotone circuit computing f. Indeed, where u=false the replacement does not change the NOT output; where u=true the original output already equals true, and the monotone suffix can only increase when the NOT output rises from false to true.

Thus any genuinely essential NOT for this f has u=true on an independent set of size at most 2. This reduces the hard structural cases to singleton or nonedge-pair witnesses, but I do not yet have a complete size-preserving simplification for those cases. Do not assume a general one-NOT elimination theorem.

Scratch DP: `/tmp/oec/pequalnp-pilot-178/gate_elimination/basic.py`.

## Independent review of the 13-gate lower-bound candidate

Reviewed `/tmp/oec/pequalnp-pilot-178/certificate_search/Lower13.lean`, 3787 lines, 223078 bytes, SHA256 `139aa8ff86fa6f697837a4a6e8832ba5203acbb98efaa15cec5b56cd10130900`.

Verdict: no semantic loophole found; acceptable as a partial lower bound conditional on its Lean/kernel checks succeeding. No build was started by this reviewer.

- Independently diffed it against accepted `L_meta_10762.lean`. The generic proof engine and circuit bridge are unchanged. Changes consist of namespace, generated constants, certificate bound layers, explicit names for two noncomputable sections, target graph expressions, and the final lower13 helper.
- Independently decoded all large decimal limb expressions. They match the data JSON exactly.
- Independently checked all 820 used row bits against the exact target edge function. Every target bit agrees.
- Verified all 42 X and 17 Y segments have constant source assignments, valid zero boundary bits, and the correct HX/HY carry markers.
- The `f` and `EF` expressions use exactly edges 02,13,04,14,24,05,15,35,06,26,36,56.
- The bridge quantifies over the real project Circuit and FanInTwo definitions and maps actual circuit evaluation to the sample model. The conclusion is 13 ≤ D.size with only fan-in-two legality and target-computation hypotheses.
- No `_root_`, quotes, `sorry`, `native_decide`, axiom/unsafe declarations, prohibited commands, attributes, or decimal numeral longer than 20 digits found.
- The final posted replacement theorem is absent. This file is a partial lower-bound component, not a complete proof of the leased statement.

The prior suspected delete0 bound11 was indeed invalid: a concrete monotone10gate restriction witness is `(x3∨x5)(x1∨x6) ∨ x1x4 ∨ x2(x4∨x6) ∨ x3x5`. Sent its explicit gate list to certificate_search to diagnose the Python port. Current Lower13 bound layer uses10 for that restriction.
