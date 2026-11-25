# Case bounds strategy

- Upstream `L_meta_6194.lean` already contains a checked proof that any fan-in-two circuit computing the Petersen edge function has at least 15 non-NOT gates. Its public theorem exposes this fact. The helper proof uses circuit simplification, an essential-input count, six necessary branch wires, and a finite graph calculation.
- Only `PEqualNP.Defs` is allowed for the assigned gap, so importing `L_meta_6194` is unavailable. `lemmas/CaseBounds.lean` includes the relevant proof under `PEqualNP.Outside.L_meta_2592_aux.CaseBounds`, then derives that any circuit of size at most 19 has at most four NOT gates. The posted premise that a NOT occurs then bounds its NOT count between one and four.
- This is a partial result only. It does not exclude the one-, two-, three-, or four-NOT cases and does not establish L-meta-2592.
- Compilation is pending the toolchain/cache setup and definitions-root build as of initial preparation.
- An initial weighted essential-support proof (nine non-NOT gates) was superseded before compilation. Its draft is retained only in scratch as `CaseBounds-weighted-support.lean`; it is weaker than the available 15-gate bound.

The mathematically hard remaining question is whether a Petersen circuit with 15–18 non-NOT gates and one to four NOT gates can exist within the 19-gate budget. The support and branch lower bound alone cannot resolve those cases.

## New read-once counting lemma

`clean_petersen_input_read_exactly_once` establishes the planned read-once foothold for a cleaned circuit: if its output is a gate, every nonoutput wire is read, it has at most 19 gates, and at least one gate is a NOT, then some input occurs exactly once among all gate operands.

The count uses normalized arities: every AND/OR reads exactly two operands and every NOT reads exactly one. If every one of the ten inputs occurred twice, these would consume at least 20 slots. The circuit's nonoutput gate wires consume at least `size - 1` more slots. Its total slot count is `2 * size - notCount`; with `size <= 19` and `notCount >= 1`, these inequalities contradict one another. Essential/live inputs ensure the resulting at-most-once input occurs at least once.

This lemma counts operand occurrences directly, so it does not assume that different occurrences belong to different reader gates. It depends on the existing `CleanL` arity convention and a live-wire hypothesis, which must be supplied by a normalization/minimality step before applying it to an arbitrary posted circuit.
