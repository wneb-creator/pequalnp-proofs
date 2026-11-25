# Reduction strategy for L-meta-2592

Started 2026-11-25 around 13:49 UTC. Only root holds and renews the lease.

## Existing cuts

All three allowed reduction slots are already occupied in current main:

- `R_meta_2592_408`: normalize missing wire reads, NOT operand lists and output placement; then prove the bounded lower bound for the normalized circuit. It permits a strict size decrease when normalization erases all NOTs.
- `R_meta_2592_318`: split a circuit at its last NOT, obtaining an arbitrary fan-in-two prefix and monotone suffix; then prove a separator theorem with combined prefix/suffix budget 18.
- `R_meta_2592_271`: prove at least 15 non-NOT gates are necessary; then handle NOT counts 1 through 4.

A fourth reduction should not be submitted while `reductions_live=3` remains the desk state.

## Structural component prepared

`/tmp/oec/pequalnp-pilot-99/reduction_strategy/CutLast.lean` contains a compact candidate proof of the complete first hypothesis of `R_meta_2592_318`.

Split the gate list into `pre ++ g :: post`, with `g` a NOT and no NOT in `post`. Set prefix output to the first input of `g`, using the missing index `n + pre.length` when `g.inputs` is empty. This index reads false exactly as empty-input NOT requires. Keep the original output index for the suffix. List append evaluation then gives the exact factorization.

The source has three helpers, all in `PEqualNP.Outside.L_meta_2592_aux`: last-NOT split, wire-list length, and factorization. It uses only `PEqualNP.Defs`. It now compiles with official Lean 4.36.0 and the pinned cache, via `lake env lean`; both logs `cutlast.stdout` and `cutlast.stderr` are empty. No unproved placeholder occurs. Root was alerted immediately for independent review and early push.

## Additional compiled boundary lemmas

`/tmp/oec/pequalnp-pilot-99/reduction_strategy/MonoPrefix.lean` also compiles. It proves pointwise monotonicity of all wires of a monotone circuit, then:

- A monotone prefix followed by output NOT cannot compute any function false at the all-false input and true at the all-true input.
- If a final AND reads a complemented monotone-prefix output and the circuit is true at all-true, that prefix output must be constantly false. The final AND therefore equals its other input.
- If a final OR reads a complemented monotone-prefix output and the circuit is false at all-false, that prefix output must be constantly true. The final OR therefore equals its other input.

These boundary lemmas do not need a constant-free circuit or valid-wire assumptions. Empty inputs and missing reads are included. Logs `monoprefix.stdout` and `monoprefix.stderr` are empty. Root was alerted immediately.

## Other useful existing sources

- `L_meta_2826`: roughly 200 lines; normalizes arbitrary 10-input circuits to binary circuits, with `binary.size + notCount C ≤ C.size`.
- `L_meta_3400`: Petersen graph with one vertex deleted, on 9 inputs; proves at least 13 non-NOT gates.
- `L_meta_3402` and `L_meta_3404`: strengthen a related 9-input case to 14 gates when supplied particular free OR inputs, respectively for zero NOTs and one or two NOTs.
- `L_meta_5367`: its internal `Main1672.finalBound` proves the 9-input graph needs at least 15 total gates. Its main result gives `15 + count(effective readers of x0 or its supplied complement) ≤ size` for circuits supplied with a free complement of input zero.

No full lower bound or counterexample established by this strategy yet.
