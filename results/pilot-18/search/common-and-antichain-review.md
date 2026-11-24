# Common outer-AND support antichain: mathematical PASS, not implemented

This review is optional preparation only. Neither ready reverse-counter
variant, any existing CNF, nor any worker is changed.

Let W be a clean-prefix leaf which is a factor of the outermost AND, and let
S be its singleton support. Exact output F implies W accepts every positive
input. On an independent input, every prefix AND is false, so the prefix
reduces to OR propagation of its supported input vertices. If S is proper,
W is also false at the empty input, by monotonicity and a missing singleton.
Consequently W equals `F OR OR(S)` on every input. This conclusion requires
both the clean-prefix invariant and the leaf's outer-AND position.

For two proper supports S contained in T, `W_S <= W_T`. Replacing only the
tail occurrence of W_T by free TRUE therefore preserves the full function
of the AND factorization. It need not replace other uses of the same prefix
wire. Equal supports are handled by retaining one representative. Retaining
one representative of each inclusion-minimal proper support leaves pairwise
incomparable proper factors. Full-support factors are exempt: their empty
value can distinguish TRUE from OR of all inputs, and no strengthening for
them is required by this cut.

## Exact scope and ports

The actual source templates and metadata give these common factors:

| Template | Common leaves | Gate/operand ports |
| --- | --- | --- |
| meet5 | A, B, C, D, E | 17-left, 17-right, 18-left, 19-left, 20-left |
| meet3or2 | A, B, C | 17-left, 17-right, 19-left |
| meet2or1meet2 | A, B | 19-left, 19-right |
| meet1or1meet3 | A only | 20-left |
| meet1or2meet2 | A only | 20-left |
| or1meet4, or2meet3 | none | no cut |

Use `tail_leaf_selectors` for these ports and the full eleven-bit support of
the selected prefix wire. Do not apply this to every `tail_ordered_groups`
entry: several such groups lie below an OR, where the factors need not cover
F and the argument fails. Full-support detection must examine all eleven
bits, including full-support copy wires; testing only selection of input 12
would not implement the stated exemption.

## Compatibility with earlier normalization

Only selected tail occurrences change to TRUE. The suffix template retains
its four gates and read-once structure. Its existing commutative common-factor
group can be reordered to restore the ordered-leaf convention. Prune newly
dead prefix computations and restore the final copy chain by the previously
reviewed construction. Copies preserve supports and covered edges, so they
do not introduce a new comparable pair of proper common factors.

If the earlier prefix normalizations need reapplying, their support-preserving
productive/dominance steps and boundary-preserving absorption steps leave
each surviving proper common factor's support and all accepted target edges
unchanged. It remains `F OR OR(S)`. Alias elimination, duplicate deletion,
sorting, and padding preserve those same functions. Recompute cost and exact
ancestry witnesses on the resulting prefix rather than carrying old witnesses
through a structural change. The universal cost bounds then apply afresh.

The one-suffix-junk consequence still follows from exact F and the at-most-21
size; no old junk identity or two-junk assertion is needed. Proper factors
remaining after this normalization stay pairwise incomparable; full TRUE
factors introduced by removal are exempt. This is the same scope of prefix
normalization already reviewed, not an independent Lean formalization of it.

## Suggested future gadget, not yet audited as code

For each qualifying leaf pair, under the guard that both supports are proper,
require a witness bit in S minus T and a witness bit in T minus S. Each witness
must imply both of its signed support literals. The two guarded disjunctions
then enforce strict incomparability; equal proper supports are excluded too.
An exemption flag must imply all eleven support bits, so it cannot spuriously
disable the cut on a proper support. Exact full-support equivalences are a
straightforward implementation. These witnesses and selected-support muxes
would require their own code/projection audit before use.

The finite audit checks every proper comparable support pair on all 2,048
inputs and 384 three-template controls, including duplicate factors, free
TRUE, OR of all inputs, and common-factor reordering. It verifies actual
metadata port maps. These are algebraic truth-function controls, not 21-gate
witnesses. No runtime benefit or SAT/UNSAT result is claimed.
