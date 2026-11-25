# Derivative route

The witness recurrence is a formal first derivative over the Boolean semiring, not the ordinary Boolean derivative. It tracks proof trees in which the opposite variable occurs exactly once. This agrees with the linear-parts description in `PEqualNP.ReadK`.

Checked lemmas in `lemmas/Derivative.lean` (Lean 4.36.0, allowed `PEqualNP.Defs` import, exit 0):

- `derivative_unique`: on a proper circuit, two witness functions with the same input values and the same singleton wire values agree on every valid wire.
- `derivative_zero_forces_repeated_and`: a wire accepting the pair, rejecting a singleton, and having derivative zero has an earlier AND gate whose two inputs both accept the pair and reject the singleton. This is a local repeated-variable certificate.

The proof follows a true child at OR gates; at AND gates with exactly one singleton-false input it follows that input. A derivative-zero input leaf is impossible. The only stopping case is an AND with both inputs singleton-false.

A full target proof still needs counting: both directional derivatives vanish, which forces repeated reads in both coordinates. Each direction provides a repeated-AND certificate, potentially the same gate. The small certificate alone does not yet establish the 65-gate bound.

Checked at 2026-11-25T02:58:48.029919+00:00. Full stdout/stderr log: `/tmp/oec/pequalnp-pilot-60/derivative-full-check.log` (empty on success).

## Checked extensions

- `repeated_and_of_pair` instantiates the repeated-AND certificate directly for real circuit evaluations at a pair and singleton.
- `derivative_true_iff_walk` proves exact equivalence between derivative truth and reachability from its seed through OR gates or through AND gates whose other input evaluates true on the base singleton. Its two propagation lemmas are also checked.

All extensions checked together with the allowed PEqualNP.Defs import, exit 0; complete log `derivative-full-check-3.log` is empty. Root notified immediately. The derivative route has completed its local bridge; global gate counting remains with the structural route.

### OR-frontier eligibility still requires a quantitative argument

For the matching F = xy or zw, the proper seven-gate circuit
`a=x or z; b=y or w; c=a and b; d=x or w; e=y or z; f=d and e; out=c and f`
computes F and both formal derivatives for the marked edge xy vanish. Every internal AND is dirty and its only upward AND frontier is the clean output gate, yet replacing either AND by either operand produces a false pair. All 16 inputs and four factor choices were checked in `firstdirty-frontier-obstruction.json`. This rules out geometry-only existence of a frontier-safe factor; it does not rule out the desired existence theorem under the 64-gate plane bound. The size budget must be used to charge the pair-filtering cost.

### Current quantitative barrier

The clean-case assembly uses singleton support S(w), requires every AND output support empty, and requires the rectangle S(a) x S(b) generated at each AND to lie in the target graph. First-dirty extraction gives a singleton/nonedge pair violating exactly these hypotheses. Later conjunctions can filter the offending rectangle, so extracting a first bad pair does not immediately identify a removable gate. The matching CNF example shows that even all AND frontiers being clean is insufficient to make a factor safe. No valid accounting has yet charged those filtering gates against the plane's 64-gate budget. A separate exact lower bound of 13 ANDs, if obtained, would not by itself provide the required 51 OR lower bound or equality rigidity.

### Fresh derivative construction and domination

`DerivativeWitness.lean` (358 lines, SHA562cda535b73fe0f6a6eface36aea24c462ddeda26f3c9ed0b047576b1ea40f2) compiled with exit0 and empty output. Its new56-line fragment constructs witnesses by a list fold for arbitrary base-wire values and input seed. This supports the checked ClampEssential strengthening: a clamped source need not have zero signatures; representative values and fresh derivatives only need to decrease. The new actual residual condition preserves all positive incidence edges, and minimality therefore yields an essential edge for every gate.

### Marked local obstruction after essentiality

Every-gate-essential does not make repeated-AND witnesses removable: matching F=xy or zw has the sharp four-gate doublezero circuit t=xy, r=t or z, s=t or w, out=r and s. The corresponding65-gate plane construction has no OR whose edge profile is contained in one operand; both final ORs add the omitted star edges to the shared48-edge subfunction. The extra gate pays for duplicate merging.

An edge-redundant OR c=a or b, with the edge profile of b contained in that of a, can be overwritten by a copy of the earlier gate a when a is not an input. This preserves all wire edge profiles and proper physical distinctness, while decreasing ordinary values and formal derivatives. The sum of maximum input indices over all gates strictly decreases, because both copied inputs are below a while the old maximum is at least a. Iteration thus localizes any remaining redundant OR to one dominated by an original input. If that input is unmarked, its two signatures are zero, so bypassing it and collapsing any resulting duplicate gates is derivative-safe; all resulting aliases represent the same input. The unresolved collision case is domination by one of the two marked inputs. These transformations are mathematical plans, not yet formalized.

OR-tightness alone does not force clean ANDs. On P4 with F=xy or zy or zw, p=x or z; a=y and p; b=w and p; c=z and b; out=a or c uses2 ORs (|E|-1) and3 ANDs, all gates essential, but b is dirty. Here one extra AND pays for redundant dirty filtering. The proposal that each OR lowers the AND-closure clean-cover potential by at most one was reported false on a matching example; therefore global OR-tightness cannot currently be identified with stepwise potential-tightness. No such implication is assumed.
