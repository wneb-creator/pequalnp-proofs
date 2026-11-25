# Empty-ownership local obstruction

This is a **nonminimum five-gate circuit** for a four-gate graph function. It is not a counterexample to L-meta-1031 and does not show that a minimum circuit can have an empty-owned AND.

Inputs0,1,2,3 are a,b,c,d. The graph edges are ac,ad,bc. Gates are:

- wire4 = a OR b
- wire5 = c OR d
- wire6 = wire4 AND wire5
- wire7 = a OR c
- wire8 = wire6 AND wire7 (output)

The output equals ac OR ad OR bc on all16 assignments. The JSON contains the complete truth table. Mask bit i is input i.

Wire6 owns all three graph edges. The output AND wire8 owns none: whenever it is true, its AND ancestor wire6 is true. Every gate nevertheless is essential on every one of the three graph-edge inputs: forcing that gate false makes the final output false.

For every gate, all earlier wires were tested as replacements. No such bypass preserves the output function. The JSON records every test, every failing global-implication input, every failing positive-edge profile, and every resulting output-error input. In particular, no gate meets the checked lower-wire/edge-profile domination criterion.

For the final gate, all128 ordered binary AND/OR replacements over the eight earlier wires were also tested (including repeated inputs). The only correct choices are AND(6,7) and its input swap. Constants are incorrect because the target is nonconstant; unary gates reduce to the already tested wire bypasses. Thus changing only the final gate cannot remove its empty-ownership role.

A four-gate circuit is OR(c,d), AND(a,previous), AND(b,c), OR(last two). Its optimality follows from the checked forest lower bound: this graph has three edges and minimum vertex cover two. The local obstruction therefore shows that edge-essentiality and current one-wire replacement tests are insufficient by themselves; exploiting global minimum size requires a larger rewrite.

Validation is exhaustive Python Boolean evaluation, not a new Lean proof. Full data: final-empty-ownership-obstruction.json. Files are frozen for independent review.

## Singleton acceptance can coexist with star ownership

This separate three-input example is also nonminimum: six gates versus the star function optimum of two. Let the graph edges be ab and ac. The complete circuit is:

- wire3 = a OR b
- wire4 = a OR c
- wire5 = wire3 AND wire4, denoted g
- wire6 = b OR c
- wire7 = a AND wire6, denoted q
- wire8 = g AND q (output)

Here g = a OR (b AND c), while q = a AND (b OR c). Since q implies a and a implies g, the output equals q. All eight assignments were evaluated directly:

| Mask | a | b | c | g | q | Output |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| 1 | 1 | 0 | 0 | 1 | 0 | 0 |
| 2 | 0 | 1 | 0 | 0 | 0 | 0 |
| 3 | 1 | 1 | 0 | 1 | 1 | 1 |
| 4 | 0 | 0 | 1 | 0 | 0 | 0 |
| 5 | 1 | 0 | 1 | 1 | 1 | 1 |
| 6 | 0 | 1 | 1 | 1 | 0 | 0 |
| 7 | 1 | 1 | 1 | 1 | 1 | 1 |

Gate g is the first AND, so it has no earlier AND in its dependency cone. It accepts singleton a and owns both graph edges ab and ac; its owned set is a nonempty star. Gate q also owns those two edges because g is not in q's cone. The final AND owns no edge because both g and q are AND ancestors true on every accepted edge pair.

The checked minimum-circuit domination criterion rules out g in a minimum circuit for this graph: the earlier input wire a globally implies g, and every graph-edge pair where g is true also makes a true. Replacing g by a therefore preserves the edge function and deletes a gate. The criterion requires control of **all graph-edge pairs accepted by g**, not merely the edges owned by g. In a larger circuit, accepted pairs avoiding a may already activate an earlier AND ancestor and consequently fail to belong to g's owned set. Star ownership alone does not exclude that case.

This example establishes the logical distinction between singleton acceptance and ownership; it does not exhibit a minimum circuit with either dirty or empty-owned AND gates.

## Sufficient criterion using essential edges

The following strengthening is proved on paper here, but has not been formalized in Lean in this job. Let h be a gate and h' a replacement computed from earlier wires, with h'(x) ≤ h(x) on every input. It suffices that h' is true on every graph-edge input where forcing h false makes the final output false.

To see this, regard the rest of the circuit as a monotone function F(z,x) of h's output z. The modified output F(h'(x),x) lies between F(false,x) and F(h(x),x). On an edge input where false deletion already leaves the output true, the modified output is therefore true. On an essential edge input, h' is true and the modified circuit agrees with the original. Thus the modified output is pointwise at most the original graph function and accepts every graph edge. Monotonicity then implies equality on every input. An earlier-wire replacement deletes a gate; a replacement binary gate may instead enable a larger subsequent rewrite.

This criterion tests essential edge inputs rather than every accepted graph-edge pair. It still cannot bypass any gate of the five-gate P4 example: each gate is essential on all three graph edges, and all earlier-wire candidates were exhaustively excluded. Empty ownership by itself has not been shown to supply a qualifying lower replacement.
