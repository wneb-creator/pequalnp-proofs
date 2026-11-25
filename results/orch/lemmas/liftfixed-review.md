# L-meta-3754 independent audit

The exact target asserts every AND gate is BelowF for a least AO2 circuit computing a bipartite C4-free graph function and satisfying Core.IsLiftFixedPoint. No full proof or refutation is claimed here.

## Definition audit

- `Defs/TopForm.lean`: IsAO2 requires AND/OR only, ReadsBack, and exactly two operands. IsLeastAO quantifies over all such circuits of the same input dimension and exact function. NoFourCycle bounds every distinct pair of vertices to at most one common neighbor.
- `Defs/Core.lean`: LiftAt applies only to an OR gate in the output cone which is not BelowF and has a nonzero implicant operand. IsLiftFixedPoint is the negation of the existence of such a local lift.
- Zero-arity gates, self-reads, and forward references are excluded by the posted assumptions. Repeated operands are permitted, but semantic alias deletion contradicts leastness. An out-of-range output computes false; if the graph function is false then the empty circuit of output n shows every least circuit has zero gates.
- Every actual wire of an AO2 circuit is true on the all-true assignment. Hence an actual BelowF operand is nonzero and satisfies IsImpWire; this bridge does not require n positive separately.
- Dead gates cannot survive leastness, but this requires a deletion proof. One must not silently substitute output-cone membership for the target's unrestricted gate index.

## Why fixed point alone does not settle the target

For the path with edges ab, bc, cd, the five-gate circuit
`((a OR c) AND (b OR d)) AND (b OR c)`
computes the graph function. Its first AND is dirty on a=d=true,b=c=false. All three OR gates read only raw variables, so the circuit is a lift fixed point. The graph is bipartite and C4-free. Boolean equality was exhaustively checked on all 16 assignments by Python. This is NOT a counterexample to the posted statement: the four-gate circuit `(b AND (a OR c)) OR (c AND d)` computes the same function, so the five-gate circuit is not least. Minimality is essential, and a proof that assumes every fixed point is already clean is invalid.

## Independent partial reviews

Reviewed frozen Tools275 SHA a245bdfdb9838a6d6c6824024d6810ed44a4b96b4ea7a8c342e135e3bd4894f9, Bypass394 SHA 83fcc84601196141d19a35fcdcfc83932e4634bc2a6043a16adc7a5abd48a930, and Ledger357 SHA 754b6caede65bb30c69f6053fe6d083e03d5d5343900247a677092b719edf69d. All are approved only for partial preservation. They import Defs only, use the owned L_meta_3754 namespaces, and have no forbidden declarations or syntax. Bypass prefix and AO2 bridge match the accepted L_meta_1485 source exactly; source attribution should accompany the copy.

- Tools proves OR-descendant propagation, the single-AND consequence, and the empty-graph leastness case.
- Bypass proves that an AND gate cannot directly read a BelowF operand in a least circuit, and no gate equals an earlier wire semantically.
- Ledger proves all-true satisfiability, BelowF forward closure in a lift fixed point, output-cone transitivity, and that an earliest dirty AND has only OR ancestors.

These do not close the remaining structural step: an earliest dirty AND formed from pure OR signals must be shown incompatible with leastness and the graph hypotheses. Its operands can have false-positive independent sets, and local fixedness does not itself remove them.
