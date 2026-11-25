# Restricted phase from the 27-gate six-owner approximation

The source `circuit_search/feature6-context-27g-best-25.json` has exact stars for rows 1, 3, 4. Its remaining central function simplifies by Boolean absorption to

`(p0 OR p2 OR p5)*(l6 OR l11 OR l13) OR p5*(l8 OR l10) OR (p0 OR p2)*(l7 OR l9 OR l15) OR p2*l16`.

This accounts for the six extra pairs `(2,6),(5,6),(2,9),(0,11),(2,13),(0,15)`. Holding row3's computation fixed gives a twelve-gate three-owner subproblem with outside OR features, which cannot become exact with only one added gate by the checked noncollinear three-owner bound. A successful repair must alter another row's computation.

Rows 0,2,3,5 form a four-point arc. Their combined cone ends at source wire46 and uses17 paid gates; an18-gate exact replacement would fit the six-owner target28. Restricting the four private source lines9,16,14,8 to false and simplifying yields the13-gate,4-AND phase `context27-four-owner-kernel.json`. Canonical kernel raw indices0..9 map to source raw indices `[0,2,3,5,7,6,13,10,11,15]`. The three canonical free opposite-pair sums map to source supports `{6,11}`, `{7,10}`, `{13,15}`. Only the first is used in this phase.

The generator explicitly checks the restricted source cone against the emitted phase on all1024 raw assignments. It then independently checks the target's twelve edge terms. Results: no false negatives,20 false-positive assignments,seven failing negative boundary cases. The five extra primes are `(1,5),(3,5),(1,6),(0,8),(0,9)`. Three coincide with the existing fourteen-gate manual phase's bad pairs; the new phase trades two additional bad pairs for one free gate.

This is computationally verified approximation data, not a Lean proof, an exact witness, or a sufficient restoration argument. Complete output is in `context27-four-owner-kernel.validation.log`.
