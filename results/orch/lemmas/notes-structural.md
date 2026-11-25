# Structural findings

Checked `Structural.lean`: monotone context endpoint lemma and full circuit-level two-NOT-output elimination, with no additional axioms or forbidden commands. A circuit `pre ++ NOT a :: mid ++ [NOT b]` whose pre and mid are AND/OR and whose final-NOT output has endpoints false/true computes exactly the source of the first NOT in the pre circuit. This yields a smaller equivalent monotone circuit.

L-meta-5367 uses only Petersen-minus-vertex >=15; replacing its `h14` premise by the now-checked >=16 result strengthens the result from `15 + effectiveReads <= size` to `16 + effectiveReads <= size`. Thus a 19-gate full candidate whose first gate is NOT on input 0 has at most two effective suffix readers of inputs 0 and its free complement. Excluding the exactly-two-reader case requires a semantic argument; generic monotonicity alone has not yet been shown sufficient.

No complete Petersen >=20 proof obtained. The generic cutLast route was abandoned because L_meta_8295 already proves it.
