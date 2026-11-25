# Independent full-bound route controls

No full51lower bound or counterexample was found. All results here are ordinary finite controls, not Lean proofs.

## Failed shared-endpoint factorization

The four-path theta decomposes into two six-cycles sharing only opposite endpoints x,y. If each six-cycle had an optimal five-OR realization exposing x OR y, the two circuits could share that gate and combine with one final OR, giving ten ORs for the twelve-edge theta.

A tiny exact canonical control refutes this particular construction: the six-cycle with five ORs and its first OR fixed to opposite endpoints is UNSAT in0.157seconds. Controls pass: an ordinary five-OR baseline is SAT, and forcing the opposite-endpoint wire at six ORs is SAT. All formulas, mappings, exact commands, complete solver logs and reconstructed witnesses are preserved. This is a finite SAT-model result, not a Lean lower bound. The control uses the reviewed global canonical encoder with only a six-cycle scenario and fixed first signature pair added.

## Topological data

Let K_E be all52-edge-free input supports, and K_W the downward closure of the468generic negative rows. K_E has38,730faces; K_W has12,234faces, with cardinality counts `1,26,273,1404,3510,4212,2340,468`. Boundary matrices were reduced over F2 using integer bitsets, with a ten-second internal cap; every computation finished in under0.2seconds.

Nonzero reduced Betti numbers:

- K_E: beta5=39, beta6=1.
- K_W: beta3=13, beta5=1.
- Relative pair(K_E,K_W): beta4=13, beta5=39, beta6=2.

The relative dimensions13+39=52 match the flag count and the standard circuit's39line-union gates plus thirteen point terms. This is a numerical structural observation only. No invariant monotone under free AND and charging shared OR gates was established. Ordinary homological dimension alone is unsuitable: a zero-OR conjunction of inputs already produces a high-dimensional boundary sphere as its false complex. The scripts and complete rank/Betti reports are preserved here for further work.

## Correlation and sharing observations

Every edge-free mixed triple is forbidden by the generic promise. The affine marginal obstruction to the unrestricted quadratic-shadow claim violates such correlations by combining two points into a phantom point incident to a line. This suggests tracking correlation on generic cap rows, but does not establish a new general lower bound.

For a four-line pencil S and concurrent outside lines a,b,c, `(S OR a) AND (S OR b) AND (S OR c) = S OR abc` is valid cleanup under the promise. Thus pure-union normalization is unsound without charging the supporting unions. A size-five union containing one pencil cannot contain another, since distinct pencils have union size seven; this limits direct sharing but does not control sharing of intermediate unions.

A GitHub-only literature search on2026-11-25 did not supply an applicable circuit theorem. The opened arithmetic-circuit survey explicitly studies circuits “having $+, \times$ gates” over the reals, so its lower-bound result was not transferred to Boolean circuits: https://github.com/dasarpmar/lowerbounds-survey/blob/master/chap_simpleLBs.tex . No external numerical claim is used here.
