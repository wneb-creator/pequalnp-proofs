# Two auxiliary counterexamples

Neither example refutes L-meta-1024 or supplies a thirteen-output circuit below39 gates. Both were independently checked on every one of the8192 Boolean assignments, including all3003 required band inputs.

## Eight-gate formal-cost obstruction

For lineL={0,1,3,9}, the circuit computes x1 OR x3 OR x9 OR (x0 AND (x2 OR x4)) OR (x0 AND (x5 OR x6)). It is globally bounded by the line OR, agrees on the entire required band, and differs on32 other assignments. Its capped additive false-certificate cost is5. Factoring the repeated x0 gives the same function in7gates with cost4. Thus a semantic four-point false certificate does not imply additive formal cost at most4 for the given circuit. This example is not a minimum-circuit obstruction.

special_status wrote the original scalar checker and toolchain_setup independently verified its8192-bit truth table, cost and equivalent7gate factorization. The complete independent log is included.

## Nine-gate two-output obstruction

For two lines A=pabc and B=pdef and q outside their union, let U=OR(a,b,c), V=OR(d,e,f), H=p AND (U OR V OR q). The two outputs U OR H and V OR H use9total gates, with7internal gates and2OR roots. Both are globally line-bounded and band-correct; each differs from its line OR on32 other assignments, including singletonp. This refutes only the proposed10gate lower bound for two globally nonordinary outputs. It is consistent with the checked impossibility using at most6internals and with the posted thirteen-output39gate claim.

fresh_proof wrote the original scalar checker; special_status independently checked the JSON circuit using bitvector truth columns. The complete independent log is included.

The two independent validators accept their corresponding JSON file as a positional argument and can be run from this directory. Original generators are preserved verbatim and retain their original scratch/output paths; do not assume they are portable. Manifest hashes identify every preserved source and complete log. No Lean proof is claimed for these auxiliary examples.
