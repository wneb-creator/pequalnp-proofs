# Backward and exact-fan-in-two normalization

Compiled BackwardNormalize.lean closes the technical normalization needed before ownership-preserving local rewrites. It imports only PEqualNP.Defs.

The proof simulates original wires by either constant Boolean functions or valid current wires. Each original gate adds at most one new binary AND/OR gate. Constant, unary, and unavailable-input computations collapse during simulation. All new inputs point backward. If the final output is constant, graph-function correctness forces false; a zero-gate out-of-range-output circuit represents it. Otherwise the simulated output wire is used.

normalize_graph: any Monotone2 circuit computing graphFun G empty has an IsAO2 replacement of no greater size.
normalize_minimal: if the original is globally IsMinimalMonoCircuit, the replacement is also globally minimum and has exactly equal size. IsAO2 supplies AndOrOnly, ReadsBack, and exactly two operands per gate.

The normalization does not preserve every original gate or its ownership. It is intended to choose an initial normalized minimum before repairing a prefix. It does not prove every minimum circuit is itself normalized, nor the final universal star-profile result.

The simulation body is adapted from accepted L_meta_4181.A1527; the public wrappers preserving exact graph semantics and global minimality are new.
