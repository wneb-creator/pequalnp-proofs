# Signed/polarity SAT bridge assessment

## Exact encoder

Scratch sources: `synth_binary.py`, `add_inversion_budget.py`, `normalize_cases.py`, and `decode_physical.py` under `/tmp/oec/pequalnp-pilot-111/counterexample/`.

A semantic gate is `y = ((a XOR ca) AND (b XOR cb)) XOR co`. The eight `(ca,cb,co)` choices are `(1,1,0),(1,0,0),(0,1,0),(0,0,0),(1,1,1),(1,0,1),(0,1,1),(0,0,1)`, with truth masks `1,2,4,8,14,13,11,7`. Normalized jobs keep indices 1,2,3,4: NOT-a AND b, a AND NOT-b, AND, OR. Each semantic wire is false on the all-zero input.

Every producer has a freely chosen primary physical phase `p_i`, meaning its primary physical wire is `z_i = y_i XOR p_i`. Input phases are fixed false. A complement flag `c_i` permits one shared physical NOT copy of `z_i`. A gate reading producer i requires complement bit `d_i = p_i XOR ca_i XOR co XOR p_output`; if this bit is true, the flag must be true. The physical gate is OR when `co XOR p_output` is true, AND otherwise. If the final producer phase is true, its flag must be true to recover the semantic output. The budget counts flags over both inputs and gate producers, including the output producer.

`SignedGate.lean` now kernel-checks these local identities, the four-operation normalization table, and that normalizing a function and its negation gives the same semantic wire. It compiled with empty stdout/stderr. It proves no global representation or count theorem.

## Proposed physical-to-signed invariant

Process old physical gates in order. Map each old wire to either a Boolean constant or a pair `(base producer, desired raw phase q)`. Maintain a list of semantic base functions, each false at zero, primary phases p, and a set of flagged producers. A reference `(i,q)` denotes `y_i XOR q`; if q differs from p_i, i is flagged.

- Input i creates base function x_i, primary phase false, no flag.
- Invalid/forward reads become constant false, exactly as Circuit.eval specifies.
- NOT of a constant flips the constant. NOT of `(i,q)` changes it to `(i,!q)` and inserts i into the flagged set if necessary. This charges at most one new flag per original NOT.
- AND/OR with a constant, or two references to the same base, simplifies to a constant or one of the input raw references. It introduces no flag and no signed binary gate. In particular, an alias never creates a raw phase that was unavailable on its input.
- AND/OR on distinct bases creates one fresh base. Normalize its truth table using the two desired raw phases, and choose the new producer primary phase to be the physical output value at zero. This gives one of the four allowed operations. The checked parameter identity shows each required input complement is precisely its existing desired raw phase relative to its primary phase. No new flag is charged.

Thus the intended global invariants are new binary count ≤ original non-NOT count and flag count ≤ original NOT count. Crucially, a producer may have primary phase true for free: AND(NOT x, NOT y) normalizes to semantic OR, whose primary physical value is negative. Counting all negative semantic uses as new NOTs would be wrong.

## Remaining global proof obligations

1. Implement the reference translation and prove its semantic invariant for Circuit.wires, including empty/unary gates and invalid reads. Preserve the flag provenance invariant; existing free-complement `Extended.extract` does not retain it.
2. Build a physical circuit from any signed DAG and its phase/flag assignment. Put flagged input NOTs first, then each binary gate followed by its flagged complement. Prove size = binary count + flag count, NOT count = flag count, and output correctness.
3. Trim unused signed producers and aliases/constants, relabel phases/flags, and prove neither count increases. Ensure the output is the final gate and every earlier gate has a later reader.
4. Sort each source pair, exchanging the two asymmetric difference operations when needed. Then reorder adjacent independent gates into the encoder's lexicographic order, again relabeling phases/flags.
5. Produce a satisfying assignment of the exact new CNF, including its one-hot operation/source constraints, truth rows, phase implications, and flag cardinality clauses. The physical LinkN2 counted bridge does not apply directly.
6. For the two 17-gate shards, connect the checked first-normalized-OR theorem and Petersen input automorphisms to the exact first pair (0,1) or (0,2).

The exact 17/18 gate counts need no padding once the global reconstruction is checked: the universal binary floor forces at least 17 normalized binary gates, while the original ≤19 circuit containing a NOT has at most 18. At 17 binary gates the remaining flag budget is at most two; at 18 it is at most one. Zero flags remain allowed.

## Existing reusable material

`CombinatorialCore.lean` / `Strong.lean`, namespace Extended: `nrm`, `gv`, `execute`, `Repr`, private `gate_rep`, `pull_gate`, `extract`, and `execute_bits` provide semantic normalization and a non-NOT count bound. They deliberately forget primary polarity and NOT provenance, so their result alone cannot justify the inversion budget. The local gate cases may be adapted.

The checked `CertificateTransport.lean` provides physical AND/OR/NOT normalization, kernel LRAT soundness, and physical at-most-NOT CNF transport. Its basic list-wire and adjacent-swap arguments may be reused, but its Model operations and padding/NOT invariants differ from the signed encoder and cannot simply be substituted.
