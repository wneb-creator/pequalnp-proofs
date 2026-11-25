# Exploratory compact-OR search with conjunction pruning

This is an external SAT investigation, not a Lean proof or a resolution of L-meta-1031. Each SAT witness is independently replayed on every assignment. An UNKNOWN/timeout verdict proves nothing. The normalization arguments below have not been formalized in Lean.

The base model is an ordered list of ORs between conjunctions of original variables and earlier OR atoms. The output is another conjunction. AND gates are free and unbounded. Edge-pair positive tests followed by all maximal-independent-set negative tests determine a monotone graph function. All operands read earlier atoms; masks are finite sets, so duplicates and order do not matter.

## Why the pruning is plausible and preserves a minimum compact representation

1. **Disjoint OR operands.** Factor the common atoms from `(C AND A) OR (C AND B)` to obtain `C AND (A OR B)`. Process the program topologically, representing every old atom by a conjunction of new atoms and substituting this representation in later masks. This introduces at most one new OR for each old OR. The two residual operand masks are disjoint. An empty residual operand makes that OR constant true, so it is omitted and the old value is represented by the common conjunction alone. Therefore a minimum-OR compact representation can be chosen with disjoint, nonempty operands.

2. **Positive branch incomparability.** In a minimum-OR representation, each branch of each OR must be true on an edge-pair test where the other is false. Otherwise that OR can be replaced by the dominating branch: all positive gate signatures are preserved and all negative values can only decrease. The output still computes the graph function. Substituting the branch conjunction for the deleted atom and factoring common atoms again yields fewer ORs, a contradiction.

3. **Private negative witnesses inside conjunctions.** Among the minimum-OR programs with disjoint operands, choose one minimizing the total number of selected atoms in every operand and output mask. For a selected atom `i` in a mask `M`, there must be a maximal-independent-set test on which `i` is false and every other selected atom is true. If no such test exists, removing `i` leaves that conjunction's entire negative-test signature unchanged and can only raise its positive-test values. Downstream negative values stay unchanged, while every previously true output on positive tests stays true by monotonicity. The resulting program still computes the graph function, has the same OR count, retains disjoint operands because a mask only shrank, and has smaller total mask cardinality. This contradicts the tie-break.

The private-witness constraint is implemented in linear expression size per mask using prefix/suffix intersections. For each selected atom `i`, the solver requires

`meet(M without i) AND NOT atom[i] AND negativeMask != 0`.

The NOT here is a SAT test of a truth-signature bitvector, not a NOT gate in the represented circuit.

## Exact count versus at-most count

To query at most `k` ORs using exactly `k` slots, the script verifies an input pair whose positive edge signatures are incomparable and each of whose literals is false on some negative test. Repeated unused copies of the OR of those two literals satisfy every pruning rule, while leaving the old output unchanged. The tested C5, Petersen, and Fano instances all admit such a pair. No distinctness constraint is imposed on the new OR-output signatures.

## Controls and scope

Before the longer searches, C5 with at most three ORs must return UNSAT, and C5 with at most four ORs must return SAT with a clean full truth-table replay. The script stops if either control fails. The longer cases are Petersen with at most thirteen ORs and Fano with at most nineteen ORs, each capped at 600 seconds in one serial 256 MB solver process.

A SAT result below the OR-count conjecture would refute that auxiliary bound. It would not by itself refute L-meta-1031, whose objective counts all AND and OR gates and asks for existence of a particular minimum form.
