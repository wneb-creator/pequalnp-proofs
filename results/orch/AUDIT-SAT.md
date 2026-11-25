# Independent SAT encoding audit for L-meta-9811

Auditor: lower_bound subagent. Source inspected: `/tmp/oec/pequalnp-pilot-85/counterexample/synthesize.py`, SHA-256 `e993ba5c5e610a351bc6234436cebf11f3e6855d0ecb941f730a0c1e19f84e68`.

Verdict: no encoding defect found. The unrestricted model and the three optional cuts below preserve existence of a circuit of at most 24 gates for the posted target. This is an independently checked mathematical argument and executable testing, not a Lean proof of encoding completeness. An UNSAT solver result would still require a kernel-checked certificate and formal encoding correspondence.

## Root-definition correspondence

The actual definitions were read in `lean/PEqualNP/Defs/CircuitLowerBounds.lean` and `MetaComplexity.lean`.

- Every allowed gate is AND, OR, or NOT, and has zero, one, or two supplied wires.
- A supplied index at or beyond the currently available wires reads false. The model's one false source at every gate represents all such indices.
- Nullary AND is true and can be represented by NOT(false), with the same one-gate cost. Nullary OR is OR(false,false).
- Unary AND/OR is an alias and can be represented by OR(a,false), with the same one-gate cost. Two equal supplied inputs likewise collapse to an alias.
- NOT uses only its first input; its absent first input defaults to false. Its second input may therefore be forced to the false source without loss.
- AND/OR inputs commute, so sorting their numeric source indices is safe.
- Prune every gate outside the actual output cone and remap all remaining wires. If the output was an input, there need be no remaining gate; an invalid output is false. Pad the selected output with OR(output,false) until there are exactly 24 gates. Thus requiring the last gate as output does not exclude a circuit of smaller size or one whose original output was earlier.
- Duplicate gates and dead gates are allowed by the base encoding; their presence does not compromise completeness.

The selector one-hot clauses, conditional wire mux clauses, operation clauses, final output unit clauses, model decoding, and full-truth-table evaluation were inspected independently. The AND, OR, NOT, and mux clauses were checked on every Boolean assignment.

## Safe optional cuts now implemented

### `--cone`

Every input and every non-output gate must be used by a later gate. Every input is essential for the posted target: turn on one chosen neighbor, then toggle the input itself. The two evaluations are false and true. Pruning the actual output cone therefore retains all 14 inputs, and every retained non-output gate has a later reader. Padding retains this property.

The implementation starts gate readers of wire `14+k` at gate `k+1`, so it does not mistake gate `k`'s false-source selector for a read of that gate's own output. NOT's ignored right input is always its current false sentinel and does not create a spurious later read.

### `--ordered`

The numeric maximum of the two selected sources is nondecreasing across gate slots. Because AND/OR sources are sorted and NOT's right source is its current false sentinel, this maximum is the selected right-source index.

To prove existence, consider an adjacent inversion at slots j,j+1, whose maxima are r>q. Here r<=14+j, because slot j's false sentinel is 14+j. Thus q<14+j, and the next gate uses neither the current output 14+j nor its own false sentinel. The two gates are independent and may be swapped. The later gate's actual sources remain unchanged when moved earlier; the original gate's false sentinel, if used, becomes 14+j+1 when moved later. Relabel uses of their outputs at later gates. The maxima vector strictly decreases lexicographically at slot j, so finite descent terminates at the desired ordering. With the cone cut, the final two gates cannot be inverted: the penultimate gate must feed the last gate. Hence this reordering keeps the output last.

Sorting additional tie keys indiscriminately is not justified by this argument. In particular, a current false sentinel and the current output have the same numeric index, so equality of maxima does not imply independence.

### `--distinct`

AND/OR gates must have unequal numeric source indices. Replace AND(a,a) or OR(a,a) by OR(a,false) when a is not the false source. Remove any resulting false constant gate by redirecting its uses to the free false source, repeating as necessary. Prune and pad with OR(last,false). Since the target is nonconstant, these padding sources are distinct. NOT(false) still supplies true when needed. Reordering preserves distinctness.

## Executable checks

Scratch audit script: `lower_bound/audit_synthesize.py`; full output: `lower_bound/audit_synthesize.log`.

- 2,000 random root circuits including nullary/unary gates, future indices, invalid outputs, earlier outputs, and dead gates: normalization and sorting preserved all 16,384 input evaluations.
- 3,000 valid-source random DAGs: normalization and sorting preserved all input evaluations, with up to 16 adjacent swaps in a case.
- 40 generated CNFs: explicitly reconstructed complete assignments satisfied every clause, and decoding reproduced the chosen circuits.
- 80 generated CNFs with all three cuts enabled: randomized 14-input AND/OR trees with zero to seven input NOT gates, sorted and padded to 24 gates, satisfied every clause under the reconstructed models.

Fixed/unlocked synthesis modes are intentionally incomplete searches. A timeout or unsuccessful witness search is not evidence of impossibility.
