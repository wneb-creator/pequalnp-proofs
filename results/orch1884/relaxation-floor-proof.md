# Checked 25-row monotone lower bound

Completed 2026-11-25 16:52 UTC. This is a proved intermediate result for L-meta-1884, not the posted theorem itself.

`RelaxationFloor.fourteen` proves that every `Monotone2` circuit satisfying the twelve positive rows and thirteen negative rows below has at least fourteen gates. Inputs are nine ordinary Boolean coordinates, indexed by the original Petersen vertices 1 through 9. Arbitrary original gate indices, constants, unary gates, repeated operands, and unused gates are covered by the initial circuit quantification.

- Positive rows: 3, 6, 12, 33, 66, 132, 264, 80, 320, 288, 160, 144.
- Negative rows: 25, 52, 58, 69, 100, 104, 138, 201, 274, 385, 386, 21, 273.
- Row `m` assigns coordinate `i` the bit `m.testBit i.val`.
- No requirement is imposed on other rows. In particular, row 260 is not needed.

The checked proof first replaces a putative circuit with a globally least, backward-reading binary monotone circuit of the same function, at a fixed point of the safe-OR lifting procedure. The exact input-2-false cofactor requires twelve gates, so a circuit of size at most thirteen has exactly one raw-input-2 reader. An AND reader must have a later reader, and restriction deletes both, contradicting the twelve-gate cofactor lower bound. An OR reader has an input-independent partner that the finite semantic lemma proves implies the target. A satisfiable such partner puts the OR gate in the closed output-OR set, contradicting rejection of the singleton input 2; an unsatisfiable partner makes the gate a removable copy. Both operand orders and repeated-operand cases are handled.

The exact nine-input graph requires sixteen gates by the existing checked certificate and an explicitly checked permutation. This forces the relaxed function to accept the exceptional independent-set row 277. The eight-input lower bound of twelve uses the four-gate extension back to that nine-input graph; no second large finite certificate is needed.

Validation:

- `RelaxationFloor.lean`: 91 lines, 3,970 bytes, SHA256 `f3045258a048f4fe5861d4c42fe197f838e526fab00575018f5d7776fe02e82c`.
- Lean compilation and module export succeeded, exit 0. Complete logs: `/tmp/oec/pequalnp-pilot-103/1884-relax-floor-second.stdout` and `.stderr`, both empty.
- The separate axiom query succeeded, exit 0, and reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Complete logs: `/tmp/oec/pequalnp-pilot-103/1884-relax-floor-axioms.stdout` and `.stderr`.
- This is currently a dependency-module proof. Its helper imports are not the permitted final single-file submission format; root owns eventual inlining and the posted-theorem checker.

New checked components owned by lean_setup:

| File | Role | SHA256 |
| --- | --- | --- |
| ClosedOrSet.lean | Closed OR-set propagation, fixed-point existence, copy deletion | 1f45e4239020b1583991a5ed484ea56be723359d71000f8905e8c3df21825ace |
| ClosedOrSafety.lean | Unsatisfiable-partner case, circuit monotonicity | 09ddf5d680bc8160ab2853ffd3d78cb419b5c947349dc4bfb986aba2757f84f5 |
| ClosedRelaxOr.lean | First actual-circuit sole-OR wrapper | feba4203e7cca2b0460f374403fe8cdc8413174043edacbc72ae4ac1737b7c99 |
| ClosedRelaxOrGeneral.lean | Actual-circuit sole-OR wrapper, both operand orders | 2ceea11c3fe4341e37b17c882f379e76752c94fdd2741c5801287b3824dc4c7c |
| LeastLiftNormalization.lean | Arbitrary circuit to globally least binary lifting fixed point | fff5cf7346e22d550247c94e025a1a49fac487129f4cf663de81f75e260192f8 |
| RelaxedFacts.lean | Nonconstancy, singleton rejection, raw-input reader existence, repeated-operand exclusion | fac8538dbbba8f689529985fc57f812ca11c4580103a936e994ea8b820269c74 |
| RelaxationSemantics.lean | Natural-coordinate sixteen-gate bound and exceptional-row acceptance | d5b6b6803ca548fe09855ef6d2c034de6c8db2b600f1a6b5668d4b20dc2afd6c |
| LeastGateFacts.lean | Least-circuit liveness and AND-output exclusion | 7e648c34b04364a693513f7bc3a6ced2f05d1a3ea8b0f3dbb23d4482f863ddd3 |

Other agents supplied the checked row semantics, sole-reader simulation, finite partner safety, eight-input extension and restriction bound, unique-reader decomposition, and two-deletion AND restriction. The final assembly consumes those exact checked interfaces.
