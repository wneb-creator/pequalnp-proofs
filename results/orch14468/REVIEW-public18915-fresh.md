# Independent source review: PASS

Reviewed final named source `lean/PEqualNP/Outside/L_meta_14468.lean`, SHA256
`5c0f4a872ef18607dfa4be1c150020e256eff4df564c55e8898fdc47bd42f124`.
The copy in `lemmas/Public18915.lean` has the same hash.

The original public PR18915 source is 112,588 bytes, SHA256
`81cc0c084c6e6374795ee8f2dfa86c517c61cb34434911ba54cf6b2f1bd53c74`.
Public author: `Leg0shii` (Legoshi), head
`c63b1058c3fe975a0c152a1b88930e9c6f41c837`.
An exact textual diff confirms that the adapted file changes only removal of
the broad Mathlib import and addition of the attribution comment. No proof,
table, definition, theorem statement, or option differs.

The final theorem statement equals the posted gap statement after whitespace
normalization. It uses the fully qualified project Gate and Circuit types.
No weakened target or additional hypothesis appears in the final theorem.
The allowed import is `PEqualNP.Defs`. The file is below the 512 KiB cap.
The only options are local `maxRecDepth` and `maxHeartbeats` settings. The
source has no forbidden proof placeholders or extra axiom declarations,
native evaluator shortcut, unsafe/partial definition, custom instance,
compiler command, syntax extension, strings, or `_root_` qualifier.

Proof chain inspected:

* `allgb` checks the finite signed live-wire atlas through budget 6.
  `boundgb` consequently proves a seven-binary-operation lower bound on the
  five-variable cofactor.
* `fullBound` applies the checked input-fixing lift to three essential
  signatures. The signature permutation is explicit: raw variables map to
  signature coordinates [5,1,3,6,7,2,4,0]. Thus fixing coordinates 5,6,7 to
  false fixes original variables 0,3,4. The remaining graph is the triangle
  1–5–7 plus the path 7–2–6.
* `binaryLower` compiles an arbitrary legal AND/OR/NOT gate list into that
  signed model. It proves at least ten non-NOT gates, allowing arbitrary NOT
  count. Invalid reads and ignored extra NOT operands retain the project
  evaluation semantics through `getD`, `run_bit`, and `exeBits`.
* `solve` returns the original list if it contains no NOT gate. If it contains
  a NOT, its length is strictly greater than its non-NOT count, hence at least
  eleven, and the explicit eleven-gate monotone circuit fits. The posted
  at-most-one-NOT hypothesis is unused because this argument is stronger.
* The final `solve (fullBound allgb)` discharges both conditional certificate
  premises; neither remains an external assumption.

Independent Python checks, saved in
`notes/pr18915-independent-finite-check.json`, validated all 512 signature
rows against the graph, the input-fixed cofactor table, and the monotone
circuit on all 256 inputs. The circuit has exactly eleven binary gates and
all its references are earlier wires.

This review found no semantic or plain-file blocker. The named Lean build and
allowed-axiom audit are separate checks owned by lean_setup/lower_bound; this
review does not substitute a textual scan for their kernel checks.
