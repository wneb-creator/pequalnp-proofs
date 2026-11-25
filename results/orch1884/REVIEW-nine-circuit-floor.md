# Independent review: NineCircuitFloor

Reviewer: lower_bound. Reviewed 2026-11-25T15:56:52.473799+00:00.
Source: results/orch1884/lemmas/NineCircuitFloor.lean
SHA256: 445fcd30f2db31bb9adef82dec09dd90536ebdaa9326173427553a29108d44d8
Bytes: 5521
Verdict: PASS (semantic and format review; successful dependency-test compilation independently reported by lean_setup).

The public Reach compiler represents each circuit wire as a Boolean function. Every AND/OR gate consumes one Reach step; nullary constants and unary identity gates are conservatively charged one step, preserving the required upper bound on cost. Missing or forward references use false exactly as Circuit.wires does. The mode remains false throughout, so the proof cannot use free negation. run_rows connects the prefix semantics to actual evaluation, and root_rows plus edge_table connect the nine input truth-table roots to the precise Petersen vertex-deletion function. Applying the checked nineMonoFloor therefore yields16≤C.size for every Monotone2 circuit computing edge. No hidden strict-arity, valid-output, or read-order assumptions were introduced.

The file contains only the MonoBase import, declarations in the1884 namespace, and ordinary proofs. No sorry, new axioms, native_decide, string literals, attributes, or forbidden _root_ marker were found in the source. Standalone assembly with the certificate remains a separate pending validation.
