# Independent review: NineGeneralFloor

Reviewer: lower_bound. Reviewed 2026-11-25T16:12:04.282375+00:00.
Source: results/orch1884/lemmas/NineGeneralFloor.lean
SHA256: f1b11610b17cdde28749ae7841f9079528fe9e5071729ce8598dfa78b2513370
Bytes: 9543
Verdict: PASS. Successful dependency-test compilation was separately reported by lean_setup.

The shared compiler tracks exact circuit prefix semantics as functions on input rows. AND/OR consume one Reach step, including nullary or unary gates; this overcharges trivial gates conservatively. NOT consumes zero steps only when mode=true. Its nullary result is true, and the nonempty case negates only the first input, matching GateOp.eval even for an ignored second operand. All absent or forward wire reads remain false.

The compiler therefore lower-bounds the number of nonNOT gates. The signed Reach bridge is a constructor-preserving conversion between identical public models; inputs and graph truth tables match. count_partition uses the exact library notCount predicate. With zero NOT gates the monotone16 certificate applies; otherwise signed15 plus positiveNOTcount gives total16. No hidden gate arity, output-validity, source-map, or read-order assumption is added.

The final assembly removes only the cross-module Reach conversion and invokes the same signed Lower theorem from its retained signedRoot14 certificate. The certificate must retain isNot, and the assembly generator now does so. Full standalone compilation remains pending.
