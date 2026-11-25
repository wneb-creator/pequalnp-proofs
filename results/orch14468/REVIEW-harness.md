# Independent review: Harness

Verdict: PASS as an 11-gate construction and conditional replacement
harness. The binary-count floor is an explicit theorem premise; this
module alone does not discharge it or prove the posted statement.

Reviewed source:107lines,3,892bytes, SHA-256
`0e6350139c46f120a30d43396fd672fa0a5fa7c948c2ad78581f17bb4699e582`.

The exact nine target edges match the posted list, including 5–7. The
`posted` definition preserves the list-index/default-value semantics of
the desk statement. `vectorEight` and `equalEight` reduce every function
on `Fin8` to the full eight-Boolean vector, so the finite `by decide`
checks cover all256 assignments rather than a restricted sample.

The baseline is exactly the independently validated 11-gate JSON
construction, with four ANDs, seven ORs, and output18. All operands refer
to earlier wires. `baseline_monotone`, `baseline_size`, and
`baseline_correct` establish the required shape, size, and full target
semantics; `baseline_posted` transports through the separately checked
target/posted equality.

`replacement_of_binary_floor` is sound for the full public gate-list
model, without an extra backward-reference or exact-fanin assumption.
If no NOT gate occurs, it returns the original circuit and removes the
NOT alternative using the actual absence proof. If a NOT gate occurs,
the count of non-NOT gates is strictly less than total length. The
assumed lower bound of ten non-NOT gates then forces total length at
least eleven, allowing the fixed baseline. It does not assume that a
NOT gate is useful or that it is the only NOT. This stronger conditional
statement can later be specialized to the desk's at-most-one-NOT premise.

I checked the archived successful compilation record and its complete
empty stdout/stderr logs; no build was rerun for review. The source
imports only `PEqualNP.Defs` and contains no `sorry`, new axiom,
`native_decide`, forbidden root marker, string literal, or attribute.
Only permitted heartbeat and recursion limits are set. Exact source
hash and compile status are recorded in `harness-validation.json`.
