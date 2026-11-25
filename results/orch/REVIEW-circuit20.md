# Independent review: twenty-gate Petersen construction

Reviewed UTC: 2026-11-25T14:14:45.032395+00:00
Reviewer: lean_setup
Verdict: PASS for preservation of the checked construction; combined target must be rebuilt.
Source: /tmp/oec/pequalnp-pilot-103/Circuit.lean
SHA256: fda5386997343a09a5ddd08ac9cd459bd67791db8bb18ed0295e35c71123d7d0
Lines: 40

- Parsed all fifteen ordered edge terms from the actual desk statement and from petersenValue: the sequences match exactly.
- Parsed the construction independently: exactly twenty AND/OR gates, each reading two earlier input/gate wires; output wire 29 is the last gate.
- Exhaustive independent Python evaluation of all 1,024 ten-bit inputs matches the posted Petersen expression.
- The construction has no NOT gates and is monotone. It proves the upper bound of twenty gates, not the posted impossibility of at most nineteen gates with a NOT.
- Imports and namespace are permitted. All declarations are inside the permitted namespace; limits are scoped permitted options. No forbidden commands, placeholder, axiom, root qualifier, strings, attributes, exported instances, or custom data types occur.
- The two supplied compile logs are empty; author reports compilation exit 0. This reviewer did not rerun Lean.
- Source contains no apparent credential material. When combining with Finite, retain only one definition of petersenValue and rebuild before pushing the combined target.

The posted theorem and local checker acceptance are still required before a final one-file proof PR.
