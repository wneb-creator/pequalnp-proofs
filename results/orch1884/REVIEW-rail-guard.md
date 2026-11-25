# Independent review: RailGuard

UTC: 2026-11-25T16:33:35.801478+00:00

Verdict: PASS for this checked conditional comparison helper. No full L-meta-1884 proof is claimed.

Source: `results/orch1884/lemmas/RailGuard.lean`, 5859 bytes, 137 lines, SHA256 `ec061ccb1a8b7f3a363537e67d1c625ed0b8785ecb0e371924623f59e644bb3a`. The author's Lean run exited 0; complete stdout and stderr at `/tmp/oec/pequalnp-pilot-103/1884-rail-guard-001.*` are both empty. This review did not rerun Lean.

`comparable` explicitly requires equal initial lengths of at least 11 and comparison at every index except 0 and 10. `step_comparable` handles existing wires, the newly appended result, and out-of-range false defaults. `run_comparable` performs list induction; ordinary AND/OR gates use pointwise Boolean monotonicity, while gates reading an exceptional source require the stated prefix-specific comparison hypothesis. The final output is explicitly excluded from the two exceptional input positions.

`reader_comparison` discharges the exceptional case under explicit stronger premises. A gate reading source 0 has true output in the higher execution by hypothesis. Any remaining exceptional reader reads source 10, is AND by hypothesis, and evaluates false in the lower execution because source 10 remains the original false input throughout every prefix. If a gate reads both rails, the positive-reader premise handles it. Arbitrary arities and invalid references are consistently covered by the library semantics; no hidden fan-in or well-formedness assumption is needed.

The file imports only PEqualNP.Defs, uses the correct L_meta_1884 namespace, and has no options, attributes, string literals, sorry, axioms, native_decide, unsafe declarations, or forbidden root-namespace text. It is below 512 KiB. No credentials or secret-like content occur. The assumptions do not establish the positive-reader condition for a Petersen circuit; that application remains separate.
