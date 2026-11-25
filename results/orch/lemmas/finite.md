# Finite verification and cutLast route

- The three existing reductions are R_meta_2592_318 (last NOT factorization plus monotone separator), R_meta_2592_408 (normalization plus normalized bound), and R_meta_2592_271 (binary floor 15 plus exclusion of 1..4 NOTs).
- Defs/LratEncoding only encodes AND/OR/TRUE circuits. It cannot directly certify this general NOT lower bound. Encoding correctness is in outside library modules not available as permitted imports.
- Drafted a generic exact last-NOT factorization lemma in /tmp/oec/pequalnp-pilot-109/finite/CutLast.lean. It handles invalid and empty NOT inputs with an out-of-range default wire. Awaiting Lean setup before verification.

- Last-NOT split is already accepted as L_meta_8295; draft is redundant and is not a new proof result.
- Ported accepted L_meta_4725 into target subnamespace PEqualNP.Outside.L_meta_2592.BinaryFloor, with all helper theorems converted to lemmas. Scratch finite/HighNot.lean (3,228 lines, 145,037 bytes) adds atMostFourNot and highNotImpossible, rigorously eliminating circuits with at least five NOTs once compiled. Source attribution retained. Awaiting cache/build readiness.

- 2026-11-25T14:09:28Z: HighNot.lean compiled successfully (exit 0). Full diagnostics: /tmp/oec/pequalnp-pilot-109/finite/high-not-build.log. SHA256 7823c8648e521541c4e05085327ed3ce37e88603e56c0c86535c35db02b4ac4c.
- Result names: PEqualNP.Outside.L_meta_2592.BinaryFloor.atMostFourNot and .highNotImpossible. Correctness hypothesis uses BinaryFloor.petersenF, definitionally the Petersen list of edges; use the same simp conversion from original L4725 final theorem for the desk expression.
- Independent preflight review found no forbidden text; source has remaining private theorem keywords and no final posted theorem because this is explicitly partial. Parent notified immediately for push-early preservation.

## Signed-binary search

- Implemented finite/synth_signed.py: 15 binary AND/OR gates, signed inputs, at most four distinct source wires used negatively (global output inversion included). Cardinalities are pure bitvector sums to retain Z3 QF_BV bitblasting. Packed initial samples are all 76 false rows plus 15 edge rows; each candidate is independently tested on all 1,024 rows, with counterexample-guided refinement.
- Added exact-equality constraints from structural agent on expanded topology: each source positive-use count plus one if negated is at most two; each shared NOT result is used at most twice. These are not the unsound bound of two on collapsed signed fanout.
- Encoding sanity check: a pinned 20-gate monotone Petersen circuit satisfied all 1,024 rows in 0.10 seconds and independently evaluated with zero errors. This is a validation witness, not a refutation (it exceeds the bound).
- Started a five-minute pure QF_BV run with 15 binary gates and four negated sources, plus a separate five-minute C++ stochastic signed-circuit search. Full logs stay in finite/signed15-fan2.log and finite/signed15-stochastic.log.

- First signed15 expanded-fanout Z3 run: UNKNOWN at 300.19 seconds (timeout), 135,001 conflicts, 113 MB peak. This is not an impossibility result.
- Signed15 stochastic run: completed 300 seconds, 437,190,000 candidates, best weighted truth-table error 39. Signed18/one-NOT: 448,080,000 candidates, best weighted error 15. No counterexample found.
- Second signed15 Z3 run adds collapsed fanout≤2 and nonempty first-input classes, derived by the structural agent from exact binary-floor equality; all constraints are optional switches in synth_signed.py.
- Added DeMorgan polarity-preserving mutations to stochastic search: complement one internal wire, dualize its gate, and flip incident input/output signs. This preserves computed truth table while exploring lower-NOT representations. New executable search_signed_gauge awaits next run.
- New formal extension finite/LeastBudget.lean proves cleaning and least-circuit selection preserve total gate count as well as the non-NOT count; wrapper targets exact15binary from size≤19 and4NOT. First compile only found a namespace shorthand ambiguity (Vertex), fixed to Fin10; rerun in progress.

- LeastBudget.lean now CHECKED (exit0; empty full log). 74lines; SHA256 083f1a2955b21f4efab91c35ae084e6c24bca850f8768dd5dc8b5739ed54606f. Root notified immediately. Strip its scratch-only first import line when appending declarations to the proof file.
- Second signed15+covered run: UNKNOWN at300.49seconds,135001conflicts,173MBpeak. No candidate or impossibility result.
- Structural agent reviewed residual-twin class constraints as sound under the clean Least15binary normalization, canonical shared-NOT placement, collapsedfanout≤2, and the nonempty first-input-class theorem. Added optional --twins with10bit first-input masks, independent classes, and twin equality only when both residual neighborhoods are nonempty. Ready for next run.

- 2026-11-25T14:31:53.192076+00:00: twins SAT and gauge annealer stopped on coordinator request to prioritize ABC build and integrated Lean on four CPU cores. Their logs explicitly mark resource scheduling; no UNSAT result. No solver or annealer remains active for this agent.
