# L-meta-1884 encoding and trace route

The lease was withdrawn at17:03:59UTC; this route is stopped. No full proof or counterexample is claimed.

## Exact prefix-NOT bridge

Frozen source: `/tmp/oec/pequalnp-pilot-99/gap1884/sat_encoding/PrefixNot.lean`, 60 lines, 2,333 bytes, SHA256 `0c173a0b18ff8dbb1518686bba31d49a4b2f05bcbfb783ebe674a88930ecbb98`. Compile/export exited 0; successful complete logs `prefix-not-02.stdout/.stderr` are empty. Cached `PrefixNot.olean` is available beside the source. The first attempt failed only because the identifier `prefix` is a Lean keyword; the definition is now `addNotZero`.

Namespace `PEqualNP.Outside.L_meta_1884.PrefixNot`. `addNotZero C` prepends a NOT gate reading raw input 0 and retains every original gate and the output index. Running it on the ten raw inputs creates wire 10 with the free negated literal. All original eleven-input gate indices therefore remain unchanged. `wires_prefix` and `eval_prefix` prove exact identities for arbitrary input lists, including all invalid/forward-read, nullary, unary, duplicate-input, and arbitrary-output behavior. `eval_prefix_ofFn` specializes to the canonical ten raw inputs plus `!(x 0)`.

`size_prefix`, `notCount_prefix`, and `fan_prefix` prove the cost and legality facts. `transfer_not_floor` takes an explicitly supplied, independently proved ten-input binary floor and transfers the same floor to the free-literal model: the extra NOT increases both circuit size and NOT count by one. `at_most_one_internal_not` specializes a 17-binary floor to size at most 18. Lower_bound owns its actual Petersen application using the earlier checked `binary_floor17`; the bridge does not assume the requested L-meta-1884 conclusion.

## Planned finite model

The canonical model has eleven physical inputs, at most eighteen gates, and a row assignment whose first ten bits are arbitrary x and whose bit 10 is `!(x 0)`. The earlier arbitrary FanInTwo encoder can be reused with AND/OR/TRUE/NOT operations, invalid-read false sentinels, and arbitrary output, omitting the old has-NOT clause. No actual-C connectivity, output-last, or first-gate symmetry restriction is justified merely by the trace lemmas. Any UNSAT certificate must correspond to a formula whose completeness has been proved. A SAT model on selected rows must be checked against all 1,024 true input assignments.

## Saturated signed trace

Frozen `TightTrace.lean` is 118 lines, SHA256 `d53be94f9c9a3f6d44b4e077ac1947a4bb71aa0b1406aa5ee493c011d4dc9d64`; successful `tight-trace-02.stdout/.stderr` are empty and an olean was exported. The independent reviewer passed the proof. This prototype uses cached `Bound17` and `PrefixNot` dependencies; the final single-file proof must inline those checked sources.

`canonical_one_not_trace` proves that a canonical correct circuit of size at most 18 with exactly one internal NOT produces an `Extended.Live` trace with exactly 17 effective binary operations. `canonical_one_not_first_or` uses the earlier checked signed-case bounds to show that the trace begins with an OR of distinct initial pins and retains both pins for its 16-step suffix. This is a statement about the extracted normalized trace. It does not justify forcing the first actual gate of a circuit, or a SAT model, to be an OR.

## Zero-NOT normalized SAT route

The earlier checked generic normalized encoding theorem accepts arbitrary input count and arbitrary selected truth rows. It therefore applies to eleven physical inputs with only the correlated assignments `(x, !x[0])`. The current formula uses 38 rows: the minimal true and maximal false assignments in the two nine-variable cofactors. Completeness for an UNSAT argument needs only that these rows are legal correlated inputs; no assumption about all 2,048 physical assignments is made. A SAT model still needs independent validation on all 1,024 legal correlated assignments.

`MonoEncoding.lean` is being checked as a standalone adaptation of the already reviewed 1,461-line generic normalization baseline, plus a finite row bridge and the elementary implication from FanInTwo plus zero NOT count to Monotone2. Its final theorem is conditional on UNSAT of the exact `enc2 11 18 rowValue freeRows`; no UNSAT certificate currently exists. The companion `DumpMonoEncoding.lean` is a diagnostic executable, not proof source, used to compare the formula byte-for-byte with the Python generator.

## Checked finite input and profile bridges

`MonoInput.lean` compiled/exported with exit 0, SHA256 `4029b96a6d850d1e81e13186b30088f124b5dc8963ceea7e7b3aafd4d2f409e3`, 47 lines, 1,962 bytes. Successful complete `mono-input-03.stdout/.stderr` are empty. This independently checked module proves all 38 row bounds and exact eleven-input list correlations, the zero-NOT implication to Monotone2, and transfer of canonical correctness to those rows. The standalone full `MonoEncoding.lean` baseline was checked through its generic normalization declarations, then failed at the newly added helper because the classical equality decider needed to be supplied and `notCount` unfolded explicitly. Those small issues are fixed in the checked isolated module and the portable source; portable rechecking waits for other large kernel jobs to finish. No complete portable-source pass is claimed yet.

`ProfileEncoding.lean` compiled/exported with exit 0, SHA256 `ebb5e98a8f9df4de5af8b75688711ebbe5386c9077f59c01d0341eac3dd7c645`, 46 lines, 1,627 bytes. Successful complete `profile-encoding-02.stdout/.stderr` are empty. For any three-element finite universe and any six nonempty subsets, it constructs six nonempty three-bit profiles, preserving every individual cardinality and every pairwise subset relation. This is a generic bridge requested by the structural I4 route; it does not assert that its hypotheses hold for an arbitrary circuit.

The diagnostic `DumpMonoEncoding.lean` ran successfully against the checked `MonoInput.olean` and project definitions. Its SHA256 is `4d7844c0d66c1bf50c88a1f3c716fe9e6a8bffb98ec664719786028c7e1ea9fd`. Complete emitted `mono18-lean.cnf` is byte-for-byte identical to counterexample's `mono18-enc2.cnf`: 5,952,884 bytes, 144,603 clauses, maximum variable 311,701, SHA256 `d70821d2b6c43b4a84fdda720013a11515d1d187ef8b89c97e61ba0d9eee49c4`. Complete comparison evidence is `mono-byte-comparison.stdout/.stderr`; the stderr is empty. The formula can be reproduced using the pinned Lean toolchain with `lean --run DumpMonoEncoding.lean`, adding the scratch module directory to LEAN_PATH after `lake env`. This executable and generated DIMACS are diagnostics, not admissible final proof declarations.

## Portable encoding completed

The corrected complete `MonoEncoding.lean` compiled and exported with exit 0. It is frozen at 1,523 lines, 71,089 bytes, SHA256 `4e4333e237ab7f7ebaf5a858f2d9cb95ef15b8fef2b674c77489e9428f1cf1d9`. It imports only Mathlib and PEqualNP.Defs and keeps all declarations inside the L-meta-1884 helper namespace. Complete successful `mono-encoding-02.stdout` is 83,164 bytes of baseline linter/deprecation warnings; stderr is empty. This supersedes the earlier portable-source pending status. The final theorem `canonical_zero_not_from_unsat` is explicitly conditional on UNSAT of `enc2 11 18 rowValue freeRows`; no actual UNSAT certificate has been obtained.

The proposed Nat-profile exhaustive alternative was not implemented or launched. The coordinator and reduction strategy found a short analytic route instead: duplicate-profile exclusion, singleton privacy, and counting the remaining subsets of a three-element universe. Reduction strategy owns that argument. The checked generic ProfileEncoding bridge remains available for it.

## Recommended definitions-only cache and replay

`MonoEncodingDefs.lean` passed with only `import PEqualNP.Defs`: 1,522 lines, 71,074 bytes, SHA256 `ba11917b16bb3e57fd2b79198c95a75cf1661fa53b9b63b6170d60da947a2b50`. Its only difference from frozen `MonoEncoding.lean` is deletion of the broad Mathlib import line; all proof bodies are byte-identical. This avoids loading the full Mathlib graph when other proof modules use the cached artifact. Complete successful `mono-encoding-defs-01.stdout/.stderr` are preserved (warnings only, empty stderr).

The generic LRAT replay block and an explicitly conditional zero-NOT application compiled in `MonoReplay.lean`, SHA256 `2867378ce24e62d511c5a8e7813062cfb9bf970325c0dfd22f681f6ae0beeeba`. The recommended cache variant `MonoReplayDefs.lean` changes only the cached import to MonoEncodingDefs, SHA256 `364711338b55db795291ae5ecb990dbf2e3cf31933adc49065421d6e8f460aba`; both have 479 lines and empty successful logs. The generic checker block is unchanged from the previously checked NormalizedReplay. A final submitted file must inline the cached dependency. The checkW acceptance equation remains an explicit hypothesis; these modules contain no actual refutation certificate.

`DumpMonoDefs.lean`, SHA256 `ed77750a0ad77539efeadd8df347a49c46bab0d2514159f1742c7dd07beeed1d`, directly uses the actual checked MonoEncodingDefs constants. It again emitted exactly the Python solver file, SHA256 `d70821d2b6c43b4a84fdda720013a11515d1d187ef8b89c97e61ba0d9eee49c4`; complete evidence is `mono-defs-byte-comparison.stdout/.stderr`. This is the preferred reproduction diagnostic.

## Stop signal

The counterexample agent reported `gap1884/STOP` at 17:03:59 UTC and stopped the normalized zero-NOT solver at 17:04:00 with SIGINT and no verdict. Its unfinished approximately 1.08 GB binary LRAT trace is not a certificate and was not packed. All this agent's Lean and diagnostic processes had already finished. All checked sources above remain frozen.

The coordinator requested a separate v4 of the broad exact-one-NOT encoder with unique selectors, NOT source equality, TRUE false-sentinel sources, and sorted commutative operands. Only the existing v3 source and the earlier generic encoding were inspected, and the local canonicalization plan was shared; no v4 source, Lean bridge, or new solver run was created before the stop signal. No claim about a v4 completeness theorem is made.
