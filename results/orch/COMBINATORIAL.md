# Combinatorial route

2026-11-25: Root assigned L-meta-2592.

Checked-source findings:
- `L_meta_4725.lean` proves `15 + notCount C ≤ C.size` for arbitrary fan-in-two Petersen circuits. Its branch-group counting argument is 3224 lines and imports only allowed project definitions and Mathlib. This closes the case of at least five NOT gates under the budget 19.
- `L_meta_5236.lean` proves a 16-binary-gate floor when `x0 OR x2` is supplied freely; consequently it excludes an 18-gate suffix with at least three NOT gates.
- The exact small-NOT remainder is L-meta-4727, still represented by reductions R_meta_4727_1, R_meta_4727_17, and R_meta_4727_53.
- L-meta-2592 already has three reductions in the repository: 271 (binary floor plus 1..4 NOT), 408 (normalization plus legal bound), and 318 (last-NOT cut plus separator).

Experiment `results/orch/lemmas/Combinatorial.lean` adapts L_meta_4725 into our namespace and derives `notCount C ≤ 4` for any hypothetical counterexample. It is not yet compiled: root is arranging the Lean toolchain.

Mathematical obstruction: monotonicity of a single-output circuit with one NOT does not immediately justify replacing the NOT by a constant. The familiar one-NOT decomposition is a selector of three monotone functions and provides no size-preserving elimination automatically.

14:20 UTC update:
- Stronger direct source `L_meta_6581.lean` proves at least 16 non-NOT gates for full Petersen. `CombinatorialStrong.lean` adapts its certificate and derives the budget-19 impossibility when at least 4 NOTs occur. First build found only an orphan `open ... in` wrapper; corrected rebuild running, with `.olean` output.
- New mathematical route gives 17 binary gates: expose first binary step in the existing `Extended.Live` relation. Each operand must remain live after the step, because fixing the other operand to the gate's canalizing value cannot remove its dependence from Petersen. A finite witness table proves this retention fact. Set one retained operand to false, use a Petersen automorphism to obtain the nine-input graph, and apply the checked 15-gate signed lower bound. The retained zero input charges one additional gate in the suffix, plus the first gate already removed.
- If the first normalized gate is AND or a signed difference with a positive annihilating operand, both that retained operand and the fresh first gate become constant. The suffix mass then charges two gates, giving 18 binary gates overall. The first pure OR case gives only 17 by this argument.
- `Geometry.lean` compiles: all 10 automorphism embeddings preserve the target cofactor and map every input into an existing nine-input variable or zero; selected input becomes zero. Exact Python checks agree.
- `CombinatorialCore.lean` compiles: generic machinery subset of L6581, cached locally for incremental development. `SeventeenCoreDev.lean` tests the new 17/18 arguments against an explicit premise asserting the existing nine-input floor, without axioms or placeholders.
- `RetentionWitness.lean` was independently prepared and compiled by lean_setup; its new declarations are copied into the addon `Seventeen.lean`.

14:23 UTC: `SeventeenCoreDev.lean` compiled with exit 0; the conditional 17-binary lower bound and first-AND 18-binary lower bound are now checked Lean implications from the nine-input floor. Independent reviewer passed the source SHA256 `12734a01edf7f8f99446fdb4accd07dae6bd23e3022f08a009f23f4ff498affb`. The source imports only the locally cached generic Core module; final source integration must inline this module and use the actual `nineFloor` certificate from Strong. New lemmas are in namespace `PEqualNP.Outside.L_meta_2592_aux.Seventeen`.

14:36 UTC: `PetersenPartial.lean` compiled with exit 0 as a self-contained file importing only `PEqualNP.Defs` (4889 lines). It integrates the independently reviewed corrected `CombinatorialStrong.lean` and `Seventeen.lean`, including the actual nine-input signed lower-bound certificate. `binaryFloorSeventeen` proves `17 + notCount C ≤ C.size` for every legal circuit computing the exact Petersen function, so `partial_only_three` excludes all budget-19 candidates with at least three NOT gates. `Seventeen.after_first_nonOr_bound` strengthens the bound to 18 binary gates when the first normalized binary gate is not OR. The full posted statement remains unresolved for one or two NOT gates. Axiom audits of these three results report only `propext`, `Classical.choice`, and `Quot.sound`. Complete build logs are `/tmp/oec/pequalnp-pilot-111/petersen-partial.stdout` and `.stderr`; the latter is empty. Self-contained source frozen for independent review and immediate research checkpoint push.

The next companion `TightBudget.lean` makes the remaining two-NOT case precise: a counterexample must use exactly 19 physical gates, exactly two NOTs, exactly 17 non-NOTs, and extract to a 17-step signed semantic derivation whose first normalized gate is OR with both input operands retained. This is a semantic normalization statement, not a claim that the first physical gate is necessarily OR.
