# Status review: L-meta-2592

Read-only source review, 2026-11-25, upstream commit 16cd526b.

## Rules and reduction capacity

- Assigned goal: no fan-in-two circuit of at most 19 gates containing a NOT computes the 10-input Petersen edge function.
- Allowed project import: `PEqualNP.Defs` only; Mathlib imports also allowed.
- Desk reports `reductions_live: 3`; join.txt caps live reductions at three per step. A fourth reduction is not currently available.
- Updated CONTRIBUTING requires helper declarations inside the assigned module namespace (or `_aux` namespace), then the fully qualified theorem last at top level.
- No forbidden text, including `_root_` and quotes, may occur even in comments. The usual four local limit options and simp attributes are the only exceptions.

## Existing reductions

1. `R_meta_2592_408`: normalize invalid reads, extra NOT operands, and output trimming; then lower-bound normalized legal circuits. The normalized circuit may lose all NOT gates only when its size strictly decreases.
2. `R_meta_2592_271`: prove the binary gate floor `15 + notCount C ≤ C.size`; then rule out one through four NOT gates at total cost at most 19.
3. `R_meta_2592_318`: cut the circuit at its last NOT into arbitrary prefix `P` and monotone suffix `Q`; rule out the separator representation when `P.size + Q.size ≤ 18`.

The last-NOT cut appears structurally routine: choose `P.output` to be the NOT operand, or an invalid wire for empty input, and let `Q` be the suffix. The separator bound retains nearly all mathematical difficulty.

Parent `R_meta_651_7` is exactly the monotone / has-NOT split; its second hypothesis is our assigned goal. `R_meta_651_1` contains usable first-gate symmetry reduction code, with two explicit Petersen automorphism generators and a finite orbit certificate. `R_meta_651_2` contains final-gate trimming and wire/AND/OR case analysis.

## Reusable checked source machinery

- `L_meta_2681.lean`, 3407 lines: internal theorem `petersen_binary_lower` (lines 3127–3146) proves that an arbitrary fan-in-two circuit computing the nine-input Petersen-minus-vertex edge function has **at least 13 non-NOT gates**. This is stronger than its exported theorem needs.
  - General minimal-circuit normalization preserves a non-NOT budget.
  - Generic `BranchGroupsLean.roots_required` translates first branch group geometry into a minimum number of branch wires.
  - `least_petersen_five_branches` (3082–3116) uses a finite graph grouping certificate to require five branches.
  - `branching_budget` then gives `9 - 1 + 5 = 13` binary gates.
  - The full Petersen graph version might prove the binary floor of 15 needed by reduction 271. It does not settle the low-NOT cases alone.
- `L_meta_2679.lean`, 6868 lines: the same nine-input function cannot be computed from original inputs plus a precomputed `x0 || x4`, followed by a monotone prefix, a NOT, and arbitrary suffix, when prefix-plus-suffix size is at most 13. A large signed-circuit certificate proves the lower bound. Generic source components include `CoThetaFreeCore`, circuit-to-trace compilation, and finite restriction/rank certificates.
- `L_meta_2683.lean`, about 6000 lines: rules out a signed nine-input circuit with at most 14 total binary gates plus at most three marked negatable wire locations (input 0 and a constant are additionally free). Potentially useful after a Petersen variable restriction with sufficient gate savings.
- `L_meta_2677.lean`: normalizes every wire/output index to at most 24 without changing the circuit on sufficiently short input lists, preserving gate count and FanInTwo/Monotone2.
- `L_meta_2642.lean`: iterated semantic gate deletion under a two-variable false restriction, preserving fan-in and recording an exact size decrease.

These sources can be copied and renamed into the assigned namespace, but cannot be imported under the assigned import allowance. Large copies must still fit 512 KiB and the checker resource limit.

## Current conclusion

No direct checked proof of the full target was located. The best mathematically meaningful decomposition currently visible is binary-floor plus low-NOT analysis. Restriction arguments can reuse substantial existing machinery, but must establish enough actual gate savings; a bare NOT cut does not yield the desired size contradiction.

## Independent early-partial review

Reviewed `results/orch/lemmas/Semantic.lean`: 3254 lines, 146636 bytes, SHA256 `b0c3772354ce38b57066f1a7cdd237eef9b8d01d2dd4e502a3bc686caed01d68`.

Verdict: source safety and logical scope PASS **as a partial**, pending Lean compilation. This is not a full proof of L-meta-2592 and is not ready for a proof PR.

- Compared with `L_meta_4725.lean` after namespace substitution: all copied helpers are unchanged. Source is committed by `6cfaa2633a7edfd9699b8598c90aba2abb5ed460` (PR #9152).
- New `five_not_excluded` correctly combines binary floor 15, the identity `nonNotCount + notCount = size`, total size at most 19, and NOT count at least 5.
- New positivity lemma obtains a filtered-list member from the explicit NOT witness.
- New `remaining_not_count` correctly restricts any hypothetical target circuit to 1–4 NOT gates.
- Repository `checkPlain` and `checkImports` both PASS. Imports are Mathlib.Tactic, Mathlib.Combinatorics.SimpleGraph.Basic, and PEqualNP.Defs.
- Namespace guard reports only the expected absent final top-level theorem `PEqualNP.Outside.L_meta_2592`; all helpers are in the assigned namespace.
- No axioms, admissions, native computation bypasses, forbidden text, string literals, or improper attributes/options found. The file is plain and nonexecutable.
- Compilation intentionally not run before cache readiness. No checker acceptance claimed.

## Independent CutLast partial review

Reviewed `results/orch/lemmas/CutLast.lean`: 87 lines, 3729 bytes, SHA256 `50da600b8a283b7ffcaa1f0ef45ace3f75d9dac44924455929cdbd5cf6ebcab1`.

Verdict: PASS as a generic decomposition partial, pending compilation evidence. It does not prove the Petersen lower bound.

- Splits at the final NOT, so the suffix has only AND/OR gates and remains fan-in two.
- Prefix and suffix sizes sum to the original size minus exactly one gate.
- Prefix output is the NOT gate's first operand, preserving normal and invalid-read behavior. Empty NOT input instead selects `n + pre.length`, exactly one past the prefix wire list, which reads false; its negation is true as required by the gate semantics.
- The suffix receives the complete original prefix wire list followed by the NOT value, preserving all original wire indices and the original output index. Ignored extra NOT operands do not affect the argument.
- Allowed imports only; all declarations are in the assigned namespace; no forbidden constructs found.
- Official plain/import guards report only that this lemma-only partial contains no theorem. Namespace guard reports only the absent final target theorem. Those are expected partial-file limitations, not a claim of full-proof format compliance.

## Stronger binary floor and extra-input embedding

Independently verified `L_meta_5236.lean`'s internal proof is stronger than its exported theorem:

- `Extended.realize` (line 4456) requires only FanInTwo and correct computation on `List.ofFn x ++ [x 0 || x 2]`. It gives a signed live trace with binary count at most the original non-NOT gate count.
- `atLeastSixteen` (line 4504) proves every such trace has at least 16 binary gates.
- The exported theorem's ReadsBack, output validity, and NOT upper bound are unused in deriving this floor.
- Consequently an ordinary circuit also has at least 16 non-NOT gates: insert an unused extra input and shift original gate/output wire indices at or above the original input length.
- This strengthens the partial exclusion to **four or more NOT gates**, leaving only counts 1–3.
- L5236 is 285226 bytes. Copying its helpers plus the 3522-byte generic embedding stays below 512 KiB and can replace the earlier 146636-byte binary-floor source.

Implemented and compiled `results/orch/lemmas/EmbedExtra.lean` (85 lines, 3522 bytes, SHA256 `1f03ccc3b52b2ef37687ba0519b2c9966704d4eb0eae908da5d3c201c4e97bc7`). Lean exit 0; complete stdout/stderr logs are empty. Only `PEqualNP.Defs` is imported.

Its `extraCircuit n` shifts indices at or above n upward by one. `extra_eval_ofFn` preserves the evaluated function for any appended bit, including malformed/out-of-range wire reads. `extra_fan`, `extra_size`, and `extra_not_count` preserve the required counts and gate constraints.

## Counterexample encoder review

Read-only review of `counterexample.cpp` and `counterexample_aig.cpp`: ordinary AND/OR/NOT clauses, one-hot source selection, both directions of exact-k NOT cardinality, AIG XOR clauses, output phase, and phase-switching NOT optimization are consistent. No sign or cardinality defect found.

These are witness searches only. Sorted-source mode and positiveMask impose additional search restrictions. An ordinary-model witness uses virtual false source 10 and gate sources 11+g, which must be translated to the Lean model; the AIG emitter already uses explicit Lean-like indices with invalid wire 1000000 representing false. Every discovered witness still requires independent 1024-row evaluation and Lean checking.

## SignedRestriction and Combinatorial partial audits

`SignedRestriction.lean`: PASS as partial, SHA256 `bc8917ac2c49733e26c9291397ea2d8cee8f5352beb320fe27303030324aeaf5`, 1784 lines, 90415 bytes. Exact source comparison against the generic prefix of L5971 found no edits except namespace rename, removal of private qualifiers, and replacing the literal input dimension 9 by 10. Its conversion theorem preserves arbitrary computation within size minus NOT-count binary gates. Its two-read restriction theorem saves at least two binary gates for either Boolean restriction. The single-fanout-first-gate theorem correctly asserts independence only after the other input is fixed to the blocking phase, under explicit no-other-read and no-direct-output assumptions. Root reports compilation exit 0. Two structures and one local instance remain: partial/manual-format status, not a claim of PR readiness. Automated guards report only the missing final theorem.

`Combinatorial.lean`: PASS as partial, SHA256 `74cf2dc383821ca0280b85cce138044567571665cd7116f293cd28edd609163c`, 78 lines, 3020 bytes. Kernel-checked finite witnesses isolate each of any two distinct input coordinates. `noPairFactor` correctly obtains three distinct Boolean outputs from a hypothetical factorization, a contradiction. `cofactorKeepsOtherInput` states that fixing either value of one input leaves any other input essential; this matches the contradiction needed against `single_fanout_first_gate`. Sole Defs import, helpers in assigned auxiliary namespace, no forbidden constructs. Full-file compilation confirmation belongs to the owning agent.

The intended 17-binary-gate route is mathematically consistent: first-gate input must be read again by the cofactor-essentiality result; restricting it removes at least two binary gates; the nine-input restricted graph has the existing binary lower bound 15. The remaining interface is conversion from the restricted signed circuit into the nine-input certificate semantics.

## Plain-format and stronger-floor delta audits

- `SignedRestrictionPlain.lean`: PASS as partial, 1785 lines, 90964 bytes, SHA256 `3faf2c688af602c3057a1c3d3850d28d74e58b6dc2eb9fd205cbce659f87576e`. Products and accessor abbreviations preserve the old structure field order. Explicit GateOp deciders preserve the removed local instance's meaning. Added unfolding steps only expose those accessors. Restored doc headings were caught and changed back to plain comments. Independent scan finds zero options, attributes, instance declarations, or custom data types; no forbidden text. Compilation reported successful by owner.
- `Combinatorial.lean` automorphism extension: PASS, 102 lines, 3823 bytes, SHA256 `21722978b382c7d1d07cd26b810fa990aa89e2b6586d1e64db5c860fb55b381f`. Independently parsed and checked all ten permutation rows: each is bijective on 0–9, sends 0 to the designated vertex, and preserves the Petersen edge set. This matches the compiled finite certificates.
- `BinarySixteen.lean`: PASS as partial, compilation confirmation pending at review time. 4657 lines, 288201 bytes, SHA256 `f01350812f5cc03411dc9d2c36d113fc3453e4fe6767b9576f5b45d2ce6d32f1`. Copied L5236 helper prefix is byte-identical after namespace substitution. The embedding matches the compiled EmbedExtra helper except fully qualified FanInTwo. New binary floor and four-NOT exclusion correctly combine the extracted trace bound and gate-count identity. Official plain/import guards pass; namespace guard reports only the missing full-target theorem. All 103 options are permitted limits, in the required local form directly before their declarations; no attributes, instance declarations, custom data types, or comment headings occur.

## Reach and first-gate integration audits

- `ReachBridge.lean`: PASS as a compiled partial fragment, 84 lines, 3775 bytes, SHA256 `273c2621fb4aa637fc1a57d28710f1cb7bbffb23c6382d2a856b997c2384962b`. Verified the small test bundle supplies twelve actual definitions/theorems matching L5236, with no axioms. The snoc induction adds one AND operation per U2 gate and correctly supplies old wires, new outputs, constants, invalid reads, and free complements. No hypothesis beyond supplying the ten input functions is added. Old L5236 namespace references must be renamed into the assigned module during final integration.
- `FirstGatePlain.lean`: PASS as a compiled partial, 1968 lines, 97960 bytes, SHA256 `3f92659d0d405ec744207e49e6e268dea588e1ab90c080c107b4337b97302f82`. Exact reviewed plain prefix plus the previously reviewed 102-line Combinatorial version and first-gate suffix. The suffix excludes a direct input output, proves at least one gate, uses cofactor essentiality to force a second reader of a first-gate input, and applies the two-read restriction bound. No hidden assumptions. Four permitted local options only; no attributes, instance declarations, or new data types.
- Later `Combinatorial.lean` inverse-map delta: PASS, 129 lines, 4768 bytes, SHA256 `99a121d1581840f39eabc4de32490e15a079c967470fd75d1d482444a1e9e590`. Independently verified all ten inverse tables satisfy the left-inverse equation and send the designated vertex to zero. Inverse function invariance follows correctly from forward invariance and that equation. Owner reports compilation exit 0.

## Cofactor and 17-gate integration audits

- `CofactorFloor.lean`: PASS as a compiled conditional component, 38 lines, SHA256 `15f8ec44f61cab4f8cd08bb2ad838fa6722b997ae117a9472acd113067944dde`. Its explicit parameters supply a base row model with input zero fixed false and a 15-gate lower bound. Composing assignments with the inverse automorphism fixes the designated vertex false and preserves the target function, so the generic U2-to-Reach bridge proves every false cofactor needs at least 15 binary gates. The test harness contains the exact reviewed Reach bridge, combinatorial inverse maps, and consumer, with no axioms or admissions.
- `ReadBudget.lean`: PASS as a compiled conditional component, 2212 lines, SHA256 `43b2a4982158384b3a514645634d6eebd86a11249dce5685182541fa9ea05c25`. It is exactly FirstGateCases plus the 74-line ReadBudget suffix. The suffix embeds the distinct gates reading an input into the restriction's eliminated set, proving reader count plus 15 is at most circuit size. Subsequent reader and polarity bounds follow correctly. The ZeroFloor hypothesis remains explicit; this component does not independently claim it.
- `BinarySeventeen.lean`: independent source audit PASS before full build; 6869 lines, 396420 bytes, SHA256 `64128ee9422354ac49a8c7b63d535e67f96bb3ea4e45134bdd24447df6922f5c`. All seven previously reviewed blocks occur exactly after removing duplicate imports and renaming old L5236 references. The concrete cofactor model supplies original pins projected to the nine-input row domain, verifies input zero is false, identifies the target through the checked row certificate, and applies nineFloor. The final suffix then combines two saved gates and the cofactor floor with the signed conversion budget to obtain `17 + notCount C ≤ C.size`, excluding three or more NOT gates. No full target theorem is asserted. Official plain/import guards pass; namespace guard reports only its missing final target theorem. All 107 options are permitted local limits directly before declarations; no new types, instances, or attributes are present. Full build confirmation was still pending at this review.

The later one-line proof-local DecidableEq fix in BinarySeventeen is also audited: 6870 lines, 396474 bytes, SHA256 `15b60a43cd2acaf95c1a2b90783b4ee0c69e07e0c4300de918dd120758526321`. It changes no mathematical assumption and introduces no instance declaration.

## Duplicate, general reader, and promotion audits

All three frozen components PASS as compiled conditional partials; their six build output/error logs are empty. Their explicit ZeroFloor hypothesis remains an assumption of these components, to be supplied by the separately established cofactor lower bound.

- `Duplicate.lean`, 2269 lines, 111146 bytes, SHA256 `c665b60d97bb3b6139fbc179bb1e56c4b43f32c83a2c90897b9a7cb3c8deaed4`: exactly ReadBudget plus DuplicateSuffix. A later gate computing the first gate's function is deletable, contradicting minimality. Established all-negative phase facts then make any later gate reading both first sources such a duplicate, even with their order exchanged. Future readers of the two sources must therefore be distinct.
- `ReadBudgetGeneral.lean`, 2248 lines, 109871 bytes, SHA256 `56687177f06f9a87f1dcf5e9ad9a17ba2fa52ac6013e88b9c0cf100f80a6990d`: exactly ReadBudget plus ReadBudgetGeneralSuffix. Restriction correctness and the eliminated-set inclusion only need well-formedness and correct computation, so removing the previous minimality assumption is valid.
- `Promotion.lean`, 2285 lines, 111476 bytes, SHA256 `106d2abea95bbea7e2eb9ff54f4eaea6d76ac83996b0bb56d76770b3f0046ad1`: exactly ReadBudgetGeneral plus PromotionSuffix. A separately chosen minimum and its two-gate restriction yield a universal signed binary lower bound of 17. Therefore a computing signed circuit with at most 17 gates is itself minimum; the minimum-only phase theorem legitimately applies. All budgets count signed binary gates, with no confusion with ordinary total size.

All declarations remain in assigned namespaces; only four permitted local limit options occur; no data types, instance declarations, or attributes were introduced. Automated guards report only the expected absence of the final target theorem.

## Further compiled partials and search cuts

- `MixedC6.lean`: PASS as a compiled partial, 146 lines, 5508 bytes, SHA256 `c88b64521bf9655a5f6ed73ccedc6890570a06311622d05dc9371630f5f79a1d`. Exactly the 129-line Combinatorial component plus its 17-line suffix. Independently checked all ten neighbor masks against the fifteen Petersen edges. Its checked statement equates center-true and center-false assignments with all neighbors false; it does not itself establish a C6 lower bound.
- `OneNotEndpoints.lean`: PASS as a compiled partial, 123 lines, 4355 bytes, SHA256 `3fc0e008ad4801243ba512a2868e981899ddee77dd58a9aa9d185b34389d92a8`. Generic endpoint arguments are correct. In masked_or_new, a fresh element of S outside R forces H to be contained in R via a two-element test, after which singleton tests give S=W∪R. The no-triple result correctly applies the conditional support-cardinality hypotheses. No general one-NOT lower bound is claimed.
- `BinarySeventeenCasesSuffix.lean`: static/interface audit PASS, 37 lines, SHA256 `a33e45d73a144312cc38f3cf50cdade01aef6f38cc6f8cab86b5b42dd260cfb4`. The lightweight test proves the same argument with an explicit ZeroFloor parameter and contains no axioms. The intended actual instantiation forces total size 19 and signed size 17 when the NOT count is exactly two, then obtains signed minimality. Actual suffix integration still needs its own build.
- The full BinarySeventeen component at SHA256 `15b60a43cd2acaf95c1a2b90783b4ee0c69e07e0c4300de918dd120758526321` completed compilation with exit 0 at 14:40:26 UTC, as reported by its owner. Its previously pending integrated-build limitation is resolved.

Reviewed additional SAT propagation cuts: selected-source constant-status muxes correctly swap false/true under negation; AND propagation and counted constant-operand eliminations are sound; one-sided sequential threshold clauses give a correct at-most encoding; NOT-orientation budget clauses match parity. Further simplifications may be missed but are not overcounted. These cuts depend on the supplied residual lower bounds and remain witness-search machinery, not formal UNSAT certificates.
