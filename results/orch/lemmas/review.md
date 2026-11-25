# Independent semantics and submission review

Reviewed 2026-11-25 against upstream HEAD 9fb616c3. No desk calls or git changes performed by this reviewer.

## Exact semantics of L-meta-2592

The statement quantifies over every `Circuit`, assumes `FanInTwo`, at most 19 gates, and at least one gate whose operation is `not`, then rules out computing the displayed Petersen edge function on all 1024 inputs.

Sources: `lean/PEqualNP/Defs/CircuitLowerBounds.lean`, `lean/PEqualNP/Defs/MetaComplexity.lean`, and the saved desk answer.

- `FanInTwo` restricts gate operations to AND, OR, NOT and the input-list length to at most two. It does not impose well-formed wire indices, exactly two inputs for binary gates, exactly one input for NOT, last-gate output, nonredundancy, or reachability from the output.
- Gates run as a left fold, appending one Boolean to the input list. Gate j produces wire 10+j for these inputs. Out-of-bounds reads, including forward/self references, yield false; they do not create cycles.
- A NOT gate reads its first operand only. A second operand is ignored. Empty NOT yields true.
- Empty AND yields true; empty OR yields false. Unary AND/OR copy their operand. Repeated operands are permitted.
- The output can name an input, any earlier gate, or a nonexistent wire; nonexistent output is false. Gates after the output and unused gates still count toward size.
- The assumed NOT can be completely unused. Any argument about an essential negation must first justify normalization/deletion and the resulting strict size decrease.
- Fin 10 inputs are converted by `List.ofFn` in index order. A search limited to legal gates must establish normalization before using UNSAT to prove this statement. A concrete legal counterexample needs no normalization argument.
- All 1024 assignments, rather than only zero/singleton/edge assignments, are required for equality. NOT circuits can agree on weight-at-most-two inputs while disagreeing on larger supports.

Independent finite enumeration of the displayed graph: 10 vertices, 15 distinct edges, degree 3 everywhere, triangle-free; 76 independent sets and 948 satisfying assignments; independence number 4 and minimum vertex-cover size 6. This confirms the graph interpretation but is not a Lean proof of a circuit bound. No semantic loophole or counterexample was established.

## Updated repository rules

`CONTRIBUTING.md` now requires all helper declarations in `namespace PEqualNP.Outside.L_meta_2592` (or its `_aux` variant/subnamespace), with named `end` at column 0. The one fully qualified main theorem is last and outside this block. Avoid helper instances and global simp lemmas.

The current local checker is check-lean 4 and supports check/refute/reduce. Its acceptance checks kernel verification, the exact statement, and allowed axioms, but does not replace the separate import/plain-text/namespace guard.

Full guard invocation for the intended proof:

```text
node .github/scripts/outside-guard.mjs imports lean/PEqualNP/Outside/L_meta_2592.lean /tmp/oec/pequalnp-pilot-99/imports.json lean/PEqualNP/Outside/L_meta_2592.lean check
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_2592.lean /tmp/oec/pequalnp-pilot-99/statement.txt check
```

Use actual discovered paths if the saved allowed-imports file has another name. The allowed project imports consist only of `PEqualNP.Defs`; importing existing outside reductions is not allowed for this gap.

## Refutations and reductions

The local checker can judge a negation with kind `refute`, but the public gap guard rejects `refute` for a prove row. A locally checked counterexample must be preserved immediately as requested by the owner; public acceptance additionally needs the appropriate posted refutation twin/kind. Do not describe a local refute verdict as public intake acceptance.

Reductions are supported by the current guard. An `R_meta_2592_k.lean` file must be judged with explicit kind `reduce`; k is 1..999 without leading zero. The final conclusion must be the exact posted statement, with 2..4 independent, distinct, smaller closed propositions as hypotheses. The file contains only its one top-level fully qualified theorem; no helper declarations or namespace. No text/meta types, statement-as-subterm, decidably false hypothesis, or hypothesis printing above 2000 characters.

The desk answer reports `reductions_live: 3`, already the maximum stated by the owner. Three reductions are in upstream: `R_meta_2592_271`, `R_meta_2592_318`, `R_meta_2592_408`. A fourth reduction should not be presumed eligible merely because the row has `reductions: true`.

## Before partial pushes and final PR

For a partial checkpoint, independently inspect the exact staged diff, ensure no forbidden tokens or credentials, make the selected Lean component compile, record its actual scope, and push only the designated branch to origin. Do not claim the posted theorem has been checked if only a helper was checked. A partial file lacking its final theorem may appropriately fail the final submission guard; distinguish this from Lean compilation.

Before final PR, run the complete guard and checker, and verify the diff against upstream has exactly one added ordinary UTF-8 Lean file, at most 512 KiB and mode 100644. No changed existing files, no orchestration notes, no logs, and no configuration changes may remain in the PR diff. Preserve notes/logs in earlier branch history or other owner-approved checkpoints, then restore their absence in the final tree without losing the recorded history. Re-review the final tree after cleanup.

Scan raw Lean text for forbidden words even inside comments: `_root_`, quotation marks, new axioms, sorry, native/bv_decide, commands, unsupported attributes/options, and later occurrences of the word import. The explicit guard performs this more comprehensively than a few manual searches.

Keep imports first, the only project import authorized, namespaces proper, and the main theorem exact. Renew immediately before long builds/checks and submission; parent alone controls the lease. Include sub-agent/timing measurements and honest build/checker status in the final report and PR body.
