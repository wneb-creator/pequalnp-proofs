# Independent checkpoint 05 review

Verdict: **PASS for preserving this partial checkpoint.** This is not a completed proof of L-meta-2592 and is not ready for a proof PR.

Reviewed file: `lean/PEqualNP/Outside/L_meta_2592.lean`

SHA256: `631fb68424d92b6ca6d3881292e4c37a2671001b32cda6af38ed7d820ad6cbe5`

Size: 245 lines, 8,933 bytes.

The actual working diff adds the 18-gate approximation inside the existing `PEqualNP.Outside.L_meta_2592` namespace and adds `petersenFunction_eq_ptFun`. The approximation block is byte-identical to the declaration/proof body of the independently reviewed `results/orch/lemmas/approximation.lean` (SHA256 `d3517b2d0b095ba1af784d5fb74abe72e218eda4d110696ff521167524e34f36`); only the surrounding namespace placement differs. No semantic change to the circuit, Boolean identity, evaluation lemma, or explicit mismatch was introduced by the merge.

The new equality lemma is exactly `(ptFun_eq x).symm`: the existing lemma expands `ptFun` to the same 15-edge Boolean expression used by `petersenFunction`. The repeated `open` line is harmless and does not change meaning.

Checks performed without a new Lean build:

- All 29 declaration names are unique within the file.
- The only import is the allowed `PEqualNP.Defs`, at the top.
- All helpers remain inside the file's own namespace.
- No `_root_`, double quotes, or attributes occur.
- The repository's `checkProofFile` guard reports only the two expected findings: no theorem exists, and the required fully qualified final theorem is absent. It reports no import, forbidden-text, option, or helper-namespace violation.
- `/tmp/oec/pequalnp-pilot-98/build-partial-05.log` contains `Build completed successfully (5149 jobs).` Root reports build exit 0.

The approximation is intentionally not exact: the previously reviewed four false-positive assignments remain. The file still has no final theorem proving the posted statement. The separate full checker ended in FAULT/137 according to root; no checker was rerun here, and this review makes no acceptance claim.
