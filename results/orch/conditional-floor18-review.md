Conditional signed first-gate lower bound

2026-11-25T14:37:55.348172+00:00

Source: results/orch/lemmas/Floor18.lean. Development import: Floor17Proof.

The first signed operation is one of AND, OR, a AND NOT b, NOT a AND b. For each non-OR operation, positiveOperand chooses a for AND/a AND NOT b and b for NOT a AND b. Setting this operand tofalse makes both its retained raw input and the first operation output constantfalse. The projected live front therefore has constant mass at least2. The existing signed deleted-Petersen lower bound15 and projected_bound force at least17 operations in the remaining suffix, hence at least18 including the first operation. The final corollary forces a full live derivation of at most17 operations to start withOR.

Independent reviewer structural_proof reports mathematical/source PASS, pending compilation: the mass charges count two real constant entries, not duplicate nonconstant entries; positive-operand orientation and deleted15 application are correct. No new axioms, finite-case tables, or heavy decision computations are introduced. Final submission must concatenate these helpers and use only permitted imports.

Compiled 2026-11-25T14:44:43.856993+00:00 with Lean v4.36.0 against checked Floor17Proof.olean, exit0. Source85lines/3790bytes, SHA-256 3abc87e4c8943a9ca3e26f1aa89c0bc64b25f11ac2c47ad5ee0a7c636a4eaa12. Complete successful logs preserved in results/orch/validation/floor18-build2.out and .err. Initial command failed before elaboration because a scratch source requires Lean -R pointing to its package directory; the corrected invocation used the documented -R option. No source fixes were needed.
