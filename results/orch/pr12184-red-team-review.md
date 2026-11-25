# PR12184 independent red-team review

Reviewed 2026-11-25T04:46:15.898777+00:00 by status_review. Source: benoitrazet, [PR12184](https://github.com/brilliant-hq/pequalnp-proofs/pull/12184), commit `23cfcb8f020d4c1dfbf6b54a16284e8f1a932234`. Preserve this attribution for any adaptation.

Verdict: static format/trust review PASS; no source-level blocker found. This is conditional on a complete pinned-toolchain build and the authoritative checker. Neither has been claimed to pass by this review. The observed upstream bot verdict is FAULT (checker exit124), a runtime failure rather than acceptance.

- Source SHA256: `1c31cfa39cea4936c1e20b0cfa430ec063d9f8cbfa5d443d9916947958146872`. Size516536bytes,5222lines,7752bytes below524288limit. UTF-8/plaintext checks pass.
- Final theorem is byte-for-byte the posted L-meta-670 statement after trimming surrounding whitespace. It is last, fully named, outside the closed owned Projection namespace. No altered size, graph edge, quantifier, or hypothesis.
- Only `import PEqualNP.Defs`; no extra import, no critical-name shadowing, no custom datatype, no instance, no attributes. No string literal, forbidden token, new axiom declaration, admitted proof, native evaluator, or compile-time extension. Only the permitted recursion/heartbeat limits occur.
- The current base branch's actual `checkProofFile` and `checkFileKind` exports pass. Machine result: scratch/pr12184-status-review-guard.json. This checks actual source bytes and the allowed module, rather than a simulated guard.
- Certificate soundness remains explicit: buildRule_sound validates every retained rule; linkedSet_sound checks bounds and automorphisms; nodeVerified_sound derives genuine impossibility; forest_all only links layerk to layerk-1. The zero layer rejects target membership. Arbitrary hash tables or malformed optional rules cannot create an unchecked proof: discarded rules merely remove possible justifications, while retained rules and every selected transition must pass their soundness premises.
- Root acceptance requires both bounded index membership and exact sameWords equality with inputs, followed by complete checkedTables coverage. The final parentFromModes consumes two closed bounds at precisely false/15 and true/14. Independent mathematical review of raw_modes, count handling, graph truth table, and essential inputs is in pr12184-mathematical-review.md.
- Full recursive axiom closure must still be certified by tools/check-lean.mjs after compilation. Static absence of new axioms is not a substitute for that check. The local checker's build subprocess limit is30minutes; runtime optimization must preserve every checked condition.

A publishing branch must still add exactly the one named Lean file, without results artifacts in its PR diff. This review did not mutate the other contributor's branch, PR, or lease.

## ForceBatch adaptation

Source-level review PASS for `PR12184_ForceBatch.lean`, SHA256 `bf0a16701f2324834772b29ee33e0e926f125201a404b84c86eb43d59ee84aa7`, 517562bytes. Actual checkProofFile also passes. Exactly four helpers were added: forcePacked/forcePacked_eq and forceBatch/forceBatch_eq. Exactly three existing declarations changed: rowCut/rowCut_at/rowCut_merge. The new lemmas prove pointwise identities preserving the complete pair-list order and all seven Batch fields. rowCut adds a forcing wrapper before the same existing Boolean checks; the two proof changes only unfold the identity lemma. No certificate data, acceptance predicate, target statement, or trust boundary changed. Actual kernel compilation and runtime comparison are still required.
