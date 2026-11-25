# Independent cached-node preservation review

Verdict: PASS for preservation of `results/orch/lemmas/CachedNodeIntegrationPrefix.lean`.

The current source is 175,597 bytes / 3,486 lines. SHA-256: `b0c1e409cc8516d90bfc7c080fdfdf1a09e0af6f00260fbcb6d1f52a4e6105c0`.

The complete retained `cached-node-integration-prefix.log` contains zero errors and 75 warnings. The author and root report compilation exit zero. The actual current `checkPlain` guard passes. No new build was run in this review.

I independently compared the full cached-node transformation with its width-278 ForceBatch input, rather than relying on the transformation report. Exactly eight declarations are added and four existing declarations change; none are removed. The preserved prefix is an exact prefix of that transformed source. Every byte from the first certificate declaration through the final theorem remains unchanged. Width reduction is an earlier, separate transformation and is not being claimed as an identity here.

- `forceVec_eq` reconstructs a bitvector from its own natural-number value, so it is an exact identity for every width, including zero.
- `forceDecor_eq` applies that identity to the truth signature and both sample vectors, preserving all three components and their order.
- `decodeBankCached_eq` proves equality with the original decoder by induction on depth. It retains both operand indices, the operation bits, the ten-bit shift, the same default record, and the append order.
- `readNodeCached_eq` proves equality with the original packed reader. It retains stored depth, packed width, record position, opcode mask, decoded bank, and live mask. The forcing operations do not introduce an extra acceptance condition or omit a check.
- `contextOf` changes only its reader call. `from_context` rewrites by the reader equality and proves the original Boolean checker identity. `contexts` and `header` only receive the noncomputable declaration modifier required by the forcing functions. Their expressions and predicates are unchanged.

There is no new semantic assumption, certificate oracle, axiom, proof hole, unsafe evaluation, prohibited text, string literal, disallowed attribute, or disallowed option. This is a checked generic prefix; it does not by itself establish the complete gap or complete certificate replay.

Reviewed UTC: 2026-11-25T05:04:55.003345+00:00
Reviewer: /root/status_review.
